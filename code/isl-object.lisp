(in-package :cl-isl)

(defgeneric copy (isl-object))

(defstruct (isl-object (:copier nil))
  (handle (alexandria:required-argument :handle)
   :type cffi:foreign-pointer))

(defmethod print-object ((isl-object isl-object) stream)
  (print-unreadable-object (isl-object stream :type t)
    (format stream "{~X}" (cffi:pointer-address (isl-object-handle isl-object)))))

(defmacro isl-object-%copy (object-name)
  "Returns the name of the function for creating a fresh copy of the
handle of the ISL object denoted by OBJECT-NAME."
  `(getf (symbol-plist ,object-name) '%copy))

(defmacro isl-object-%make (object-name)
  "Returns the name of the function for turning a suitable handle into an
ISL object of type OBJECT-NAME."
  `(getf (symbol-plist ,object-name) '%make))

(defmacro isl-object-%free (object-name)
  "Returns the name of the function for freeing a handle of an ISL object
of type OBJECT-NAME."
  `(getf (symbol-plist ,object-name) '%free))

(defun isl-object-name-p (x)
  (and (symbolp x)
       (not (null (isl-object-%make x)))))

;;; This hash table is used in each ISL object constructor to ensure that
;;; each handle has exactly one corresponding wrapper object.
(defvar *isl-object-table* (trivial-garbage:make-weak-hash-table :weakness :value))

;;; Finalizers may run in a thread of their own, and isl must not be called
;;; from two threads at once.  So a finalizer only records which handle to
;;; free, and the handles are freed by whichever thread next creates an ISL
;;; object.
(defvar *pending-frees* '())

(defvar *pending-frees-lock* (bordeaux-threads:make-lock "isl pending frees"))

(defun schedule-free (free handle)
  (bordeaux-threads:with-lock-held (*pending-frees-lock*)
    (push (cons free handle) *pending-frees*)))

(defun free-pending-handles ()
  (let ((pending
          (bordeaux-threads:with-lock-held (*pending-frees-lock*)
            (shiftf *pending-frees* '()))))
    (loop for (free . handle) in pending do
      (funcall free handle))))

(defmacro define-isl-object
    (name &key (abstract nil)
            (list-type nil)
            (superclass 'isl-object)
            (from-str nil)
            ((:free %free) (isl-object-%free superclass))
            ((:copy %copy) (isl-object-%copy superclass)))
  (let ((predicate (make-isl-sym name (if (find #\- (string name)) "-P" "P")))
        (%make (make-isl-sym "%MAKE-" name))
        (%%make (make-isl-sym "%%MAKE-" name))
        (%from-str-us (make-isl-sym name "-FROM-STR"))
        (%from-str-library (make-isl-sym "%ISL-" name "-READ-FROM-STR"))
        )
    (setf (isl-object-%copy name) %copy)
    (setf (isl-object-%make name) %make)
    (setf (isl-object-%free name) %free)
    `(progn
       ;; Also record the functions of this object when the compiled file
       ;; is loaded, so that later files can be compiled on their own.
       (eval-when (:compile-toplevel :load-toplevel :execute)
         (setf (isl-object-%copy ',name) ',%copy)
         (setf (isl-object-%make ',name) ',%make)
         (setf (isl-object-%free ',name) ',%free))
       (defstruct (,name (:include ,superclass)
                         (:predicate ,predicate)
                         (:copier nil)
                         (:constructor ,%%make (handle))))
       (declaim (ftype (function (cffi:foreign-pointer) (values ,name &optional)) ,%make))
       ,@(when list-type
           `((define-isl-object-list ,list-type ,name)))
       ,@(when from-str
           `((define-isl-function ,%from-str-us ,%from-str-library
               (:give ,name)
               (:parm context *context*)
               (:keep string))))
       ,@(unless abstract
           `((defun ,%make (handle)
               (when (cffi:null-pointer-p handle) (isl-error))
               (free-pending-handles)
               (let ((existing (gethash (cffi:pointer-address handle) *isl-object-table*)))
                 (cond (existing
                        ;; The handle is another reference to an object
                        ;; that already has a wrapper, which owns one
                        ;; reference only.
                        (,%free handle)
                        existing)
                       (t
                        (setf (gethash (cffi:pointer-address handle) *isl-object-table*)
                              (trivial-garbage:finalize
                               (,%%make handle)
                               (lambda () (schedule-free ',%free handle))))))))))
       ,@(when %copy
           `((defmethod copy ((,name ,name))
               (,%make (,%copy (isl-object-handle ,name)))))))))

(defmacro define-isl-object-list (name element-type)
  (let* ((%name
           (case name
             (identifier-list "ID-LIST")
             (value-list "VAL-LIST")
             (affine-list "AFF-LIST")
             (otherwise name)))
         (%element-type
           (case element-type
             (identifier "ID")
             (value "VAL")
             (affine "AFF")
             (otherwise element-type)))
         (%free (make-isl-sym "%ISL-" %name "-FREE"))
         (%copy (make-isl-sym "%ISL-" %name "-COPY"))
         (%size (make-isl-sym "%ISL-" %name "-SIZE"))
         (%get-elt (make-isl-sym "%ISL-" %name "-GET-" %element-type))
         (%set-elt (make-isl-sym "%ISL-" %name "-SET-" %element-type))
         (%to-str (make-isl-sym "%ISL-" %name "-TO-STR"))
         (size (make-isl-sym name "-SIZE"))
         (get-elt (make-isl-sym name "-ELT"))
         (set-elt (make-isl-sym "SET-" name "-ELT"))
         (elements (make-isl-sym name "-ELEMENTS")))
    `(progn
       (define-isl-object ,name
         :free ,%free
         :copy ,%copy
         :from-str nil)
       (defmethod print-object ((,name ,name) stream)
         (print-unreadable-object (,name stream :type t)
           (write-string (,%to-str (isl-object-handle ,name)) stream)))
       (define-isl-function ,size ,%size
         (:give size)
         (:keep ,name))
       (define-isl-function ,get-elt ,%get-elt
         (:give ,element-type)
         (:keep ,name)
         (:keep unsigned-byte))
       (define-isl-function ,set-elt ,%set-elt
         (:give ,name)
         (:take ,name)
         (:keep unsigned-byte)
         (:take ,element-type))
       (defun ,elements (,name)
         (declare (type ,name ,name))
         (loop for index below (,size ,name)
               collect
               (,get-elt ,name index))))))
