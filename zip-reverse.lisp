; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;(1, 2, 3) (4, 5, 6)
;((1, 4), (2, 5), (3, 6))...a

;(3, 2, 1) (6, 5, 4)
;((3, 6), (2, 5), (1, 4))...b

(defdata lon (listof nat))

(defdata pair (cons nat nat))
(defdata lop (listof pair))

(definec app2 (x :tl y :tl) :tl
  (if (endp x)
      y
    (cons (first x) (app2 (rest x) y))))

(definec rev2 (x :tl) :tl
   (if (endp x)
       x
     (app2 (rev2 (cdr x)) (list (car x)))))

(definec zip2 (l1 :lon l2 :lon) :lop
  :ic (equal (len l1) (len l2))
  (cond
   ((endp l1) nil)
   (t (cons (cons (car l1) (car l2)) (zip2 (cdr l1) (cdr l2))))))#|ACL2s-ToDo-Line|#


;(definec zip3 (l1 :lon l2 :lon) :tl
;  :ic (equal (len l1) (len l2))
;  (cond
;   ((endp l1) nil)
;   (t (app2 (cons (car l1) (car l2)) (zip3 (cdr l1) (cdr l2))))))

(set-gag-mode nil)

(defthm zip2-rev2
  (implies (and (lonp tl1) (lonp tl2) (equal (len tl1) (len tl2)) (consp tl1))
           (equal (rev2 (zip2 tl1 tl2))
                  (zip2 (rev2 tl1) (rev2 tl2)))))

(defthm zip2-rev2
  (implies (and (lonp tl1) (lonp tl2) (equal (len tl1) (len tl2)))
           (equal (rev2 (zip2 tl1 tl2))
                  (zip2 (rev2 tl1) (rev2 tl2)))))
