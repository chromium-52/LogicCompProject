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
;; Proving Japanese multiplication using ACL2s theorem prover

; Encode the two integers into a format that ACL2s can understand
;; using decimal expansion to output a pair of lists (each element in the list represents a particular digit)
; Multiply each digit by each digit in the other list
;; the number of multiplications is equal to (number of digits of first integer) * (number of digits of second integer)
;; if the sum of the products of any digit is greater than or equal to 10, carry its tens digit
; Put all the digits together

; 42 * 21
; l1...(4, 2)
; l2...(2, 1)
; 
; 2 * 1 = 2 => 2
;
; 4 * 1 = 4
; 2 * 2 = 4 => 4 + 4 = 8
;
; 4 * 2 = 8 => 8
;
; => 882

; 14 * 23
; l1...(1, 4)
; l2...(2, 3)
;
; 4 * 3 = 12 => 2 (with carry of 1)
;
; 1 * 3 = 3
; 4 * 2 = 8 => 1 + 3 + 8 = 2 (with carry of 1)
;
; 1 * 2 = 2 => 1 + 2 = 3
;
; => 322

; 321 * 13
; l1...(3, 2, 1)
; l2......(1, 3)
;
; 1 * 3 = 3
;
; 2 * 3 = 6
; 1 * 1 = 1 => 6 + 1 = 7
;
; 3 * 3 = 9
; 2 * 1 = 2 => 9 + 2 = 1 (with carry of 1)
;
; 3 * 1 = 3 => 1 + 3 = 4
;
; => 4173

#|
87 * 34 = 2958
i1 = 87
i2 = 34
l1 = (int-to-list 87) = (list 7 8)
l2 = (int-to-list 34) = (list 4 3)
(rec-multiply l1 l2) = calls multiply recursively 
         (multiply l1 l2 0) = 28 (0,0)
         (multiply l1 l2 1) = 32 + 21 = 53 1 (1,0) + (0,1)
         (multiply l1 l2 2) = 24 (1,1) bc no index equalling to 2
         = (list 28 53 24)
(process-carry (list 28 53 24)) = (list 8 5 9 2)
(list-to-int (list 8 5 9 2) = 2958
|#

(defdata lessthanten (oneof 0 1 2 3 4 5 6 7 8 9))

;; list of naturals
(defdata lon (listof lessthanten))

;; previously used functions
(definec app2 (x :lon y :lon) :lon
  (if (endp x)
      y
    (cons (first x) (app2 (rest x) y))))

(definec rev2 (x :lon) :lon
   (if (endp x)
       x
     (app2 (rev2 (cdr x)) (list (car x)))))

(definec in2 (n :nat l :lon) :bool
  (and (consp l)
       (or (== n (first l))
           (in2 n (rest l)))))

;; convert the given lon to a natural
(definec list-to-nat (l :lon) :nat
  (cond
   ((endp l) 0)
   (t (+ (* (expt 10 (1- (len l))) (car l)) (list-to-nat (cdr l))))))

(check= (list-to-nat '()) 0)
(check= (list-to-nat '(0)) 0)
(check= (list-to-nat '(3)) 3)
(check= (list-to-nat '(6 5 1)) 651)
(check= (list-to-nat '(4 4 1 2 8)) 44128)

(definec multiply2-helper (val :nat l2 :lon length :nat) :nat
  (cond
   ((endp l2) 0)
   (t (+ (* val (car l2) (expt 10 (+ length (1- (len l2)))))
         (multiply2-helper val (cdr l2) length)))))

(check= (multiply2-helper 1 (list 2 1 1) 2) 21100)
(check= (multiply2-helper 2 (list 2 1 1) 1) 4220)
(check= (multiply2-helper 3 (list 2 1 1) 0) 633)

;(multiply2 '(1 2 3) '(2 1 1))
(definec multiply2 (l1 :lon l2 :lon) :nat
  (cond
   ((endp l1) 0)
   (t (+ (multiply2-helper (car l1) l2 (1- (len l1)))
         (multiply2 (cdr l1) l2)))))

(check= (multiply2 (list 1 2 3) (list 2 1 1)) 25953)
(check= (multiply2 (list 1 2) (list 2 1 1)) 2532)

(set-gag-mode nil)

(defthm multby0l1
  (implies (and (equal (list 0) l1) (lonp l2))
           (equal (multiply2 l1 l2) 0)))

(defthm multby0l2
  (implies (and (equal (list 0) l2) (lonp l1))
           (equal (multiply2 l1 l2) 0)))

(defthm cdr-empty
  (implies (endp l)
           (equal (len (cdr l)) 0)))#|ACL2s-ToDo-Line|#


(defthm multiply2-defthm
  (implies (and (lonp l1) (lonp l2))
           (equal (multiply2 l1 l2) (* (list-to-nat l1) 
                                       (list-to-nat l2)))))
