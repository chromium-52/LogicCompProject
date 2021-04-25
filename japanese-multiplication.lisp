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

#|
Examples:

Ex 1) 14 * 23 = 322
l1...'(1, 4)
l2...'(2, 3)

1 * 2 * 10^2 + 1 * 3 * 10^1 = 230
4 * 2 * 10^1 + 4 * 3 * 10^0 = 92

230 + 92 = 322
=> 322

Ex 2) 321 * 13 = 4173
l1...'(3, 2, 1)
l2......'(1, 3)

3 * 1 * 10^3 + 3 * 3 * 10^2 = 3900
2 * 1 * 10^2 + 2 * 3 * 10^1 = 260
1 * 1 * 10^1 + 1 * 3 * 10^0 = 13

3900 + 260 + 13 = 4173
=> 4173

Overall program flow:

Ex) 87 * 34 = 2958
l1 = (list 8 7)
l2 = (list 3 4)
(japanese-mult l1 l2) = calls mult-helper recursively
           (mult-helper 8 (list 3 4) 1) = 2720 (8 * 3 * 10^2 + 8 * 4 * 10^1)
         + (mult-helper 7 (list 3 4) 0) = 238 (7 * 3 * 10^1 + 7 * 4 * 10^0)
         = 2958
|#

;; one-digit natural number
(defdata less-than-ten (oneof 0 1 2 3 4 5 6 7 8 9))
;; list of naturals
(defdata loltn (listof less-than-ten))

;; convert the given lon to a natural
(definec list-to-nat (l :loltn) :nat
  (cond
   ((endp l) 0)
   (t (+ (* (car l) (expt 10 (1- (len l))))
         (list-to-nat (cdr l))))))

(check= (list-to-nat '()) 0)
(check= (list-to-nat '(0)) 0)
(check= (list-to-nat '(3)) 3)
(check= (list-to-nat '(6 5 1)) 651)
(check= (list-to-nat '(4 4 1 2 8)) 44128)

;; add the products of the corresponding digits along a single diagonal
;; (refer to the step-by-step diagram of Japanese multiplication attached
;;  to the accompanying paper to visualize this function)
(definec mult-helper (val :nat l2 :loltn length :nat) :nat
  (cond
   ((endp l2) 0)
   (t (+ (* val (car l2) (expt 10 (+ length (1- (len l2)))))
         (mult-helper val (cdr l2) length)))))

(check= (mult-helper 1 (list 2 1 1) 2) 21100)
(check= (mult-helper 2 (list 2 1 1) 1) 4220)
(check= (mult-helper 3 (list 2 1 1) 0) 633)

;; add the values of all individual diagonals
(definec japanese-mult (l1 :loltn l2 :loltn) :nat
  (cond
   ((endp l1) 0)
   (t (+ (mult-helper (car l1) l2 (1- (len l1)))
         (japanese-mult (cdr l1) l2)))))

(check= (japanese-mult (list 1 2 3) (list 2 1 1)) 25953)
(check= (japanese-mult (list 1 2) (list 2 1 1)) 2532)
(check= (japanese-mult (list 0) (list 1 2 3)) 0)
(check= (japanese-mult (list 7 2 4) (list 6 5 2 1)) 4721204)

;; making sure the theorem we're trying to prove is not incorrect
(test? (implies (and (lonp l1) (lonp l2))
                (equal (japanese-mult l1 l2)
                       (* (list-to-nat l1) (list-to-nat l2)))))

(set-gag-mode nil)

;; relates mult-helper to list-to-nat with arbitrary natural numbers,
;;primary purpose is to simplify mult-help-to-list-to-nat's claim
(defthm mult-help-to-list-to-nat-helper
  (implies (and (natp x) (loltnp l2) (natp y))
           (equal (mult-helper x l2 y)
                  (* x (list-to-nat l2) (expt 10 y)))))

;; relates mult-helper to list-to-nat with two lists of natural numbers
(defthm mult-help-to-list-to-nat
  (implies (and (loltnp l1)
                (consp l1)
                (loltnp l2)
                l2)
           (equal (mult-helper (car l1) l2 (len (cdr l1)))
                  (* (car l1) (expt 10 (1- (len l1)))
                     (list-to-nat l2)))))

;; overall defthm
;; proves that our japanese-mult function is equivalent to multiplying
;; two lists of natural numbers 
(defthm japanese-multiplication
  (implies (and (loltnp l1) (loltnp l2))
           (equal (japanese-mult l1 l2)
                  (* (list-to-nat l1) 
                     (list-to-nat l2)))))

#|
Intermediary lemmas that later turned out to be unnecessary to prove the theorem

(defthm endp-l2
  (implies (and (loltnp l1) (loltnp l2) (endp l2))
           (equal (japanese-mult l1 l2)
                  0)))

(defthm mult-help-0
  (implies (AND (loltnp L2) (natp x))
         (EQUAL (MULT-HELPER 0 L2 x)
                0)))
                
(defthm testing2
  (IMPLIES (AND (loltnp l1)
                (CONSP L1)
                (EQUAL (JAPANESE-MULT (CDR L1) L2)
                       (* (LIST-TO-NAT L2)
                          (LIST-TO-NAT (CDR L1))))
                (loltnp L2)
                L2)
           (EQUAL (+ (JAPANESE-MULT (CDR L1) L2)
                     (MULT-HELPER (car l1) L2 (LEN (CDR L1))))
                  (+ (* (* (car l1) (expt 10 (1- (len l1))))
                        (LIST-TO-NAT L2))
                     (* (LIST-TO-NAT (cdr L1)) 
                        (LIST-TO-NAT L2))))))

(defthm consp-l2
  (implies (and (loltnp l1) (loltnp l2) (consp l2))
           (equal (japanese-mult l1 l2)
                  (* (list-to-nat l1) 
                     (list-to-nat l2)))))
|#
