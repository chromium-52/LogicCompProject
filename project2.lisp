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

;; one-digit natural number
(defdata less-than-ten (oneof 0 1 2 3 4 5 6 7 8 9))
;; list of naturals
(defdata lon (listof less-than-ten))

;; append two lists
(definec app2 (x :lon y :lon) :lon
  (if (endp x)
      y
    (cons (first x) (app2 (rest x) y))))

;; reverse the given list
(definec rev2 (x :lon) :lon
   (if (endp x)
       x
     (app2 (rev2 (cdr x)) (list (car x)))))

;; convert the given lon to a natural
(definec list-to-nat (l :lon) :nat
  (cond
   ((endp l) 0)
   (t (+ (* (car l) (expt 10 (1- (len l))))
         (list-to-nat (cdr l))))))

;(definec list-to-nat (l :lon) :nat
;  (cond
;   ((endp l) 0)
;   (t (+ (car l) (* 10 (list-to-nat (cdr l)))))))

(check= (list-to-nat '()) 0)
(check= (list-to-nat '(0)) 0)
(check= (list-to-nat '(3)) 3)
(check= (list-to-nat '(6 5 1)) 651)
(check= (list-to-nat '(4 4 1 2 8)) 44128)

;; add the products of the corresponding digits along a single diagonal
;; (refer to a diagram of Japanese multiplication for additional information)
(definec mult-helper (val :nat l2 :lon length :nat) :nat
  (cond
   ((endp l2) 0)
   (t (+ (* val (car l2) (expt 10 (+ length (1- (len l2)))))
         (mult-helper val (cdr l2) length)))))

(check= (mult-helper 1 (list 2 1 1) 2) 21100)
(check= (mult-helper 2 (list 2 1 1) 1) 4220)
(check= (mult-helper 3 (list 2 1 1) 0) 633)

;; add the values of all individual diagonals
(definec japanese-mult (l1 :lon l2 :lon) :nat
  (cond
   ((endp l1) 0)
   (t (+ (mult-helper (car l1) l2 (1- (len l1)))
         (japanese-mult (cdr l1) l2)))))

(check= (japanese-mult (list 1 2 3) (list 2 1 1)) 25953)
(check= (japanese-mult (list 1 2) (list 2 1 1)) 2532)
(check= (japanese-mult (list 0) (list 1 2 3)) 0)
(check= (japanese-mult (list 7 2 4) (list 6 5 2 1)) 4721204)

(test? (implies (and (lonp l1) (lonp l2))
                (equal (japanese-mult l1 l2) (* (list-to-nat l1) 
                                                (list-to-nat l2)))))

(set-gag-mode nil)

;(defthm l1-is-zero
;  (implies (and (equal (list 0) l1) (lonp l2))
;           (equal (japanese-mult l1 l2) 0)))

;(defthm l2-is-zero
;  (implies (and (equal (list 0) l2) (lonp l1))
;           (equal (japanese-mult l1 l2) 0)))


;;previous implementation of list-to-nat
(definec list-to-nat-rev (l :lon) :nat
  (cond
   ((endp l) 0)
   (t (+ (car l) (* 10 (list-to-nat-rev (cdr l)))))))

;;tried to prove list-to-nat so that ACL2s would see that it is true, leave it alone and only focus on japanese mult
(defthm list-to-nat-defthm
  (implies (and (lonp l1) (lonp l2) (natp x) (natp y)
                (equal (list-to-nat l1) x)
                (equal (list-to-nat l2) y))
           (equal (* (list-to-nat l1) (list-to-nat l2))
                  (* x y))))#|ACL2s-ToDo-Line|#

;;tried to get rid of list-to-nat
(defthm expand-japanese-mult
  (implies (and (lonp l1) (lonp l2))
           (equal (japanese-mult l1 l2)
                  (* (mult-helper 1 l1 0) (mult-helper 1 l2 0)))))

;;one of the subgoals that ACL2 failed at
(skip-proofs
 (defthm test
   (IMPLIES (AND (EQUAL (CAR L1) 0)
              (LONP (CDR L1))
              (CONSP L1)
              (EQUAL (japanese-mult (CDR L1) L2)
                     (* (LIST-TO-NAT L2)
                        (LIST-TO-NAT (CDR L1))))
              (LONP L2))
         (EQUAL (mult-helper 0 L2 (LEN (CDR L1)))
                0))))

(test? (implies (and (lonp l1) (lonp l2))
                (equal (japanese-mult l1 l2) (* (list-to-nat l1) 
                                                (list-to-nat l2)))))
;;same thing as above, just a different one
(defthm groupme
  (IMPLIES (AND (NOT (ENDP L1))
                (EQUAL (japanese-mult (CDR L1) L2)
                       (* (LIST-TO-NAT (CDR L1))
                          (LIST-TO-NAT L2)))
                (LONP L1)
                (LONP L2))
           (EQUAL (japanese-mult L1 L2)
                  (* (LIST-TO-NAT L1) (LIST-TO-NAT L2))))
  :hints (("Goal" :hands-off list-to-nat)))

;;same as above, expands list-to-nat which we want to avoid because we don't think proving list-to-nat is
;;useful when trying to prove japanese-mult, i.e., list-to-nat has nothing to do with the main proof.
(defthm placeholder
  (implies (and (less-than-tenp n)
                (equal (car l1) n)
                (lonp (cdr l1))
                (consp l1)
                (equal (japanese-mult (cdr l1) l2)
                       (* (list-to-nat l2)
                          (list-to-nat (cdr l1))))
                (lonp l2))
           (equal (mult-helper n l2 (len (cdr l1)))
                  (* n (list-to-nat l2)
                     (expt 10 (len (cdr l1))))))
  :hints (("Subgoal *1/" :hands-off (list-to-nat l1))))

;;main theorem of japanese-mult
(defthm japanese-multiplication
  (implies (and (lonp l1) (lonp l2))
           (equal (japanese-mult l1 l2)
                  (* (list-to-nat l1) 
                     (list-to-nat l2)))))

;(defthm japanese-multiplication-rev2
;  (implies (and (lonp l1) (lonp l2))
;           (equal (japanese-mult l1 l2) (* (list-to-nat (rev2 l1))
;                                        (list-to-nat (rev2 l2))))))
