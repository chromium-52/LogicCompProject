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

;; list of integers
(defdata loi (listof int))

;; convert the given integer to a list with each element representing its corresponding digit
(definec int-to-list (n :nat) :loi
  (cond 
   ((<= n 9) (list n))
   (t (cons (mod n 10) (int-to-list (floor (/ n 10) 1))))))

(check= (int-to-list 0) (list 0))
(check= (int-to-list 6) (list 6))
(check= (int-to-list 10) (list 0 1))
(check= (int-to-list 256) (list 6 5 2))
(check= (int-to-list 15468) (list 8 6 4 5 1))

;; convert the given loi to an integer
(definec list-to-int (l :loi) :int
  (cond
   ((endp l) 0)
   (t (+ (car l) (* 10 (list-to-int (cdr l)))))))

(check= (list-to-int '()) 0)
(check= (list-to-int '(0)) 0)
(check= (list-to-int '(3)) 3)
(check= (list-to-int '(1 5 6)) 651)
(check= (list-to-int '(8 2 1 4 4)) 44128)

;; zero-based indexOf
(definec index-of (l :loi n :int) :nat
  (cond
   ((endp l) 10000) ; return a "sentinel" value if the given element does not appear
   (t (if (equal (car l) n)
        0
        (1+ (index-of (cdr l) n))))))

(check= (index-of '() 1) 10000)
(check= (index-of '(1 2 3 4 5) 1) 0)
(check= (index-of '(1 2 3 4) 3) 2)
(check= (index-of '(1 2 3 4 5) 5) 4)
(check= (index-of '(1 2 3 4 5 6) 7) 10006)

;; get the element at the given index (int-at, similar to charAt for strings)
(definec int-at (l :loi index :nat) :int
  (cond
   ((endp l) 0) ; return a "sentinel" value if index out of bounds
   ((zerop index) (car l))
   (t (int-at (cdr l) (1- index)))))

(check= (int-at '() 1) 0)
(check= (int-at '(1 2 3 4 5) 0) 1)
(check= (int-at '(1 2 3 4 5) 1) 2)
(check= (int-at '(1 2 3 4 5) 4) 5)
(check= (int-at '(1 2 3 4 5) 6) 0)

;; multiply elements whose indicies that add up to the magnitude equal to that of 10 raised
;; to a power of the given index
(definec multiply (l1 :loi l2 :loi index :nat acc :nat) :int
  :ic (>= index acc)
  (cond
   ((zerop acc) (* (int-at l1 acc) (int-at l2 (- index acc))))
   (t (+ (* (int-at l1 acc) (int-at l2 (- index acc))) (multiply l1 l2 index (1- acc))))))

(check= (multiply (list 7 8) (list 4 3) 0 0) 28) ;; (7 * 4)           ;; (0 * 0)           ;; 2 - 2 = 0
(check= (multiply (list 7 8) (list 4 3) 1 1) 53) ;; (8 * 4) + (7 * 3) ;; (1 * 0) + (0 * 1) ;; 2 - 1 = 1
(check= (multiply (list 7 8) (list 4 3) 2 2) 24) ;; (8 * 3)           ;; (1 * 1)           ;; 2 - 0 = 2
(check= (multiply (list 2 5 4) (list 3 2) 0 0) 6)  ;; (2 * 3)           ;; (0 * 0)           ;; 3 - 3 = 0
(check= (multiply (list 2 5 4) (list 3 2) 1 1) 19) ;; (2 * 2) + (5 * 3) ;; (0 * 1) + (1 * 0) ;; 3 - 2 = 1
(check= (multiply (list 2 5 4) (list 3 2) 2 2) 22) ;; (4 * 3) + (5 * 2) ;; (2 * 0) + (1 * 1) ;; 3 - 1 = 2
(check= (multiply (list 2 5 4) (list 3 2) 3 3) 8)  ;; (4 * 2)           ;; (2 * 1)           ;; 3 - 0 = 3
(check= (multiply (list 3 7) (list 7 4 2) 0 0) 21)
(check= (multiply (list 3 7) (list 7 4 2) 1 1) 61)
(check= (multiply (list 3 7) (list 7 4 2) 2 2) 34)
(check= (multiply (list 3 7) (list 7 4 2) 3 3) 14)
(check= (multiply (list 4 0 0 1) (list 7 0 1) 5 5) 1)

;; run multiply recursively and add the results of multiplying to their correct places
(definec rec-multiply (l1 :loi l2 :loi l1-length :nat) :loi
  (cond
   ((zerop l1-length) (list (multiply l1 l2 l1-length l1-length)))
   (t (cons (multiply l1 l2 l1-length l1-length)
            (rec-multiply l1 l2 (1- l1-length))))))

(check= (rec-multiply (list 7 8) (list 4 3) 2) (list 24 53 28))
(check= (rec-multiply (list 2 5 4) (list 3 2) 3) (list 8 22 19 6))
(check= (rec-multiply (list 3 7) (list 7 4 2) 3) (list 14 34 61 21))

;; process all carries
(definec process-carry (l :loi carry :nat) :loi
  ;; make (+ (car l) carry) into a local variable
  (cond
   ((endp l) (if (equal carry 0)
               nil
               (list carry)))
   (t (if (<= (+ (car l) carry) 9)
        (cons (+ (car l) carry)
              (process-carry (cdr l) 0))
        (cons (mod (+ (car l) carry) 10)
              (process-carry (cdr l) (floor (/ (+ (car l) carry) 10) 1)))))))

(check= (process-carry '() 0) nil)
(check= (process-carry '(1 2 3) 0) '(1 2 3))
(check= (process-carry '(3 6 11) 0) '(3 6 1 1))
(check= (process-carry '(1 3 12 5 11) 0) '(1 3 2 6 1 1))
(check= (process-carry '(21 35 72 53 13) 0) '(1 7 5 0 9 1))
(check= (process-carry '(14 34 61 21) 0) '(4 5 4 7 2))

;; main function
(definec japanese-mult (i1 :nat i2 :nat) :int
  :ic (natp (1- (+ (len (int-to-list i1)) (len (int-to-list i2)))))
  (list-to-int (process-carry (reverse (rec-multiply (int-to-list i1)
                                                     (int-to-list i2)
                                                     (1+ (max (len (int-to-list i1)) (len (int-to-list i2))))))
                              0)))

(check= (japanese-mult 87 34) 2958)
(check= (japanese-mult 254 54) 13716)
(check= (japanese-mult 12 3) 36)
(check= (japanese-mult 73 247) 18031)
(check= (japanese-mult 1004 107) 107428)
(check= (japanese-mult 21114 10) 211140)

(set-gag-mode nil)#|ACL2s-ToDo-Line|#


(defthm japanese-multiplication
  (implies (and (natp x) (natp y))
           (equal (japanese-mult x y) (* x y))))

#|
(defthm japanese-multiplication
  (implies (and (natp x) (natp y))
           (equal (japanese-mult x y) (* x y))))

ACL2 Warning [Non-rec] in ( DEFTHM JAPANESE-MULTIPLICATION ...):  A
:REWRITE rule generated from JAPANESE-MULTIPLICATION will be triggered
only by terms containing the function symbol JAPANESE-MULT, which has
a non-recursive definition.  (Note that JAPANESE-MULT is defined with
JAPANESE-MULT-DEFINITION-RULE.)  Unless this definition is disabled,
this rule is unlikely ever to be used.


<< Starting proof tree logging >>

By the simple :definition NATP we reduce the conjecture to

Goal'
(IMPLIES (AND (INTEGERP X)
              (<= 0 X)
              (INTEGERP Y)
              (<= 0 Y))
         (EQUAL (JAPANESE-MULT X Y) (* X Y))).

This forcibly simplifies, using the :compound-recognizer rules 
ACL2::INTEGER-LISTP-IMPLIES-TLP and ACL2::NATP-COMPOUND-RECOGNIZER,
the :definitions INT-AT-DEFINITION-RULE, JAPANESE-MULT-DEFINITION-RULE
(forced), MAX, MULTIPLY-DEFINITION-RULE, NATP, REC-MULTIPLY-DEFINITION-RULE
and SYNP, the :executable-counterparts of BINARY-+, EQUAL, FORCE and
UNARY--, linear arithmetic, primitive type reasoning, the :rewrite
rules ACL2::|(* y x)|, ACL2::|(+ (+ x y) z)|, ACL2::|(+ (if a b c) x)|,
ACL2::|(+ 0 x)|, ACL2::|(+ c (+ d x))|, ACL2::|(+ x (- x))|, 
ACL2::|(+ x (if a b c))|, ACL2::|(+ y (+ x z))|, ACL2::|(- (+ x y))|,
ACL2::|(- (if a b c))|, ACL2S-REDUCE-ADDITIVE-CONSTANT-<, 
ACL2::BUBBLE-DOWN-+-MATCH-1, CONS-TRUE-LISTP-SIG, ACL2::DEFAULT-TIMES-2,
ACL2::INTEGER-LISTP-IMPLIES-TLP, ACL2::NORMALIZE-ADDENDS, ACL2::REV-OF-CONS
and ACL2::REVERSE-REMOVAL and the :type-prescription rules ALLP, 
INT-TO-LIST-CONTRACT-TP, INTEGER-LISTP, LEN, MULTIPLY-CONTRACT-TP and
REC-MULTIPLY-CONTRACT-TP, to the following six conjectures.

Subgoal 6
(IMPLIES
 (AND (INTEGERP X)
      (<= 0 X)
      (INTEGERP Y)
      (<= 0 Y)
      (< (LEN (INT-TO-LIST Y))
         (LEN (INT-TO-LIST X)))
      (NOT (CONSP (INT-TO-LIST Y))))
 (EQUAL
   (LIST-TO-INT
        (PROCESS-CARRY (APP (REV (REC-MULTIPLY (INT-TO-LIST X)
                                               (INT-TO-LIST Y)
                                               (LEN (INT-TO-LIST X))))
                            (LIST (+ (* 0
                                        (INT-AT (INT-TO-LIST X)
                                                (+ 1 (LEN (INT-TO-LIST X)))))
                                     (MULTIPLY (INT-TO-LIST X)
                                               (INT-TO-LIST Y)
                                               (+ 1 (LEN (INT-TO-LIST X)))
                                               (LEN (INT-TO-LIST X))))))
                       0))
   (* X Y))).

By the simple :rewrite rule ACL2::|(* 0 x)| we reduce the conjecture
to

Subgoal 6'
(IMPLIES
 (AND (INTEGERP X)
      (<= 0 X)
      (INTEGERP Y)
      (<= 0 Y)
      (< (LEN (INT-TO-LIST Y))
         (LEN (INT-TO-LIST X)))
      (NOT (CONSP (INT-TO-LIST Y))))
 (EQUAL
      (LIST-TO-INT
           (PROCESS-CARRY (APP (REV (REC-MULTIPLY (INT-TO-LIST X)
                                                  (INT-TO-LIST Y)
                                                  (LEN (INT-TO-LIST X))))
                               (LIST (+ 0
                                        (MULTIPLY (INT-TO-LIST X)
                                                  (INT-TO-LIST Y)
                                                  (+ 1 (LEN (INT-TO-LIST X)))
                                                  (LEN (INT-TO-LIST X))))))
                          0))
      (* X Y))).

This simplifies, using the :compound-recognizer rules 
ACL2::ACL2-NUMBER-LISTP-IMPLIES-TLP, ACL2::ATOM-LISTP-IMPLIES-TLP,
ACL2::INTEGER-LISTP-IMPLIES-TLP and ACL2::RATIONAL-LISTP-IMPLIES-TLP,
the :executable-counterpart of LEN, the :forward-chaining rules 
ACL2-NUMBER-LIST-IS-SUBTYPE-OF-ATOM-LIST, 
DEFDATA::ACL2-NUMBER-LISTP-FORWARD-TO-TRUE-LISTP, INT-TO-LIST-CONTRACT,
INTEGER-LIST-IS-SUBTYPE-OF-RATIONAL-LIST, 
INTEGER-LISTP-FORWARD-TO-RATIONAL-LISTP, 
RATIONAL-LIST-IS-SUBTYPE-OF-ACL2-NUMBER-LIST, 
ACL2::RATIONAL-LISTP-FORWARD-TO-ACL2-NUMBER-LISTP and 
DEFDATA::RATIONAL-LISTP-FORWARD-TO-ACL2-NUMBER-LISTP, the :rewrite
rules ACL2::|(+ 0 x)|, ACL2::|(< 0 (len x))| and 
ACL2::CONSP-UNDER-IFF-WHEN-TRUE-LISTP and the :type-prescription rule
MULTIPLY-CONTRACT-TP, to

Subgoal 6''
(IMPLIES
 (AND (INTEGERP X)
      (<= 0 X)
      (INTEGERP Y)
      (<= 0 Y)
      (INT-TO-LIST X)
      (NOT (INT-TO-LIST Y)))
 (EQUAL
     (LIST-TO-INT
          (PROCESS-CARRY (APP (REV (REC-MULTIPLY (INT-TO-LIST X)
                                                 NIL (LEN (INT-TO-LIST X))))
                              (LIST (MULTIPLY (INT-TO-LIST X)
                                              NIL (+ 1 (LEN (INT-TO-LIST X)))
                                              (LEN (INT-TO-LIST X)))))
                         0))
     (* X Y))).
^^^ Checkpoint Subgoal 6'' ^^^

Name the formula above *1.

Subgoal 5
(IMPLIES
 (AND (INTEGERP X)
      (<= 0 X)
      (INTEGERP Y)
      (<= 0 Y)
      (<= (LEN (INT-TO-LIST X))
          (LEN (INT-TO-LIST Y)))
      (NOT (CONSP (INT-TO-LIST Y))))
 (EQUAL
   (LIST-TO-INT
        (PROCESS-CARRY (APP (REV (REC-MULTIPLY (INT-TO-LIST X)
                                               (INT-TO-LIST Y)
                                               (LEN (INT-TO-LIST Y))))
                            (LIST (+ (* 0
                                        (INT-AT (INT-TO-LIST X)
                                                (+ 1 (LEN (INT-TO-LIST Y)))))
                                     (MULTIPLY (INT-TO-LIST X)
                                               (INT-TO-LIST Y)
                                               (+ 1 (LEN (INT-TO-LIST Y)))
                                               (LEN (INT-TO-LIST Y))))))
                       0))
   (* X Y))).

By the simple :rewrite rule ACL2::|(* 0 x)| we reduce the conjecture
to

Subgoal 5'
(IMPLIES
 (AND (INTEGERP X)
      (<= 0 X)
      (INTEGERP Y)
      (<= 0 Y)
      (<= (LEN (INT-TO-LIST X))
          (LEN (INT-TO-LIST Y)))
      (NOT (CONSP (INT-TO-LIST Y))))
 (EQUAL
      (LIST-TO-INT
           (PROCESS-CARRY (APP (REV (REC-MULTIPLY (INT-TO-LIST X)
                                                  (INT-TO-LIST Y)
                                                  (LEN (INT-TO-LIST Y))))
                               (LIST (+ 0
                                        (MULTIPLY (INT-TO-LIST X)
                                                  (INT-TO-LIST Y)
                                                  (+ 1 (LEN (INT-TO-LIST Y)))
                                                  (LEN (INT-TO-LIST Y))))))
                          0))
      (* X Y))).

This simplifies, using the :compound-recognizer rules 
ACL2::ACL2-NUMBER-LISTP-IMPLIES-TLP, ACL2::ATOM-LISTP-IMPLIES-TLP,
ACL2::INTEGER-LISTP-IMPLIES-TLP and ACL2::RATIONAL-LISTP-IMPLIES-TLP,
the :executable-counterparts of BINARY-+, BINARY-APPEND, CONS, LEN,
LIST-TO-INT, MULTIPLY, PROCESS-CARRY, REC-MULTIPLY and REV, the :forward-
chaining rules ACL2-NUMBER-LIST-IS-SUBTYPE-OF-ATOM-LIST, 
DEFDATA::ACL2-NUMBER-LISTP-FORWARD-TO-TRUE-LISTP, INT-TO-LIST-CONTRACT,
INTEGER-LIST-IS-SUBTYPE-OF-RATIONAL-LIST, 
INTEGER-LISTP-FORWARD-TO-RATIONAL-LISTP, 
RATIONAL-LIST-IS-SUBTYPE-OF-ACL2-NUMBER-LIST, 
ACL2::RATIONAL-LISTP-FORWARD-TO-ACL2-NUMBER-LISTP and 
DEFDATA::RATIONAL-LISTP-FORWARD-TO-ACL2-NUMBER-LISTP and the :rewrite
rules ACL2::|(< 0 (len x))| and ACL2::CONSP-UNDER-IFF-WHEN-TRUE-LISTP,
to

Subgoal 5''
(IMPLIES (AND (INTEGERP X)
              (<= 0 X)
              (INTEGERP Y)
              (<= 0 Y)
              (NOT (INT-TO-LIST X))
              (NOT (INT-TO-LIST Y)))
         (EQUAL 0 (* X Y))).

This simplifies, using the :definition SYNP and the :rewrite rule 
ACL2::|(equal (* x y) 0)|, to

Subgoal 5'''
(IMPLIES (AND (INTEGERP X)
              (<= 0 X)
              (INTEGERP Y)
              (<= 0 Y)
              (NOT (INT-TO-LIST X))
              (NOT (INT-TO-LIST Y))
              (NOT (EQUAL X 0)))
         (EQUAL Y 0)).
^^^ Checkpoint Subgoal 5''' ^^^

Normally we would attempt to prove Subgoal 5''' by induction.  However,
we prefer in this instance to focus on the original input conjecture
rather than this simplified special case.  We therefore abandon our
previous work on this conjecture and reassign the name *1 to the original
conjecture.  (See :DOC otf-flg.)  [Note:  Thanks again for the hint.]

No induction schemes are suggested by *1.  Consequently, the proof
attempt has failed.

Summary
Form:  ( DEFTHM JAPANESE-MULTIPLICATION ...)
Rules: ((:COMPOUND-RECOGNIZER ACL2::ACL2-NUMBER-LISTP-IMPLIES-TLP)
        (:COMPOUND-RECOGNIZER ACL2::ATOM-LISTP-IMPLIES-TLP)
        (:COMPOUND-RECOGNIZER ACL2::INTEGER-LISTP-IMPLIES-TLP)
        (:COMPOUND-RECOGNIZER ACL2::NATP-COMPOUND-RECOGNIZER)
        (:COMPOUND-RECOGNIZER ACL2::RATIONAL-LISTP-IMPLIES-TLP)
        (:DEFINITION INT-AT-DEFINITION-RULE)
        (:DEFINITION JAPANESE-MULT-DEFINITION-RULE)
        (:DEFINITION MAX)
        (:DEFINITION MULTIPLY-DEFINITION-RULE)
        (:DEFINITION NATP)
        (:DEFINITION NOT)
        (:DEFINITION REC-MULTIPLY-DEFINITION-RULE)
        (:DEFINITION SYNP)
        (:EXECUTABLE-COUNTERPART BINARY-+)
        (:EXECUTABLE-COUNTERPART BINARY-APPEND)
        (:EXECUTABLE-COUNTERPART CONS)
        (:EXECUTABLE-COUNTERPART EQUAL)
        (:EXECUTABLE-COUNTERPART FORCE)
        (:EXECUTABLE-COUNTERPART LEN)
        (:EXECUTABLE-COUNTERPART LIST-TO-INT)
        (:EXECUTABLE-COUNTERPART MULTIPLY)
        (:EXECUTABLE-COUNTERPART PROCESS-CARRY)
        (:EXECUTABLE-COUNTERPART REC-MULTIPLY)
        (:EXECUTABLE-COUNTERPART REV)
        (:EXECUTABLE-COUNTERPART UNARY--)
        (:FAKE-RUNE-FOR-LINEAR NIL)
        (:FAKE-RUNE-FOR-TYPE-SET NIL)
        (:FORWARD-CHAINING ACL2-NUMBER-LIST-IS-SUBTYPE-OF-ATOM-LIST)
        (:FORWARD-CHAINING DEFDATA::ACL2-NUMBER-LISTP-FORWARD-TO-TRUE-LISTP)
        (:FORWARD-CHAINING INT-TO-LIST-CONTRACT)
        (:FORWARD-CHAINING INTEGER-LIST-IS-SUBTYPE-OF-RATIONAL-LIST)
        (:FORWARD-CHAINING INTEGER-LISTP-FORWARD-TO-RATIONAL-LISTP)
        (:FORWARD-CHAINING RATIONAL-LIST-IS-SUBTYPE-OF-ACL2-NUMBER-LIST)
        (:FORWARD-CHAINING ACL2::RATIONAL-LISTP-FORWARD-TO-ACL2-NUMBER-LISTP)
        (:FORWARD-CHAINING
             DEFDATA::RATIONAL-LISTP-FORWARD-TO-ACL2-NUMBER-LISTP)
        (:REWRITE ACL2::|(* 0 x)|)
        (:REWRITE ACL2::|(* y x)|)
        (:REWRITE ACL2::|(+ (+ x y) z)|)
        (:REWRITE ACL2::|(+ (if a b c) x)|)
        (:REWRITE ACL2::|(+ 0 x)|)
        (:REWRITE ACL2::|(+ c (+ d x))|)
        (:REWRITE ACL2::|(+ x (- x))|)
        (:REWRITE ACL2::|(+ x (if a b c))|)
        (:REWRITE ACL2::|(+ y (+ x z))|)
        (:REWRITE ACL2::|(- (+ x y))|)
        (:REWRITE ACL2::|(- (if a b c))|)
        (:REWRITE ACL2::|(< 0 (len x))|)
        (:REWRITE ACL2::|(equal (* x y) 0)|)
        (:REWRITE ACL2S-REDUCE-ADDITIVE-CONSTANT-<)
        (:REWRITE ACL2::BUBBLE-DOWN-+-MATCH-1)
        (:REWRITE CONS-TRUE-LISTP-SIG)
        (:REWRITE ACL2::CONSP-UNDER-IFF-WHEN-TRUE-LISTP)
        (:REWRITE ACL2::DEFAULT-TIMES-2)
        (:REWRITE ACL2::INTEGER-LISTP-IMPLIES-TLP)
        (:REWRITE ACL2::NORMALIZE-ADDENDS)
        (:REWRITE ACL2::REV-OF-CONS)
        (:REWRITE ACL2::REVERSE-REMOVAL)
        (:TYPE-PRESCRIPTION ALLP)
        (:TYPE-PRESCRIPTION INT-TO-LIST-CONTRACT-TP)
        (:TYPE-PRESCRIPTION INTEGER-LISTP)
        (:TYPE-PRESCRIPTION LEN)
        (:TYPE-PRESCRIPTION MULTIPLY-CONTRACT-TP)
        (:TYPE-PRESCRIPTION REC-MULTIPLY-CONTRACT-TP))
Warnings:  Non-rec
Time:  3.74 seconds (prove: 3.16, print: 0.01, proof tree: 0.00, other: 0.57)
Prover steps counted:  55343

---
The key checkpoint goals, below, may help you to debug this failure.
See :DOC failure and see :DOC set-checkpoint-summary-limit.
---

*** Key checkpoints before reverting to proof by induction: ***

Subgoal 6''
(IMPLIES
 (AND (INTEGERP X)
      (<= 0 X)
      (INTEGERP Y)
      (<= 0 Y)
      (INT-TO-LIST X)
      (NOT (INT-TO-LIST Y)))
 (EQUAL
     (LIST-TO-INT
          (PROCESS-CARRY (APP (REV (REC-MULTIPLY (INT-TO-LIST X)
                                                 NIL (LEN (INT-TO-LIST X))))
                              (LIST (MULTIPLY (INT-TO-LIST X)
                                              NIL (+ 1 (LEN (INT-TO-LIST X)))
                                              (LEN (INT-TO-LIST X)))))
                         0))
     (* X Y)))

Subgoal 5'''
(IMPLIES (AND (INTEGERP X)
              (<= 0 X)
              (INTEGERP Y)
              (<= 0 Y)
              (NOT (INT-TO-LIST X))
              (NOT (INT-TO-LIST Y))
              (NOT (EQUAL X 0)))
         (EQUAL Y 0))

ACL2 Error in ( DEFTHM JAPANESE-MULTIPLICATION ...):  See :DOC failure.

******** FAILED ********

**Summary of Cgen/testing**
We tested 1500 examples across 3 subgoals, of which 500 (500 unique)
satisfied the hypotheses, and found 0 counterexamples and 500 witnesses.

Cases in which the conjecture is true include:
 [found in : "Goal"]
 -- ((Y 1) (X 992))
 -- ((Y 58) (X 6))
 -- ((Y 13) (X 424))
|#