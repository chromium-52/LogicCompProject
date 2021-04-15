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

;; list of naturals
(defdata lon (listof nat))

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

;; convert the given nat to a list with each element representing its corresponding digit
;(definec nat-to-list (n :nat) :lon
;  (cond 
;   ((<= n 9) (list n))
;   (t (cons (mod n 10) (nat-to-list (floor (/ n 10) 1))))))

;(check= (nat-to-list 0) (list 0))
;(check= (nat-to-list 6) (list 6))
;(check= (nat-to-list 10) (list 0 1))
;(check= (nat-to-list 256) (list 6 5 2))
;(check= (nat-to-list 15468) (list 8 6 4 5 1))

;; convert the given lon to a natural
(definec list-to-nat (l :lon) :nat
  (cond
   ((endp l) 0)
   (t (+ (car l) (* 10 (list-to-nat (cdr l)))))))

(check= (list-to-nat '()) 0)
(check= (list-to-nat '(0)) 0)
(check= (list-to-nat '(3)) 3)
(check= (list-to-nat '(1 5 6)) 651)
(check= (list-to-nat '(8 2 1 4 4)) 44128)

;; zero-based indexOf
(definec index-of (l :lon n :nat) :nat
  :ic (in2 n l)
  (if (equal (car l) n)
    0
    (1+ (index-of (cdr l) n))))

(check= (index-of '(1 2 3 4 5) 1) 0)
(check= (index-of '(1 2 3 4) 3) 2)
(check= (index-of '(1 2 3 4 5) 5) 4)

;; get the element at the given index (similar to charAt for strings in Java)
(definec nat-at (l :lon index :nat) :nat
  (cond
   ((endp l) 0)
   ((zerop index) (car l))
   (t (nat-at (cdr l) (1- index)))))

(check= (nat-at '() 1) 0)
(check= (nat-at '(1 2 3 4 5) 0) 1)
(check= (nat-at '(1 2 3 4 5) 1) 2)
(check= (nat-at '(1 2 3 4 5) 4) 5)
(check= (nat-at '(1 2 3 4 5) 6) 0)

;; multiply elements whose indicies that add up to the magnitude equal to that of 10 raised
;; to a power of the given index
(definec multiply (l1 :lon l2 :lon index :nat acc :nat) :nat
  :ic (>= index acc)
  (cond
   ((zerop acc) (* (nat-at l1 acc) (nat-at l2 (- index acc))))
   (t (+ (* (nat-at l1 acc) (nat-at l2 (- index acc))) (multiply l1 l2 index (1- acc))))))

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
(definec rec-multiply (l1 :lon l2 :lon length :nat) :lon
  (cond
   ((zerop length) (list (multiply l1 l2 length length)))
   (t (cons (multiply l1 l2 length length)
            (rec-multiply l1 l2 (1- length))))))

(check= (rec-multiply (list 7 8) (list 4 3) 2) (list 24 53 28))
(check= (rec-multiply (list 2 5 4) (list 3 2) 3) (list 8 22 19 6))
(check= (rec-multiply (list 3 7) (list 7 4 2) 3) (list 14 34 61 21))

;; process all carries
(definec process-carry (l :lon carry :nat) :lon
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
<<<<<<< HEAD
(definec japanese-mult (l1 :lon l2 :lon) :nat
  (list-to-nat (process-carry (rev2 (rec-multiply l1 l2 (1+ (max (len l1) (len l2)))))
                              0)))

(check= (japanese-mult (list 7 8) (list 4 3)) 2958) ; 87 * 34 = 2958
(check= (japanese-mult (list 4 5 2) (list 4 5)) 13716) ; 254 * 54 = 13716
(check= (japanese-mult (list 2 1) (list 3)) 36) ; 12 * 3 = 36
(check= (japanese-mult (list 3 7) (list 7 4 2)) 18031) ; 73 * 247 = 18031
(check= (japanese-mult (list 4 0 0 1) (list 7 0 1)) 107428) ; 1004 * 107 = 107428
(check= (japanese-mult (list 4 1 1 1 2) (list 0 1)) 211140) ; 21114 * 10 = 211140

(set-gag-mode nil)

;(defthm nat-to-list-never-empty
;  (implies (and (natp x) (natp y))
;           (and (nat-to-list x) (nat-to-list y))))

;(defthm list-of-nats
;  (implies (and (natp x) (natp y))
;           (and (acl2-numberp (car (nat-to-list x))) (acl2-numberp (car (nat-to-list y))))))

(defthm japanese-multiplication
<<<<<<< HEAD
  (implies (and (lonp l1) (lonp l2))
           (equal (japanese-mult l1 l2) (* (list-to-nat l1) (list-to-nat l2)))))
;  :hints (("Goal" :induct (tlp x))))

(defthm placeholder
  (implies (and (natp x) (natp y))
           (equal (rec-multiply (nat-to-list x)
                                (nat-to-list y)
                                (1+ (max (len (nat-to-list x)) (len (nat-to-list y)))))
                  (nat-to-list (* x y)))))
