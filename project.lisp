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
   ((or (zerop acc) (< (len l2) (1- acc))) (* (int-at l1 acc) (int-at l2 (- index acc))))
   (t (+ (* (int-at l1 acc) (int-at l2 (- index acc))) (multiply l1 l2 index (1- acc))))))

(check= (multiply (list 7 8) (list 4 3) 0 0) 28) ;; (7 * 4)           ;; (0 * 0)           ;; 2 - 2 = 0
(check= (multiply (list 7 8) (list 4 3) 1 1) 53) ;; (8 * 4) + (7 * 3) ;; (1 * 0) + (0 * 1) ;; 2 - 1 = 1
(check= (multiply (list 7 8) (list 4 3) 2 2) 24) ;; (8 * 3)           ;; (1 * 1)           ;; 2 - 0 = 2
(check= (multiply (list 2 5 4) (list 3 2) 0 0) 6)  ;; (2 * 3)           ;; (0 * 0)           ;; 3 - 3 = 0
(check= (multiply (list 2 5 4) (list 3 2) 1 1) 19) ;; (2 * 2) + (5 * 3) ;; (0 * 1) + (1 * 0) ;; 3 - 2 = 1
(check= (multiply (list 2 5 4) (list 3 2) 2 2) 22) ;; (4 * 3) + (5 * 2) ;; (2 * 0) + (1 * 1) ;; 3 - 1 = 2
(check= (multiply (list 2 5 4) (list 3 2) 3 3) 8)  ;; (4 * 2)           ;; (2 * 1)           ;; 3 - 0 = 3

;; run multiply recursively and add the results of multiplying to their correct places
(definec rec-multiply (l1 :loi l2 :loi l1-length :nat) :loi
  (cond
   ((zerop l1-length) (list (multiply l1 l2 l1-length l1-length)))
   (t (cons (multiply l1 l2 l1-length l1-length)
            (rec-multiply l1 l2 (1- l1-length))))))

(check= (rec-multiply (list 7 8) (list 4 3) 2) (list 24 53 28)) ;; but want (list 24 53 28)
(check= (rec-multiply (list 2 5 4) (list 3 2) 3) (list 8 22 19 6))

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

;; main function
(definec japanese-mult (i1 :nat i2 :nat) :int
  ;; (l1 (int-to-list i1))
  ;; (l2 (int-to-list i2))
  (list-to-int (process-carry (reverse (rec-multiply (int-to-list i1)
                                            (int-to-list i2)
                                            (len (int-to-list i1))))
                              0)))

(check= (japanese-mult 87 34) 2958)
(check= (japanese-mult 254 54) 13716)
(check= (japanese-mult 12 3) 36)
(check= (japanese-mult 73 247) 20002)

(defthm japanese-multiplication
  (implies (and (natp x) (natp y))
           (equal (japanese-mult x y) (* x y))))

;(defconst *japanese-mult-contract-theorem*
;  '(implies (and (natp x) (natp y)) (equal (japanese-mult x y) (* x y))))

;(make-event `(thm ,*japanese-mult-contract-theorem*))
