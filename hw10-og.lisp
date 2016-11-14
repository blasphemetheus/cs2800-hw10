#|
CS 2800 Homework 10 - Fall 2016 


This homework is done in groups. The rules are:

 * ALL group members must submit the homework file (this file)

 * The file submitted must be THE SAME for all group members (we
   use this to confirm that alleged group members agree to be
   members of that group)

 * You must list the names of ALL group members below using the
   format below. If you fail to follow instructions, that costs
   us time and it will cost you points, so please read carefully.


Names of ALL group members: FirstName1 LastName1, FirstName2 LastName2, ...

Note: There will be a 10 pt penalty if your names do not follow 
this format.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

For this homework you will need to use ACL2s.

Technical instructions:

- open this file in ACL2s as hw10.lisp

- make sure you are in BEGINNER mode. This is essential! Note that you can
  only change the mode when the session is not running, so set the correct
  mode before starting the session.

- insert your solutions into this file where indicated (usually as "...")

- only add to the file. Do not remove or comment out anything pre-existing
  unless asked to.

- make sure the entire file is accepted by ACL2s. In particular, there must
  be no "..." left in the code. If you don't finish all problems, comment
  the unfinished ones out. Comments should also be used for any English
  text that you may add. This file already contains many comments, so you
  can see what the syntax is.

- when done, save your file and submit it as hw10.lisp

- avoid submitting the session file (which shows your interaction with the
  theorem prover). This is not part of your solution. Only submit the lisp
  file!

|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lists of natural numbers (lon) and list of rationals (lor) are defined 
;; below for reference
(defdata lon (listof nat))
(defdata lor (listof rational))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; I. Product of rationals
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Consider the following function definition:

; prod : Lor -> Rational
; (prod l) is the product of the numbers in a list of rationals.
; If the list of numbers is empty, then the product is 1.
(defunc prod (l)
  :input-contract (lorp l)
  :output-contract (rationalp (prod l))
  (cond ((endp l) 1)
        (t (* (first l) (prod (rest l))))))


; The above is a correct function for prod, but it is not tail-recursive.

; (a) Define the product of a list of rationals tail recursively.

; prod-t : Lor x Rational -> Rational
; (prod-t l acc) is the product of the rational numbers in l and the
; rational number acc.  If the list l is empty, then the product is acc.
(defunc prod-t (l acc)
  :input-contract (and (lorp l) (rationalp acc))
  :output-contract (rationalp (prod-t l acc))
  ...)

; Give at least 4 check= checks for your prod-t function.
...

; (b) Define a function prod* with the same signature as prod such that (prod* l) 
; calls prod-t and is intended to compute the same value as (prod l)

; prod* : Lor -> Rational
; (prod* l) is the product of the numbers in a list of rationals.
; If the list of numbers is empty, then the product is 1.
(defunc prod* (l)
  :input-contract (lorp l)
  :output-contract (rationalp (prod* l))
  ...)

#|

(c) Formulate a lemma Tprod-t (don't prove it yet) that relates the value 
computed by (prod-t l acc) and the value computed by (prod l). Your lemma 
should have the following form:

Tprod-t : ... => (prod-t l acc) = ... (prod l) ...

Replace the ... by suitable hypotheses and ACL2 expressions. Function prod*
should not appear in this lemma.

(d) Assuming lemma Tprod-t above has been proven, prove the following claim
purely using equational reasoning. If you use Tprod-t, make sure to provide a
substitution.

Tprod*: (lorp l) => (prod l) = (prod* l)
...

(e) Finally, prove Tprod-t by induction. Use the induction scheme derived from the  
function prod-t.
...

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; II. Deletion from a list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

Consider the following function definition:
;; deletes ALL occurrences of x from the list l
(defunc delete (x l)
  :input-contract (listp l)
  :output-contract (listp (delete x l))
  (cond ((endp l)            ())
        ((equal x (first l)) (delete x (rest l)))
        (t                   (cons (first l) (delete x (rest l))))))

;; (a) Define a tail-recursive version delete-t of delete. Your function should 
;; have the signature shown below. Argument acc is an accumulator that collects 
;; intermediate results and, in the end, contains the final value.

(defunc delete-t (x l acc)
  :input-contract (and (listp l) (listp acc))
  :output-contract (listp (delete-t x l acc))
  ...)

;; (b) Define a function delete* with the same signature as delete such that
;; (delete* x l) calls delete-t and is intended to compute the same value as 
;; (delete x l).
...

#|
(c) Formulate a lemma psi that relates the value computed by (delete-t x l acc) and 
the value computed by (delete x l). Your lemma should have the following form:

psi : ... => (delete-t x l acc) = ... (delete x l) ...

Replace the ... by suitable hypotheses and ACL2 expressions. Function delete*
should not appear in the lemma.

(d) Assuming lemma psi above has been proven, prove the following claim
purely using equational reasoning. If you use psi, make sure to provide a
substitution.

psi*: (listp l) => (delete* x l) = (delete x l)
...

(e) Finally, prove psi by induction. Use the induction scheme suggested by
function delete-t
...
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; III. Exponentiation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; expt : Rational x Nat -> Rational
; (expt b p) is b raised to the power p. If p is zero, then the result is 1.

(defunc expt (b p)
  :input-contract (and (rationalp b) (natp p))
  :output-contract (rationalp (expt b p))
  (cond ((equal p 0) 1)
        (t (* b (expt b (- p 1))))))

(a)
; This is a correct function for exponentiation, but it is not tail-recursive.
; Define the same function so that it is tail-recursive.

; expt-t : Rational x Nat x Rational -> Rational
; (expt-t b p acc) is the product of acc with b raised to the expt p.
; If p is 0, then the result is acc.
; Replace the ... above with an explanation of what expt-t is computing.
(defunc expt-t (b p acc)
  :input-contract (and (rationalp b) (natp p) (rationalp acc))
  :output-contract (rationalp (expt-t b p acc))
  ...)

; Give at least 4 check= checks for your expt-t function in addition to the given ones.

(check= (expt-t 0 0 0) 0)
(check= (expt-t 0 0 1) 1)
...

(b)
;; Define a function expt* with the same signature as expt such that
;; (expt* b p) calls expt-t and is intended to compute the same value as 
;; (expt b p).

;; expt* : Rational x Nat -> Rational
;; (expt b p) is b raised to the power p. If p is zero, then the result is 1.
(defunc expt* (b p)
  :input-contract (and (rationalp b) (natp p))
  :output-contract (rationalp (expt* b p))
  ...)

#|

(c) Formulate a lemma Texpt-t that relates the value computed by (expt-t b p acc) and 
the value computed by (expt b p). Your lemma should have the following form:

Texpt-t : ... => (expt-t b p acc) = ... (expt b p) ...

Function expt* should not appear in the lemma.

(d) ASSUMING lemma Texpt-t above has been proven, prove the following claim PURELY using 
equational  reasoning (i.e., no induction). If you use Texpt-t, make sure to provide a 
substitution. State and prove that expt and expt* compute the same function. 

Texpt*:
(and (rationalp b) (natp p)) => (equal (expt b p) (expt* b p))

...

(e) Prove the lemma Texpt-t from (c)
...
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; PRACTICE QUESTION (no need to turn this in)
; IV. The next odd number
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Consider the following function get-next-odd that takes a list l of natural numbers
;; as input and returns the list of all elements n of l such that the element
;; *following* n in l is an odd natural number (which implies that n cannot
;; be the last element of l). See the test cases below. We assume that the
;; function oddp returns true exactly if its argument is an odd natural number.

(defunc get-next-odd (l)
  :input-contract (natlistp l)
  :output-contract (natlistp (get-next-odd l))
  (cond ((or (endp l) (endp (rest l)))     nil)
        ((oddp (second l)) (cons (first l) (get-next-odd (rest l))))
        (t                  (get-next-odd (rest l)))))


;; (a) Define a tail-recursive version get-next-odd-t of get-next-odd. Your function should 
;; have the signature shown below. Argument acc is an accumulator that collects 
;; intermediate results and, in the end, contains the final value.
(defunc get-next-odd-t (l acc)
  :input-contract (and (natlistp l) (natlistp acc))
  :output-contract (natlistp (get-next-odd-t l acc))
  ...)

(check= (get-next-odd-t '(4)             '(5 6 7)) '(5 6 7))
(check= (get-next-odd-t '(4 7)           '())      '(4))
(check= (get-next-odd-t '(10 1 3 2 4 4 5) '(5 6 7)) '(4 1 10 5 6 7))
;; Define two more check= checks

;; (b) Define a non-recursive function get-next-odd* with the same signature as  
;; get-next-odd such that get-next-odd* calls get-next-odd-t and is intended to
;; compute the same value as get-next-odd.
(defunc get-next-odd* (l)
  :input-contract (natlistp l)
  :output-contract (natlistp (get-next-odd* l))
  ...)


#|
(c) Formulate a lemma phi that relates the value computed by get-next-odd and 
the value computed by get-next-odd-t. Your lemma should have the following form:

phi : ... => (get-next-odd-t l acc) = ... (get-next-odd l) ...

Replace the ... by suitable hypotheses and ACL2 expressions. Function get-next-odd*
should NOT appear in the lemma.

(d) Assuming lemma phi above has been proven, prove the following claim
purely using equational reasoning. If you use phi, make sure to provide a
substitution.
phi* :(natlistp l) /\ (natlistp acc) => (get-next-odd* l) = (get-next-odd l)
...

(e) Finally, prove phi by induction.
...

|#
