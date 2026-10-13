import SDitH.Proofs.BinaryIrreducibility
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Nat.Bits

/-! Executable binary-polynomial arithmetic with a proved interpretation in
`(ZMod 2)[X]`. Computations in this module are ordinary Lean definitions; their
certificate equalities must be discharged by the kernel, without native code
being accepted as proof. -/

namespace SDitH.Proofs.BinaryPolynomialCertificate

open Polynomial

abbrev Bits := List Bool

/-- Little-endian coefficients, including a possible zero tail. -/
noncomputable def polynomial : Bits → (ZMod 2)[X]
  | [] => 0
  | b :: bs => (if b then 1 else 0) + X * polynomial bs

/-- Drop an all-zero leading coefficient while constructing a canonical list. -/
def cons (b : Bool) (bs : Bits) : Bits :=
  if b = false ∧ bs = [] then [] else b :: bs

def add : Bits → Bits → Bits
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => cons (a ^^ b) (add as bs)

def mul : Bits → Bits → Bits
  | [], _ => []
  | a :: as, bs => if a then add bs (cons false (mul as bs)) else cons false (mul as bs)

def square : Bits → Bits
  | [] => []
  | a :: as => cons a (cons false (square as))

theorem polynomial_cons (b : Bool) (bs : Bits) :
    polynomial (cons b bs) = (if b then 1 else 0) + X * polynomial bs := by
  unfold cons
  by_cases h : b = false ∧ bs = []
  · rw [if_pos h]
    rcases h with ⟨rfl, rfl⟩
    simp [polynomial]
  · rw [if_neg h]
    rfl

theorem polynomial_add (as bs : Bits) :
    polynomial (add as bs) = polynomial as + polynomial bs := by
  induction as generalizing bs with
  | nil => simp [add, polynomial]
  | cons a as ih =>
    cases bs with
    | nil => simp [add, polynomial]
    | cons b bs =>
      rw [add, polynomial_cons, ih]
      cases a <;> cases b <;> simp [polynomial, mul_add, add_assoc, add_left_comm,
        CharTwo.add_cancel_left]

theorem polynomial_mul (as bs : Bits) :
    polynomial (mul as bs) = polynomial as * polynomial bs := by
  induction as with
  | nil => simp [mul, polynomial]
  | cons a as ih =>
    cases a <;> simp [mul, polynomial_add, polynomial_cons, polynomial, ih] <;> ring

theorem polynomial_square (as : Bits) :
    polynomial (square as) = polynomial as ^ 2 := by
  induction as with
  | nil => simp [square, polynomial]
  | cons a as ih =>
    cases a <;> simp [square, polynomial_cons, polynomial, CharTwo.add_sq, mul_pow, ih] <;> ring

structure SquareStep where
  quotient : Bits
  result : Bits

def checkChain (f start : Bits) : List SquareStep → Bool
  | [] => true
  | step :: rest =>
      (square start == add (mul f step.quotient) step.result) && checkChain f step.result rest

def finish (start : Bits) : List SquareStep → Bits
  | [] => start
  | step :: rest => finish step.result rest

theorem checkChain_take (f start : Bits) (steps : List SquareStep) (k : Nat)
    (h : checkChain f start steps = true) : checkChain f start (steps.take k) = true := by
  induction steps generalizing start k with
  | nil => simp [checkChain]
  | cons step rest ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.take_succ_cons, checkChain, Bool.and_eq_true, beq_iff_eq] at h ⊢
      exact ⟨h.1, ih step.result k h.2⟩

theorem checkChain_append (f start : Bits) (left right : List SquareStep) :
    checkChain f start (left ++ right) =
      (checkChain f start left && checkChain f (finish start left) right) := by
  induction left generalizing start with
  | nil => simp [checkChain, finish]
  | cons step rest ih => simp [checkChain, finish, ih, Bool.and_assoc]

theorem finish_append (start : Bits) (left right : List SquareStep) :
    finish start (left ++ right) = finish (finish start left) right := by
  induction left generalizing start with
  | nil => rfl
  | cons step rest ih => exact ih step.result

theorem chain_power (f start : Bits) (steps : List SquareStep)
    (h : checkChain f start steps = true) :
    aeval (AdjoinRoot.root (polynomial f)) (polynomial (finish start steps)) =
      (aeval (AdjoinRoot.root (polynomial f)) (polynomial start)) ^ (2 ^ steps.length) := by
  induction steps generalizing start with
  | nil => simp [finish]
  | cons step rest ih =>
    have h' := h
    simp only [checkChain, Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨hs, ht⟩ := h'
    have heq := congrArg polynomial hs
    rw [polynomial_square, polynomial_add, polynomial_mul] at heq
    have heval := congrArg (aeval (AdjoinRoot.root (polynomial f))) heq
    simp only [map_pow, map_add, map_mul, AdjoinRoot.aeval_eq,
      AdjoinRoot.mk_self, zero_mul, zero_add] at heval
    rw [finish, ih step.result ht, AdjoinRoot.aeval_eq, ← heval, ← pow_mul]
    rw [AdjoinRoot.aeval_eq]
    simp only [List.length_cons, Nat.pow_succ]
    congr 1
    omega

theorem chain_dvd (f : Bits) (steps : List SquareStep)
    (h : checkChain f [false, true] steps = true) :
    polynomial f ∣ X ^ (2 ^ steps.length) - polynomial (finish [false, true] steps) := by
  rw [← AdjoinRoot.mk_eq_mk]
  have hp := (chain_power f [false, true] steps h).symm
  simpa only [polynomial, Bool.false_eq_true, if_false, if_true, mul_zero, add_zero,
    mul_one, zero_add, map_pow, aeval_X, AdjoinRoot.aeval_eq] using hp

/-- The checked identity supplies explicit Bezout witnesses. -/
theorem coprime_of_check (f r a b : Bits)
    (h : add (mul f a) (mul r b) = [true]) :
    IsCoprime (polynomial f) (polynomial r) := by
  have heq := congrArg polynomial h
  simp only [polynomial_add, polynomial_mul, polynomial,
    if_true, mul_zero, add_zero] at heq
  exact ⟨polynomial a, polynomial b, by simpa only [mul_comm] using heq⟩

theorem coprime_of_dvd_sub {f p r : (ZMod 2)[X]} (hd : f ∣ p - r)
    (hc : IsCoprime f (r - X)) : IsCoprime f (p - X) := by
  obtain ⟨q, hq⟩ := hd
  obtain ⟨a, b, hab⟩ := hc
  refine ⟨a - b * q, b, ?_⟩
  linear_combination hab + b * hq

theorem coprime_frobenius_of_check (f r a b : Bits) (n : Nat)
    (hd : polynomial f ∣ X ^ (2 ^ n) - polynomial r)
    (hc : add (mul f a) (mul (add r [false, true]) b) = [true]) :
    IsCoprime (polynomial f) (X ^ (2 ^ n) - X) := by
  apply coprime_of_dvd_sub hd
  have h := coprime_of_check f (add r [false, true]) a b hc
  simpa only [polynomial_add, polynomial, Bool.false_eq_true, if_false, if_true,
    mul_zero, add_zero, mul_one, zero_add, CharTwo.sub_eq_add] using h

/-- A Euclidean remainder transcript avoids reducing large dense products in
one kernel computation. The final nonzero remainder must be exactly one. -/
def checkEuclid (f r : Bits) : List SquareStep → Bool
  | [] => r == [true]
  | step :: rest =>
      (f == add (mul step.quotient r) step.result) && checkEuclid r step.result rest

def checkRemainders (f r : Bits) : List SquareStep → Bool
  | [] => true
  | step :: rest =>
      (f == add (mul step.quotient r) step.result) && checkRemainders r step.result rest

def euclidFinish (f r : Bits) : List SquareStep → Bits × Bits
  | [] => (f, r)
  | step :: rest => euclidFinish r step.result rest

theorem checkEuclid_append (f r : Bits) (left right : List SquareStep) :
    checkEuclid f r (left ++ right) = (checkRemainders f r left &&
      checkEuclid (euclidFinish f r left).1 (euclidFinish f r left).2 right) := by
  induction left generalizing f r with
  | nil => simp [checkRemainders, euclidFinish]
  | cons step rest ih => simp [checkEuclid, checkRemainders, euclidFinish, ih, Bool.and_assoc]

theorem coprime_of_euclid (f r : Bits) (steps : List SquareStep)
    (h : checkEuclid f r steps = true) : IsCoprime (polynomial f) (polynomial r) := by
  induction steps generalizing f r with
  | nil =>
    have hr : r = [true] := beq_iff_eq.mp h
    exact ⟨0, 1, by simp [hr, polynomial]⟩
  | cons step rest ih =>
    simp only [checkEuclid, Bool.and_eq_true, beq_iff_eq] at h
    have heq := congrArg polynomial h.1
    rw [polynomial_add, polynomial_mul] at heq
    obtain ⟨a, b, hab⟩ := ih r step.result h.2
    refine ⟨b, a - b * polynomial step.quotient, ?_⟩
    linear_combination hab + b * heq

theorem coprime_frobenius_of_euclid (f r : Bits) (n : Nat) (steps : List SquareStep)
    (hd : polynomial f ∣ X ^ (2 ^ n) - polynomial r)
    (hc : checkEuclid f (add r [false, true]) steps = true) :
    IsCoprime (polynomial f) (X ^ (2 ^ n) - X) := by
  apply coprime_of_dvd_sub hd
  have h := coprime_of_euclid f (add r [false, true]) steps hc
  simpa only [polynomial_add, polynomial, Bool.false_eq_true, if_false, if_true,
    mul_zero, add_zero, mul_one, zero_add, CharTwo.sub_eq_add] using h

end SDitH.Proofs.BinaryPolynomialCertificate
