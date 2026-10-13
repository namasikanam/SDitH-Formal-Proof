import SDitH.Proofs.BLCArithmetic

/-! The translation structure of the committed arithmetic in one party's
random vector. The common accumulator is the sum of execution zero's
party vectors, so it is any one party's vector plus the sum of the others;
the witness correction, the randomness lines' constants and the plain
consistency check are therefore translations of values depending only on
the other parties by (linear images of) that party's vector. With the
hidden party's vector uniform and independent (a PRG hypothesis recorded
as a pending decision), these are the one-time pads of the
honest-verifier zero-knowledge argument. -/

namespace SDitH.Proofs.HiddenShareTranslation

open Spec.BLC Polynomial
open scoped BigOperators

noncomputable section

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

theorem foldExecution_acc {N ell kappa : Nat} (phi : Fin N → Fin kappa → K) (random : Fin N → Fin ell → K) (c : Fin ell) :
    (foldExecution phi random).acc c = ∑ i, random i c := by
  unfold foldExecution
  rw [SDitH.Proofs.BLC.foldl_acc, List.map_ofFn]
  simp [List.sum_ofFn]

theorem commonAcc_eq_sum {tau N ell kappa : Nat} [NeZero tau] (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (c : Fin ell) :
    commonAcc phi random c = ∑ i, random 0 i c := by
  unfold commonAcc foldExecutions
  exact foldExecution_acc phi (random 0) c

/-- The sum of the other parties' vectors at execution zero. -/
def others {tau N ell : Nat} [NeZero tau] (random : Fin tau → Fin N → Fin ell → K) (h : Fin N) (c : Fin ell) : K :=
  ∑ i ∈ Finset.univ.erase h, random 0 i c

/-- The common accumulator is the hidden party's vector plus the others. -/
theorem commonAcc_translate {tau N ell kappa : Nat} [NeZero tau] (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (h : Fin N) (c : Fin ell) :
    commonAcc phi random c = random 0 h c + others random h c := by
  rw [commonAcc_eq_sum, others, ← Finset.add_sum_erase _ _ (Finset.mem_univ h)]

variable {tau N kappa s wit rnd : Nat} [NeZero tau]

/-- The witness correction is the witness minus the others, translated by the
hidden party's vector. -/
theorem witnessCorrection_translate (xi : F) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K) (M : Matrix (Fin s) (Fin (wit + rnd)) K)
    (witness : Fin wit → K) (h : Fin N) (j : Fin wit) :
    (commitArithmetic xi phi random M witness).witnessCorrection j =
      (witness j - others random h (witnessIndex j)) - random 0 h (witnessIndex j) := by
  simp only [commitArithmetic, commonAcc_translate phi random h]
  ring

/-- The randomness line's constant is the hidden party's coordinate plus the
others, in the field. -/
theorem randomnessLine_constant_translate (xi : F) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K) (M : Matrix (Fin s) (Fin (wit + rnd)) K)
    (witness : Fin wit → K) (h : Fin N) (j : Fin rnd) :
    ((commitArithmetic xi phi random M witness).randomnessLines j).coeff 0 =
      algebraMap K F (random 0 h (randomnessIndex j)) + algebraMap K F (others random h (randomnessIndex j)) := by
  simp only [commitArithmetic, buildLine, coeff_add, coeff_C, coeff_C_mul_X, commonAcc_translate phi random h, map_add]
  simp

/-- The plain consistency check is linear in the accumulator, so it is the
check of the others translated by the check of the hidden party's vector. -/
theorem plainCheck_translate (xi : F) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K) (M : Matrix (Fin s) (Fin (wit + rnd)) K)
    (witness : Fin wit → K) (h : Fin N) :
    (commitArithmetic xi phi random M witness).plainCheck =
      consistencyCheck M (random 0 h) + consistencyCheck M (others random h) := by
  simp only [commitArithmetic, consistencyCheck]
  rw [← Matrix.mulVec_add]
  congr 1
  funext c
  exact commonAcc_translate phi random h c

end
end SDitH.Proofs.HiddenShareTranslation
