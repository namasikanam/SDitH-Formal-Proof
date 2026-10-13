import SDitH.Proofs.HiddenShareTranslation
import SDitH.Spec.BLCCommit

/-! The per-execution corrections as translations. Execution e's correction
is the common accumulator minus execution e's accumulator, which is the sum
of execution e's party vectors; so it is a value depending on the common
accumulator and execution e's other parties, translated by execution e's
hidden party's vector. Together with the execution-zero translations these
are all the pads of the auxiliary data: each execution's hidden vector
pads its own correction, and execution zero's hidden vector pads the
witness correction, the plain check and the hashed coefficients. -/

namespace SDitH.Proofs.CorrectionTranslation

open Spec.BLC HiddenShareTranslation
open scoped BigOperators

noncomputable section

variable {K : Type*} [CommRing K]

/-- The sum of the other parties' vectors at an execution. -/
def othersAt {tau N ell : Nat} (random : Fin tau → Fin N → Fin ell → K) (e : Fin tau) (h : Fin N) (c : Fin ell) : K :=
  ∑ i ∈ Finset.univ.erase h, random e i c

theorem others_eq_othersAt {tau N ell : Nat} [NeZero tau] (random : Fin tau → Fin N → Fin ell → K) (h : Fin N) :
    others random h = othersAt random 0 h := rfl

/-- An execution's accumulator is its hidden party's vector plus the others. -/
theorem foldExecutions_acc {tau N ell kappa : Nat} (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (e : Fin tau) (h : Fin N) (c : Fin ell) :
    (foldExecutions phi random e).acc c = random e h c + othersAt random e h c := by
  unfold foldExecutions othersAt
  rw [foldExecution_acc, ← Finset.add_sum_erase _ _ (Finset.mem_univ h)]

/-- An execution's correction is the common accumulator minus the others,
translated by the execution's hidden vector. -/
theorem correction_translate {tau N ell kappa : Nat} [NeZero tau] (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (e : Fin tau) (h : Fin N) (c : Fin ell) :
    correction phi random e c = (commonAcc phi random c - othersAt random e h c) - random e h c := by
  unfold correction
  rw [Pi.sub_apply, foldExecutions_acc phi random e h c]
  ring

/-- The transmitted corrections are the positive executions' corrections. -/
theorem positiveCorrections_translate {tau N ell kappa : Nat} [NeZero tau] (phi : Fin N → Fin kappa → ZMod 2)
    (random : Fin tau → Fin N → Fin ell → ZMod 2) (hidden : Fin tau → Fin N) (j : Fin (tau - 1)) (c : Fin ell) :
    Spec.BLCCommit.positiveCorrections (correction phi random) j c =
      (commonAcc phi random c - othersAt random (Spec.BLCCommit.positiveIndex j) (hidden (Spec.BLCCommit.positiveIndex j)) c) -
        random (Spec.BLCCommit.positiveIndex j) (hidden (Spec.BLCCommit.positiveIndex j)) c := by
  unfold Spec.BLCCommit.positiveCorrections
  exact correction_translate phi random _ _ c

end
end SDitH.Proofs.CorrectionTranslation
