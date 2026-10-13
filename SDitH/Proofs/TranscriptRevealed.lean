import SDitH.Proofs.RevealedBijection

/-! The honest committed arithmetic's revealed triple is the revealed map of
the hidden party's vector with the other parties' contributions as
constants. Composed with the bijection, a uniform hidden vector makes the
honest triple uniform and independent of the witness: the deterministic
core of the hidden-share step of the zero-knowledge argument, pending the
PRG hypothesis that supplies the uniform vector. -/

namespace SDitH.Proofs.TranscriptRevealed

open Spec.BLC Polynomial HiddenShareTranslation RevealedBijection
open scoped BigOperators Classical

noncomputable section

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]
variable {tau N kappa s wit rnd : Nat} [NeZero tau]

/-- The constants contributed by the other parties. -/
def constantsA (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K) (witness : Fin wit → K) (h : Fin N) :
    Fin wit → K :=
  fun j => witness j - others random h (witnessIndex j)

def constantsB (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K) (h : Fin N) : Fin rnd → K :=
  fun j => others random h (randomnessIndex j)

def constantsC (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K) (M : Matrix (Fin s) (Fin (wit + rnd)) K)
    (h : Fin N) : Fin s → K :=
  consistencyCheck M (others random h)

/-- The honest triple, with the randomness constants read in the base ring, is
the revealed map of the hidden party's vector. -/
theorem triple_eq_revealed (xi : F) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K) (M : Matrix (Fin s) (Fin (wit + rnd)) K)
    (witness : Fin wit → K) (h : Fin N) :
    ((commitArithmetic xi phi random M witness).witnessCorrection,
      fun j => commonAcc phi random (randomnessIndex j),
      (commitArithmetic xi phi random M witness).plainCheck) =
      revealedMap M (constantsA random witness h) (constantsB random h) (constantsC random M h) (random 0 h) := by
  unfold revealedMap constantsA constantsB constantsC
  refine Prod.ext (funext fun j => ?_) (Prod.ext (funext fun j => ?_) (funext fun a => ?_))
  · dsimp only
    rw [witnessCorrection_translate xi phi random M witness h j]
  · dsimp only
    exact commonAcc_translate phi random h _
  · dsimp only
    rw [plainCheck_translate xi phi random M witness h]
    simp [consistencyCheck]

/-- The randomness constants of the lines are the algebra images of the
accumulator coordinates. -/
theorem randomnessLines_constant (xi : F) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K) (M : Matrix (Fin s) (Fin (wit + rnd)) K)
    (witness : Fin wit → K) (j : Fin rnd) :
    ((commitArithmetic xi phi random M witness).randomnessLines j).coeff 0 =
      algebraMap K F (commonAcc phi random (randomnessIndex j)) := by
  simp [commitArithmetic, buildLine, coeff_add, coeff_C]

/-- With a uniform hidden vector, the honest base-ring triple is uniform and
independent of the witness. -/
theorem triple_uniform [Fintype K] [Nonempty K] (xi : F) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K) (M : Matrix (Fin s) (Fin (wit + rnd)) K)
    (witness : Fin wit → K) (h : Fin N) :
    (PMF.uniformOfFintype (Fin (s + (wit + rnd)) → K)).map (fun v =>
        let random' := Function.update random 0 (Function.update (random 0) h v)
        ((commitArithmetic xi phi random' M witness).witnessCorrection,
          fun j => commonAcc phi random' (randomnessIndex j),
          (commitArithmetic xi phi random' M witness).plainCheck)) =
      PMF.uniformOfFintype ((Fin wit → K) × (Fin rnd → K) × (Fin s → K)) := by
  have hothers : ∀ v, others (Function.update random 0 (Function.update (random 0) h v)) h = others random h := by
    intro v
    funext c
    unfold others
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : i ≠ h := Finset.ne_of_mem_erase hi
    simp [hne]
  have hmap : (fun v : Fin (s + (wit + rnd)) → K =>
      let random' := Function.update random 0 (Function.update (random 0) h v)
      ((commitArithmetic xi phi random' M witness).witnessCorrection,
        fun j => commonAcc phi random' (randomnessIndex j),
        (commitArithmetic xi phi random' M witness).plainCheck)) =
      revealedMap M (constantsA random witness h) (constantsB random h) (constantsC random M h) := by
    funext v
    rw [triple_eq_revealed xi phi _ M witness h]
    unfold constantsA constantsB constantsC
    simp only [hothers, Function.update_self]
  rw [hmap]
  exact revealed_uniform M _ _ _

end
end SDitH.Proofs.TranscriptRevealed
