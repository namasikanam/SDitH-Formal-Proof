import SDitH.Proofs.PairFork
import SDitH.Proofs.CandidateReduction
import SDitH.Proofs.SharedSlopeGame
import SDitH.Proofs.SeedPairing

/-! The seed-collision event as a witnessed pair: a recorded seed collision
at a leaf (two distinct seeds whose four expansion entries are recorded in
the union of the two branches' histories and whose commitments agree) is
witnessed, under the layout's output projection and the layout's transport
of the seed-pairing companion, by every family matching that union. The
transport needs the layout's input map injective (hence bijective on the
finite block type) and the key map injective. -/

namespace SDitH.Proofs.SeedCollisionWitness

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open Spec.IdealCipher Spec.IdealCipherPairCollision Spec.SeedPrimitives Spec.SeedPairing
open CandidateReduction CandidateBAVC PairFork SeedPairing
open scoped Classical ENNReal

noncomputable section

section Transport

variable {lambda : Nat} (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
  (hin : Function.Injective layout.input)

/-- The layout's input map as an equivalence. -/
def inputEquiv : Bits lambda ≃ Bits lambda :=
  Equiv.ofBijective layout.input hin.bijective_of_finite

/-- The seed-pairing companion transported through the layout's input map. -/
def companionL (y : Bits lambda) : Bits lambda :=
  layout.input (companion ((inputEquiv layout hin).symm y))

theorem inputEquiv_apply (x : Bits lambda) : inputEquiv layout hin x = layout.input x := rfl

theorem companionL_input (x : Bits lambda) : companionL layout hin (layout.input x) = layout.input (companion x) := by
  unfold companionL
  rw [← inputEquiv_apply layout hin x, Equiv.symm_apply_apply]

theorem companionL_involutive : Function.Involutive (companionL layout hin) := by
  intro y
  have h1 : companionL layout hin y = layout.input (companion ((inputEquiv layout hin).symm y)) := rfl
  rw [h1, companionL_input, companion_involutive]
  exact Equiv.apply_symm_apply (inputEquiv layout hin) y

theorem companionL_ne (hlambda : 0 < lambda) (y : Bits lambda) : companionL layout hin y ≠ y := by
  intro h
  have hy : layout.input ((inputEquiv layout hin).symm y) = y := Equiv.apply_symm_apply (inputEquiv layout hin) y
  rw [companionL] at h
  conv_rhs at h => rw [← hy]
  exact companion_ne hlambda _ (hin h)

end Transport

section Event

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The event is off without a fork result. -/
theorem seedCollision_none {State : Type*} (snapshot : Snap F lambda s higherCount w widths State) :
    seedCollision V snapshot none = false := rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A recorded seed collision is witnessed by every family matching the
union of the two attempt histories. -/
theorem seedCollision_witnessed {State : Type*} (hin : Function.Injective V.layout.input)
    (hkey : Function.Injective V.layout.key) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (snapshot : Snap F lambda s higherCount w widths State)
    (left right : Br F lambda tau kappa s higherCount w widths)
    (h : seedCollision V snapshot (some (left, right)) = true)
    (g : Family (Bits lambda) (Bits lambda))
    (hg : Matches g (attemptHistory right ++ attemptHistory left)) :
    Witnessed V.layout.output (companionL V.layout hin) g (attemptHistory right ++ attemptHistory left) := by
  have h' := h
  simp only [seedCollision, onAttempts] at h'
  unfold attemptHistory at hg ⊢
  revert h' hg
  cases hl' : left.checked.terminal with
  | attempt a =>
    cases hr' : right.checked.terminal with
    | attempt b =>
      intro hg h'
      simp only at h' hg ⊢
      cases hba : a.signature.body with
      | none => rw [hba] at h'; simp at h'
      | some bodyA =>
        cases hbb : b.signature.body with
        | none => rw [hba, hbb] at h'; simp at h'
        | some bodyB =>
          rw [hba, hbb] at h'
          simp only at h'
          obtain ⟨e, i, ls, rs, hcoll, hls, hrs⟩ := of_decide_eq_true h'
          set fam := snapshot.world.other.family with hfam
          set salt := bodyA.1 with hsalt
          set address := tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i with haddr
          have hside : ∀ side : Bool,
              Spec.BAVCCipherProgram.encStar V.layout fam ls (cipherInput V.variant salt address side) =
                Spec.BAVCCipherProgram.encStar V.layout fam rs (cipherInput V.variant salt address side) :=
            (BAVCBindingReconstruction.commitSeed_eq_iff (tau * 2 ^ kappa) V.variant
              (Spec.BAVCCipherProgram.encStar V.layout fam) salt ls rs (Spec.SeedTree.leafOffset e i)).mp hcoll.2
          have hmem : ∀ x, x ∈ a.world.other.cipherHistory ++ b.world.other.cipherHistory →
              x ∈ b.world.other.cipherHistory ++ a.world.other.cipherHistory := by
            intro x hx
            rw [List.mem_append] at hx ⊢
            exact hx.symm
          have hcomp : cipherInput V.variant salt address true = companion (cipherInput V.variant salt address false) :=
            cipherInput_companion hl hL (by
              have := SharedSlopeGame.leafOffset_bound (tau := tau) (kappa := kappa) e i
              simp only [Spec.SharedSlopeGame.leafCount] at this
              omega) V.variant salt
          have h1 : g (V.layout.key ls) (V.layout.input (cipherInput V.variant salt address true)) =
              fam (V.layout.key ls) (V.layout.input (cipherInput V.variant salt address true)) := hg _ (hmem _ (hls true))
          have h2 : g (V.layout.key rs) (V.layout.input (cipherInput V.variant salt address true)) =
              fam (V.layout.key rs) (V.layout.input (cipherInput V.variant salt address true)) := hg _ (hmem _ (hrs true))
          refine ⟨_, hmem _ (hls false), _, hmem _ (hrs false), ?_, rfl, hside false, ?_⟩
          · intro hk
            exact hcoll.1 (hkey hk)
          · show V.layout.output (g (V.layout.key ls)
                (companionL V.layout hin (V.layout.input (cipherInput V.variant salt address false)))) =
              V.layout.output (g (V.layout.key rs)
                (companionL V.layout hin (V.layout.input (cipherInput V.variant salt address false))))
            rw [companionL_input, ← hcomp, h1, h2]
            exact hside true
    | exhausted t => intro _ h'; simp at h'
    | aborted t => intro _ h'; simp at h'
    | rejected t => intro _ h'; simp at h'
  | exhausted t => intro _ h'; simp at h'
  | aborted t => intro _ h'; simp at h'
  | rejected t => intro _ h'; simp at h'

end Event

end
end SDitH.Proofs.SeedCollisionWitness
