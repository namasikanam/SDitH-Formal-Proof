import SDitH.Proofs.CandidateReduction
import SDitH.Proofs.InvCExtra
import SDitH.Proofs.SharedSlopeGame
import SDitH.Proofs.SeedPairing

/-! The slope-game event with the stored mask and the chain: the setting of
the shared slope game read from the signer and the verifier, the identity
layout's commitments and expansion entries in the shared game's form, and
the event that the first branch's claim (its salt, the completed seed
vector and its auxiliary data) is chained in the snapshot's table, has every
seed's expansion recorded in the union of the two histories, and has two
executions' slopes differing but equal under the mask stored in the
snapshot's table at the claim's auxiliary digest. This event is the one
the shared slope-game coverage can bound; it implies the existential-mask
event used so far. -/

namespace SDitH.Proofs.SlopeEventSetting

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open Spec.IdealCipher Spec.SeedPrimitives Spec.SlopeConsistency Spec.SharedSlopeGame Spec.BAVCChainInputs Spec.SeedPairing
open Spec.ConsistencyMatrix (masked)
open CandidateReduction CandidateBAVC SeedPairing CandidateSimulator SharedSigner
open scoped Classical

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))

/-- The shared slope game's setting read from the signer's primitives and
the verifier's encoding and variant. -/
def slopeSetting : Setting lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) :=
  ⟨S.signer.p, S.signer.randomCount, S.signer.enough, V.encoding, V.variant⟩

section Layout

variable {wit rnd : Nat}

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- Under the identity layout, the induced primitives' seed commitment is
the shared game's commitment. -/
theorem induced_commitSeed (family : Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Spec.SlopeConsistencyGame.Out lambda s wit rnd)) (variant : Grinding)
    (salt seed : Bits lambda) (e : Fin tau) (i : Fin (2 ^ kappa)) :
    (induced (tau := tau) (kappa := kappa) family table (Spec.BAVCCipherProgram.fullLayout lambda) variant).commitSeed salt seed
        (Spec.SeedTree.leafOffset e i) =
      commitOf (tau := tau) (kappa := kappa) variant family salt e i seed := rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- Under the identity layout, the expansion entries of a seed are the
shared game's two seed entries. -/
theorem expandEntries_fullLayout (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (family : Family (Bits lambda) (Bits lambda)) (ciphers : List (Entry (Bits lambda) (Bits lambda))) (variant : Grinding)
    (salt seed : Bits lambda) (e : Fin tau) (i : Fin (2 ^ kappa))
    (h : expandEntries family ciphers (Spec.BAVCCipherProgram.fullLayout lambda) variant salt
      (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) seed) :
    seedEntry family seed (input0 (tau := tau) (kappa := kappa) variant salt e i) ∈ ciphers ∧
      seedEntry family seed (companion (input0 (tau := tau) (kappa := kappa) variant salt e i)) ∈ ciphers := by
  have hcomp : cipherInput variant salt (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) true =
      companion (cipherInput variant salt (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) false) :=
    cipherInput_companion hl hL (by
      have := SharedSlopeGame.leafOffset_bound (tau := tau) (kappa := kappa) e i
      simp only [Spec.SharedSlopeGame.leafCount] at this
      omega) variant salt
  refine ⟨h false, ?_⟩
  have h1 := h true
  rw [hcomp] at h1
  exact h1

end Layout

/-- The slope-game event with the stored mask: the first branch's claim is
chained in its table, every seed's expansion is recorded in the union of the
two histories, and two executions' slopes differ but agree under the mask
stored in the snapshot's table at the claim's auxiliary digest. -/
def slopeWinC {State : Type*} (snapshot : Snap F lambda s higherCount w widths State) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a b bodyA bodyB =>
    decide (∃ c : Claim lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)),
      c.salt = bodyA.1 ∧ c.full = fullOf V a bodyA bodyB ∧ c.aux = bodyA.2.1 ∧
      ChainIn' (slopeSetting S V) snapshot.world.other.family snapshot.world.other.hashTable c ∧
      Queried (slopeSetting S V) snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory) c ∧
      ∃ pm, snapshot.world.other.hashTable (maskInput c.auxiliary) = some pm ∧
        ∃ e e', slopeOf (slopeSetting S V) c e ≠ slopeOf (slopeSetting S V) c e' ∧
          ∀ a', masked pm.2 (slopeOf (slopeSetting S V) c e) a' = masked pm.2 (slopeOf (slopeSetting S V) c e') a')

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem slopeWinC_none {State : Type*} (snapshot : Snap F lambda s higherCount w widths State) :
    slopeWinC S V snapshot none = false := rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The shared game's slope of a claim with the branch's data is the
branch's slope. -/
theorem slopeOf_eq (a : Att F lambda tau kappa s higherCount w widths)
    (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths)
    (c : Claim lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hsalt : c.salt = bodyA.1) (hfull : c.full = fullOf V a bodyA bodyB) (haux : c.aux = bodyA.2.1) (e : Fin tau) :
    slopeOf (slopeSetting S V) c e = slopesOf S V a bodyA bodyB e := by
  unfold slopeOf slopesOf slopeSetting
  rw [hsalt, hfull, haux]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The stored-mask event implies the existential-mask event. -/
theorem slopeWin_of_slopeWinC {State : Type*} (snapshot : Snap F lambda s higherCount w widths State)
    (result : Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths))
    (h : slopeWinC S V snapshot result = true) : slopeWin S V result = true := by
  rcases result with _ | ⟨left, right⟩
  · exact h
  simp only [slopeWinC, slopeWin, onAttempts] at h ⊢
  revert h
  cases left.checked.terminal with
  | attempt a =>
    cases right.checked.terminal with
    | attempt b =>
      intro h
      simp only at h ⊢
      rcases hba : a.signature.body with _ | bodyA
      · rw [hba] at h; simp at h
      rcases hbb : b.signature.body with _ | bodyB
      · rw [hba, hbb] at h; simp at h
      rw [hba, hbb] at h
      simp only at h ⊢
      obtain ⟨c, hsalt, hfull, haux, -, -, pm, -, e, e', hne, hmask⟩ := of_decide_eq_true h
      refine decide_eq_true ⟨pm.2, e, e', ?_, ?_⟩
      · rw [← slopeOf_eq S V a bodyA bodyB c hsalt hfull haux e, ← slopeOf_eq S V a bodyA bodyB c hsalt hfull haux e']
        exact hne
      · intro a'
        rw [← slopeOf_eq S V a bodyA bodyB c hsalt hfull haux e, ← slopeOf_eq S V a bodyA bodyB c hsalt hfull haux e']
        exact hmask a'
    | exhausted t => intro h; simp at h
    | aborted t => intro h; simp at h
    | rejected t => intro h; simp at h
  | exhausted t => intro h; simp at h
  | aborted t => intro h; simp at h
  | rejected t => intro h; simp at h

end
end SDitH.Proofs.SlopeEventSetting
