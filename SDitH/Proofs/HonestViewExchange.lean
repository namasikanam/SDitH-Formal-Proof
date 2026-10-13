import SDitH.Proofs.CommitViewExchange

/-! The candidate signings' inner views under the exchange. The honest
post-processing (the signature-level query and the body) and the simulated
one read the committed value only through its payload, its signed state's
key at the leaves, its seeds, lines and auxiliary data, none of which an
internal node of the tree enters; so for a fixed salt and root the
commitment run followed by either post-processing, viewed with the family
stripped and the history pruned, has the same law under the exchanged
family and under the family. -/

namespace SDitH.Proofs.HonestViewExchange

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.AbstractSignature Spec.SignatureSecurity
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open HiddenLeafNode TreeExchange CommitPhaseExchange CommitRunExchange CommitPruned CommitViewExchange CandidateResample
open scoped Classical

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths) (salt : Bits lambda)
  (b : Nat) (hbk : b ≤ tau * 2 ^ kappa - 1) (x : Seed lambda)

include hbk in
/-- An internal node is no leaf. -/
theorem internal_ne_leaf (e : Fin tau) (i : Fin (2 ^ kappa)) : (leafNode e i).val ≠ b := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  have hge : tau * 2 ^ kappa ≤ Spec.SeedTree.leafAddress e i := Nat.le_add_right _ _
  show Spec.SeedTree.leafAddress e i ≠ b
  omega

include hbk in
/-- The honest post-processing does not read an internal node. -/
theorem honestPost_setTree (pk message : List Bool)
    (table : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda))
    (c : Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    honestPost S pk message salt (.done (setTree b x c)) table = honestPost S pk message salt (.done c) table := by
  simp only [honestPost, payloadOf_setTree, bodyOf_setTree S salt b x (internal_ne_leaf b hbk)]

include hbk in
/-- The simulated post-processing does not read an internal node. -/
theorem simPost_setTree (pk message : List Bool) (digest : Digest lambda)
    (table : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda))
    (c : Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    simPost S pk message salt digest (.done (setTree b x c)) table = simPost S pk message salt digest (.done c) table := by
  simp only [simPost, stateOf, setTree, simulatedCoefficients]
  rw [attempt_setTree b x (internal_ne_leaf b hbk)]

end
end SDitH.Proofs.HonestViewExchange
