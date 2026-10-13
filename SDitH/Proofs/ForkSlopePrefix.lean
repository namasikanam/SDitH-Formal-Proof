import SDitH.Proofs.ForkSlope

/-! Evaluation on a common prefix table. The two branches of a fork run on
tables that extend the shared prefix and on cipher histories that extend
the shared history. An evaluation reads only the hash inputs it visits; if
every visited input is already in the prefix, the evaluation holds on the
prefix itself, and evaluations are monotone in the cipher history. Hence
two verifications of a fork, one per branch, whose visited inputs lie in
the prefix, satisfy the fork-to-slope lemma on the prefix table with the
union of the two histories. Which visited inputs can lie outside the
prefix is the accounting left to the chain-mention bounds. -/

namespace SDitH.Proofs.ForkSlopePrefix

open Spec.BAVC Spec.DomainSeparation Spec.SharedScheme Spec.HashCipherProgram Spec.HashCipherEvaluation
open Spec.SlopeConsistency Spec.CandidateVerifier Spec.BLCSeedLines
open Spec.SlopeConsistencyGame (Out)
open scoped Classical
noncomputable section

section Generic

variable {Input Dig Key Block A : Type*}

/-- The hash inputs visited by a program against a table, stopping at the
first absent one. -/
def hashInputs (family : Spec.IdealCipher.Family Key Block) (table : Input → Option Dig) :
    Program Input Dig Key Block A → List Input
  | .done _ => []
  | .hash input next =>
    match table input with
    | some answer => input :: hashInputs family table (next answer)
    | none => [input]
  | .cipher request next => hashInputs family table (next (Spec.IdealCipher.answer family request))

theorem evaluates_restrict (family : Spec.IdealCipher.Family Key Block) (table P : Input → Option Dig)
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (program : Program Input Dig Key Block A) (value : A)
    (h : Evaluates family table ciphers program value)
    (hin : ∀ x ∈ hashInputs family table program, P x = table x) :
    Evaluates family P ciphers program value := by
  induction h with
  | done value => exact .done value
  | hash input next answer value stored _ ih =>
    have hvisited : hashInputs family table (.hash input next) = input :: hashInputs family table (next answer) := by
      simp [hashInputs, stored]
    rw [hvisited] at hin
    exact .hash input next answer value (by rw [hin input (List.mem_cons_self), stored])
      (ih fun x hx => hin x (List.mem_cons_of_mem input hx))
  | cipher request next value recorded _ ih =>
    exact .cipher request next value recorded (ih hin)

theorem evaluates_mono_ciphers (family : Spec.IdealCipher.Family Key Block) (table : Input → Option Dig)
    (ciphers more : List (Spec.IdealCipher.Entry Key Block)) (hsub : ∀ e ∈ ciphers, e ∈ more)
    (program : Program Input Dig Key Block A) (value : A) (h : Evaluates family table ciphers program value) :
    Evaluates family table more program value := by
  induction h with
  | done value => exact .done value
  | hash input next answer value stored _ ih => exact .hash input next answer value stored ih
  | cipher request next value recorded _ ih => exact .cipher request next value (hsub _ recorded) ih

end Generic

variable {lambda tau kappa s wit rnd : Nat}

/-- Two candidate-middle verifications on tables extending a prefix, with
all visited inputs in the prefix: the fork-to-slope outcome on the prefix
table and the union of the two cipher histories. -/
theorem fork_masked_slope_prefix {F : Type*} [Field F] [Algebra (ZMod 2) F] (xi : F)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (V : VerifierSetting F lambda tau kappa s wit rnd)
    (hmid : V.middle = candidateMiddle xi p V.nodes encode randomCount enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (saltL saltR : Bits lambda) (auxL auxR : Spec.BLCCommit.Auxiliary tau s wit rnd) (piopL piopR : Digest lambda)
    (decL decR : Spec.BLCRetry.Counter × Opening lambda tau)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (P tableL tableR : List Bool → Option (Out lambda s wit rnd))
    (hextL : ∀ x y, P x = some y → tableL x = some y) (hextR : ∀ x y, P x = some y → tableR x = some y)
    (ciphersL ciphersR : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (left right : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (hl : Evaluates family tableL ciphersL (verifyProgram V saltL auxL piopL decL) (Except.ok left))
    (hr : Evaluates family tableR ciphersR (verifyProgram V saltR auxR piopR decR) (Except.ok right))
    (hinL : ∀ x ∈ hashInputs family tableL (verifyProgram V saltL auxL piopL decL), (P x).isSome)
    (hinR : ∀ x ∈ hashInputs family tableR (verifyProgram V saltR auxR piopR decR), (P x).isSome)
    (hlines : left.lines = right.lines) (hfree : DigestCollisionFree P)
    (e : Fin tau) (hne : V.expand piopL decL.1 e ≠ V.expand piopR decR.1 e) :
    (∃ (i : Fin (2 ^ kappa)) (ls rs : Seed lambda), saltL = saltR ∧
        Spec.BAVCBinding.IsSeedCollision
          (Spec.BAVCReconstructionProgram.primitives (tau := tau) (N := 2 ^ kappa) V.layout V.variant family
            (SharedSchemeChain.projected P))
          saltL (Spec.SeedTree.leafOffset e i) ls rs ∧
        ∀ side : Bool,
          Spec.IdealCipher.entry (.encrypt (V.layout.key ls)
            (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
            (family (V.layout.key ls) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphersL ++ ciphersR ∧
          Spec.IdealCipher.entry (.encrypt (V.layout.key rs)
            (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
            (family (V.layout.key rs) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphersL ++ ciphersR) ∨
      ∃ (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (M : Spec.SlopeConsistencyGame.Mask s wit rnd),
        saltL = saltR ∧ auxL.corrections = auxR.corrections ∧ auxL.plain = auxR.plain ∧
        ∀ a, maskedSlope p saltL full randomCount enough auxL M e a = auxL.plain a := by
  have hPL : ∀ x ∈ hashInputs family tableL (verifyProgram V saltL auxL piopL decL), P x = tableL x := by
    intro x hx
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hinL x hx)
    rw [hy, hextL x y hy]
  have hPR : ∀ x ∈ hashInputs family tableR (verifyProgram V saltR auxR piopR decR), P x = tableR x := by
    intro x hx
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hinR x hx)
    rw [hy, hextR x y hy]
  have hl' := evaluates_mono_ciphers family P ciphersL (ciphersL ++ ciphersR)
    (fun e he => List.mem_append_left _ he) _ _ (evaluates_restrict family tableL P ciphersL _ _ hl hPL)
  have hr' := evaluates_mono_ciphers family P ciphersR (ciphersL ++ ciphersR)
    (fun e he => List.mem_append_right _ he) _ _ (evaluates_restrict family tableR P ciphersR _ _ hr hPR)
  exact ForkSlope.fork_masked_slope xi p encode randomCount enough V hmid hencoding hlinesEnc saltL saltR auxL auxR
    piopL piopR decL decR family P (ciphersL ++ ciphersR) left right hl' hr' hlines hfree e hne

end
end SDitH.Proofs.ForkSlopePrefix
