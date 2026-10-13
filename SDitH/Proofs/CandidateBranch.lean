import SDitH.Proofs.CandidateForkSlope
import SDitH.Proofs.BranchAccounting
import SDitH.Proofs.ForkSlopePrefix

/-! Branch accounting and the prefix restriction for the candidate scheme.
On a well-formed branch table cut at the fork table, an accepting
candidate verification whose lines value is the fixed target visits only
inputs present in the fork table, unless the fixed-target, mention or
mask event occurred; and two such verifications on tables extending the
fork table give the uniform slope data on the fork table with the union
of the two histories. -/

namespace SDitH.Proofs.CandidateBranch

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.OracleChain Spec.RandomOracleTrace
open Spec.RandomOracleMention Spec.ProductOracle Spec.HashCipherEvaluation Spec.SharedScheme Spec.CandidateVerifier
open Spec.CandidateScheme Spec.CandidateBAVC Spec.SlopeConsistency Spec.BLCSeedLines
open Spec.SlopeConsistencyGame (Out)
open ForkSlopePrefix (hashInputs)
open ForkCut (Cut linesString)
open ForkCutRun (targetBad)
open BranchAccounting (MaskAfterCut)
open CandidateBAVC (leafValue induced)
open CandidateForkSlope (completion)
open SharedSigner (expandEntries)
open scoped Classical
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- One branch of a candidate fork, accounted. -/
theorem branch_visited_or_event {F : Type*} [Field F] [Algebra (ZMod 2) F] (hlambda : 0 < lambda) (htau : 0 < tau)
    (xi : F) (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (V : VerifierSetting F lambda tau kappa s wit rnd)
    (hmid : V.middle = candidateMiddle xi p V.nodes encode randomCount enough)
    (salt : Bits lambda) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (piop : Digest lambda)
    (decomposition : Spec.BLCRetry.Counter × Opening lambda tau (2 ^ kappa))
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table P : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Entry (List Bool) (Out lambda s wit rnd)))
    (hord : Ordered log) (hfresh : Fresh log) (htraced : Traced table log) (hcut : Cut P log) (hPT : Extends P table)
    (left : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (hl : Evaluates family table ciphers (Spec.CandidateScheme.verifyProgram V salt aux piop decomposition) (Except.ok left))
    (target : Digest lambda) (htarget : left.lines = target) :
    (∀ x ∈ hashInputs family table (Spec.CandidateScheme.verifyProgram V salt aux piop decomposition), (P x).isSome) ∨
      traceBad (targetBad P target) log = true ∨
      prefixBad (digestMention (mentions lambda tau)) log = true ∨
      MaskAfterCut P table := by
  obtain ⟨recon, pa, pl, value, hrecon, hpa, hmiddle, hpl, hleft, hvisited⟩ :=
    CandidateSchemeChain.verify_visited family table ciphers V salt aux piop decomposition left hl
  obtain ⟨_, hhcom, hrows, houter, _, _⟩ :=
    CandidateBAVC.reconstruct_evaluates family table ciphers V.layout V.variant salt _ decomposition.2 recon hrecon
  set prim := induced (tau := tau) (kappa := kappa) family table V.layout V.variant with hprim
  set commits := commitsOf (leafValue family V.layout V.variant salt (V.expand piop decomposition.1) decomposition.2)
    with hcommits
  have hlinesT : table (linesString pa.1 (V.encoding.vector aux.plain ++ V.encoding.base value.2.2.2)) = some pl := hpl
  have hpl1 : pl.1 = target := by
    rw [← htarget, hleft]
  rcases ForkCutRun.present_or_target P table log hcut htraced target _ pl hlinesT hpl1 with hlinesP | hbad
  swap
  · exact Or.inr (Or.inl hbad)
  have hrows' : ∀ e, ∃ pair, table (rowString (commits e)) = some pair ∧
      pair.1 = prim.hash (Spec.BAVCBinding.rowQuery commits e) := hrows
  have houter' : ∃ pair, table (outerString salt fun e => prim.hash (Spec.BAVCBinding.rowQuery commits e)) = some pair ∧
      pair.1 = recon.hcom := houter
  have haux : ∃ pair, table (auxString recon.hcom (Spec.BLCHashChain.sourceTail V.encoding aux.corrections)) = some pair ∧
      pair.1 = pa.1 := ⟨pa, hpa, rfl⟩
  rcases ForkCut.verification_chain_at_cut hlambda htau (Nat.two_pow_pos kappa) log table P hord hfresh
    htraced hcut hPT salt commits (fun e => prim.hash (Spec.BAVCBinding.rowQuery commits e)) recon.hcom _ pa.1 _
    hrows' houter' haux hlinesP with ⟨hrowsP, houterP, hauxP⟩ | hbad
  swap
  · exact Or.inr (Or.inr (Or.inl hbad))
  cases hmask : P (maskInput pa.1) with
  | none =>
    refine Or.inr (Or.inr (Or.inr ⟨pa.1, ?_, hmask⟩))
    rw [hmid] at hmiddle
    unfold candidateMiddle at hmiddle
    cases hmiddle with
    | hash _ _ answer _ stored _ => exact ⟨answer, stored⟩
  | some _ =>
    left
    intro x hx
    rcases hvisited x hx with hx | rfl | hx | rfl
    · simp only [Spec.BAVCBinding.hashQueries, List.mem_append, List.mem_ofFn, List.mem_singleton] at hx
      rcases hx with ⟨e, rfl⟩ | rfl
      · exact hrowsP e
      · exact houterP
    · exact hauxP
    · rw [hmid, VisitedInputs.candidateMiddle_visited, List.mem_singleton] at hx
      subst hx
      rw [hmask]
      rfl
    · exact hlinesP

/-- The uniform slope data of a candidate fork on a table. -/
def UniformSlope {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (V : VerifierSetting F lambda tau kappa s wit rnd)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (P : List Bool → Option (Out lambda s wit rnd))
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) (saltL saltR : Bits lambda)
    (auxL auxR : Spec.BLCCommit.Auxiliary tau s wit rnd) (piopL piopR : Digest lambda)
    (decL decR : Spec.BLCRetry.Counter × Opening lambda tau (2 ^ kappa)) : Prop :=
  ∃ (reconL reconR : Reconstructed lambda tau (2 ^ kappa)) (auxD : Digest lambda) (pm : Out lambda s wit rnd),
    saltL = saltR ∧ auxL.corrections = auxR.corrections ∧ auxL.plain = auxR.plain ∧
    Evaluates family P ciphers
      (Spec.CandidateBAVC.reconstruct V.layout V.variant saltL (V.expand piopL decL.1) decL.2) (Except.ok reconL) ∧
    Evaluates family P ciphers
      (Spec.CandidateBAVC.reconstruct V.layout V.variant saltR (V.expand piopR decR.1) decR.2) (Except.ok reconR) ∧
    P (maskInput auxD) = some pm ∧
    (∃ pa, P (Spec.BLCHashChain.auxQuery reconL.hcom (Spec.BLCHashChain.sourceTail V.encoding auxL.corrections)) =
      some pa ∧ pa.1 = auxD) ∧
    commitsOf (leafValue family V.layout V.variant saltL (V.expand piopL decL.1) decL.2) =
      commitsOf (leafValue family V.layout V.variant saltR (V.expand piopR decR.1) decR.2) ∧
    ∀ e : Fin tau, V.expand piopL decL.1 e ≠ V.expand piopR decR.1 e →
      (∃ (i : Fin (2 ^ kappa)) (ls rs : Seed lambda),
          Spec.BAVCBinding.IsSeedCollision (induced (tau := tau) (kappa := kappa) family P V.layout V.variant) saltL
            (Spec.SeedTree.leafOffset e i) ls rs ∧
          expandEntries family ciphers V.layout V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) ls ∧
          expandEntries family ciphers V.layout V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) rs) ∨
        (completion (V.expand piopL decL.1) decL.2 decR.2 e = completion (V.expand piopR decR.1) decR.2 decL.2 e ∧
          ∀ a, maskedSlope p saltL (completion (V.expand piopL decL.1) decL.2 decR.2) randomCount enough auxL pm.2 e a =
            auxL.plain a)

/-- The prefix restriction with uniform data, for the candidate scheme. -/
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
    (decL decR : Spec.BLCRetry.Counter × Opening lambda tau (2 ^ kappa))
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (P tableL tableR : List Bool → Option (Out lambda s wit rnd))
    (hextL : ∀ x y, P x = some y → tableL x = some y) (hextR : ∀ x y, P x = some y → tableR x = some y)
    (ciphersL ciphersR : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (left right : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (hl : Evaluates family tableL ciphersL (Spec.CandidateScheme.verifyProgram V saltL auxL piopL decL) (Except.ok left))
    (hr : Evaluates family tableR ciphersR (Spec.CandidateScheme.verifyProgram V saltR auxR piopR decR) (Except.ok right))
    (hinL : ∀ x ∈ hashInputs family tableL (Spec.CandidateScheme.verifyProgram V saltL auxL piopL decL), (P x).isSome)
    (hinR : ∀ x ∈ hashInputs family tableR (Spec.CandidateScheme.verifyProgram V saltR auxR piopR decR), (P x).isSome)
    (hlines : left.lines = right.lines) (hfree : DigestCollisionFree P) :
    UniformSlope p randomCount enough V family P (ciphersL ++ ciphersR) saltL saltR auxL auxR piopL piopR decL decR := by
  have hPL : ∀ x ∈ hashInputs family tableL (Spec.CandidateScheme.verifyProgram V saltL auxL piopL decL), P x = tableL x := by
    intro x hx
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hinL x hx)
    rw [hy, hextL x y hy]
  have hPR : ∀ x ∈ hashInputs family tableR (Spec.CandidateScheme.verifyProgram V saltR auxR piopR decR), P x = tableR x := by
    intro x hx
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hinR x hx)
    rw [hy, hextR x y hy]
  have hl' := ForkSlopePrefix.evaluates_mono_ciphers family P ciphersL (ciphersL ++ ciphersR)
    (fun e he => List.mem_append_left _ he) _ _ (ForkSlopePrefix.evaluates_restrict family tableL P ciphersL _ _ hl hPL)
  have hr' := ForkSlopePrefix.evaluates_mono_ciphers family P ciphersR (ciphersL ++ ciphersR)
    (fun e he => List.mem_append_right _ he) _ _ (ForkSlopePrefix.evaluates_restrict family tableR P ciphersR _ _ hr hPR)
  exact CandidateForkSlope.fork_masked_slope xi p encode randomCount enough V hmid hencoding hlinesEnc saltL saltR
    auxL auxR piopL piopR decL decR family P (ciphersL ++ ciphersR) left right hl' hr' hlines hfree

end
end SDitH.Proofs.CandidateBranch
