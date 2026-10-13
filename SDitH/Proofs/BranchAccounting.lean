import SDitH.Proofs.VisitedInputs
import SDitH.Proofs.ForkCut
import SDitH.Proofs.ForkCutRun

/-! One branch of a fork, accounted. On a well-formed branch table cut at
the fork table, an accepting candidate-middle verification whose lines
value is the fork point's fixed target visits only inputs present in the
fork table, unless a named event occurred: a fresh post-fork digest equal
to the target, a fresh digest equal to a mentioned value, or the mask
input of the forgery's auxiliary digest absent from the fork table. The
first two are charged by the trace bounds; the third is the recorded
open question of the mask's position across the fork. -/

namespace SDitH.Proofs.BranchAccounting

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.OracleChain Spec.RandomOracleTrace
open Spec.RandomOracleMention Spec.ProductOracle Spec.HashCipherEvaluation Spec.SharedScheme Spec.CandidateVerifier
open Spec.BAVCReconstructionProgram (primitives)
open Spec.SlopeConsistencyGame (Out)
open ForkSlopePrefix (hashInputs)
open ForkCut (Cut linesString)
open ForkCutRun (targetBad)
open scoped Classical
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- A mask input read by the branch and absent from the fork table. -/
def MaskAfterCut (P table : List Bool → Option (Out lambda s wit rnd)) : Prop :=
  ∃ auxiliary : Digest lambda, (∃ pair, table (maskInput auxiliary) = some pair) ∧ P (maskInput auxiliary) = none

theorem branch_visited_or_event {F : Type*} [Field F] [Algebra (ZMod 2) F] (hlambda : 0 < lambda) (htau : 0 < tau)
    (xi : F) (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (V : VerifierSetting F lambda tau kappa s wit rnd)
    (hmid : V.middle = candidateMiddle xi p V.nodes encode randomCount enough)
    (salt : Bits lambda) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (piop : Digest lambda)
    (decomposition : Spec.BLCRetry.Counter × Opening lambda tau)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table P : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Entry (List Bool) (Out lambda s wit rnd)))
    (hord : Ordered log) (hfresh : Fresh log) (htraced : Traced table log) (hcut : Cut P log) (hPT : Extends P table)
    (left : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (hl : Evaluates family table ciphers (verifyProgram V salt aux piop decomposition) (Except.ok left))
    (target : Digest lambda) (htarget : left.lines = target) :
    (∀ x ∈ hashInputs family table (verifyProgram V salt aux piop decomposition), (P x).isSome) ∨
      traceBad (targetBad P target) log = true ∨
      prefixBad (digestMention (mentions lambda tau)) log = true ∨
      MaskAfterCut P table := by
  obtain ⟨recon, rows, pa, pl, value, hrecon, _, hhashes, hobserved, hpa, hmiddle, hpl, hleft, hvisited⟩ :=
    VisitedInputs.verify_visited V salt aux piop decomposition family table ciphers left hl
  set prim := primitives (tau := tau) (N := 2 ^ kappa) V.layout V.variant family (SharedSchemeChain.projected table) with hprim
  set commits := Spec.BAVCBinding.rowCommitments rows.leaves with hcommits
  have hwith : Spec.BAVCBindingROM.withTable prim (SharedSchemeChain.projected table) = prim := rfl
  -- The lines string: in the fork table or the fixed-target event.
  have hlinesT : table (linesString pa.1 (V.encoding.vector aux.plain ++ V.encoding.base value.2.2.2)) = some pl := hpl
  have hpl1 : pl.1 = target := by
    rw [← htarget, hleft]
  rcases ForkCutRun.present_or_target P table log hcut htraced target _ pl hlinesT hpl1 with hlinesP | hbad
  swap
  · exact Or.inr (Or.inl hbad)
  -- The chain strings: in the fork table or the mention event.
  have hrows : ∀ e, ∃ pair, table (rowString (commits e)) = some pair ∧
      pair.1 = prim.hash (Spec.BAVCBinding.rowQuery commits e) := by
    intro e
    have hlook := BAVCBindingROM.observed_lookup prim _ salt commits hobserved _
      (BAVCBinding.rowQuery_mem prim salt commits e)
    rw [hwith] at hlook
    obtain ⟨pair, hpair, hd⟩ := Option.map_eq_some_iff.mp hlook
    exact ⟨pair, hpair, hd⟩
  have houter : ∃ pair, table (outerString salt fun e => prim.hash (Spec.BAVCBinding.rowQuery commits e)) = some pair ∧
      pair.1 = recon.hcom := by
    have hlook := BAVCBindingROM.observed_lookup prim _ salt commits hobserved _
      (BAVCBinding.outerQuery_mem prim salt commits)
    rw [hwith] at hlook
    obtain ⟨pair, hpair, hd⟩ := Option.map_eq_some_iff.mp hlook
    refine ⟨pair, hpair, ?_⟩
    rw [hd, hhashes]
    rfl
  have haux : ∃ pair, table (auxString recon.hcom (Spec.BLCHashChain.sourceTail V.encoding aux.corrections)) = some pair ∧
      pair.1 = pa.1 := ⟨pa, hpa, rfl⟩
  rcases ForkCut.verification_chain_at_cut hlambda htau (Nat.two_pow_pos kappa) log table P hord hfresh
    htraced hcut hPT salt commits (fun e => prim.hash (Spec.BAVCBinding.rowQuery commits e)) recon.hcom _ pa.1 _
    hrows houter haux hlinesP with ⟨hrowsP, houterP, hauxP⟩ | hbad
  swap
  · exact Or.inr (Or.inr (Or.inl hbad))
  -- The mask input: in the fork table or the mask event.
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

end
end SDitH.Proofs.BranchAccounting
