import SDitH.Proofs.HeadLastSplit
import SDitH.Proofs.PrefixLinesFreshRun

/-! The head's run split at its last row query, and the outer input's
freshness after it. The head's initial part is bounded by the head budget
less one and the last row query by one, so the head's traced run is the
initial part's run continued by the last row query's run; a fresh last row
query's run result has the newest trace entry at that query with its
answer recorded as the last row hash, so a stored outer string over the
recorded row hashes raises the mention event. -/

namespace SDitH.Proofs.HeadLastRun

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind PrefixLinesFresh PrefixHeadSplit CollectLast OuterFresh ThreeHashRun ThreeHashShape
open HeadLastSplit PrefixLinesFreshRun
open scoped Classical

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The initial part's budget: the head budget less the last row query. -/
theorem headBudget_eq (htau : tau ≠ 0) : headBudget tau kappa = (headBudget tau kappa - 1) + 1 := by
  unfold headBudget
  omega

theorem headInit_bounded {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) :
    Bounded (headBudget tau kappa - 1) (headInit S salt root) := by
  unfold headInit headBudget
  refine HashCipherProgram.bounded_mono _ _ _ (by omega)
    (HashCipherProgram.bounded_bind _ _ (2 * (tau * 2 ^ kappa - 1))
      (2 * (Spec.SharedSlopeExec.allPairs tau kappa).length + (tau - 1))
      (SharedSigner.treeThrough_bounded S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) fun nodes => ?_)
  refine HashCipherProgram.bounded_mono _ _ _ (by rw [Nat.mul_comm])
    (HashCipherProgram.bounded_bind _ _ ((Spec.SharedSlopeExec.allPairs tau kappa).length * 2) (tau - 1)
      (SharedSigner.collect_bounded _ 2 (fun pair => SharedSigner.commitCall_bounded S.layout _ S.variant salt _ _) _ _)
      fun commits => ?_)
  refine HashCipherProgram.bounded_mono _ _ _ (by simp [List.length_dropLast, List.length_finRange])
    (HashCipherProgram.bounded_bind _ _ ((List.finRange tau).dropLast.length * 1) 0
      (SharedSigner.collect_bounded _ 1 (fun e => SharedSigner.hashCall_bounded _) _ _) fun partialRows => ?_)
  trivial

theorem lastRow_bounded (htau : tau ≠ 0) (data : HeadData lambda tau kappa) :
    Bounded 1 (lastRow (s := s) (wit := wit) (rnd := rnd) htau data) := by
  intro _
  trivial

/-- The head's traced run is the initial part's run continued by the last
row query's run. -/
theorem runFixed_head_split {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure family (headBudget tau kappa) (prefixHead S salt root) table hashes ciphers log =
      (runFixed procedure family (headBudget tau kappa - 1) (headInit S salt root) table hashes ciphers log).bind
        (continueRun family 1 (lastRow htau)) := by
  rw [headBudget_eq htau, prefixHead_eq_last htau]
  rw [show headBudget tau kappa - 1 + 1 - 1 = headBudget tau kappa - 1 by omega]
  exact runFixed_bind family (headBudget tau kappa - 1) 1 (headInit S salt root) (lastRow htau)
    (headInit_bounded htau S salt root) (lastRow_bounded htau) table hashes ciphers log

/-- A fresh last row query's run result: the newest trace entry is that query
with its answer recorded as the last row hash. -/
theorem lastRow_shape (htau : tau ≠ 0) (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (mid : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (data : HeadData lambda tau kappa) (hmid : mid.state = .done data)
    (hfresh : mid.hashTable (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)) = none)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (hout : out ∈ (continueRun family 1 (lastRow htau) mid).support) :
    ∃ a : Out lambda s wit rnd,
      out.state = .done (data.1, data.2.1, Function.update data.2.2 (lastIndex htau) a.1) ∧
      out.trace = ⟨mid.hashTable, Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau), a⟩ :: mid.trace ∧
      out.hashTable = Function.update mid.hashTable
        (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)) (some a) := by
  obtain ⟨out', hout', hstate, htable, htrace⟩ := continueRun_done_support family 1 (lastRow htau) mid data hmid out hout
  obtain ⟨a, out'', hout'', heq⟩ := runFixed_hash_fresh_support family 0 _ _ mid.hashTable mid.hashHistory mid.cipherHistory
    mid.trace hfresh out' hout'
  have h0 := runFixed_zero_support family _ _ _ _ _ out'' hout''
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [hstate, heq, (mark_fields _ _).1, h0]
  · rw [htrace, heq, (mark_fields _ _).2.2.2.2, h0]
  · rw [htable, heq, (mark_fields _ _).2.1, h0]
    dsimp only
    congr 1
    funext x y
    exact Subsingleton.elim _ _

/-- After a fresh last row query with the traced invariant, a stored outer
string over the recorded row hashes raises the mention event. -/
theorem outer_mention_after_head (hl : 0 < lambda) (htau : tau ≠ 0)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (mid : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (data : HeadData lambda tau kappa) (hmid : mid.state = .done data)
    (hfresh : mid.hashTable (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)) = none)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (hout : out ∈ (continueRun family 1 (lastRow htau) mid).support) (htraced : Traced out.hashTable out.trace)
    (salt : Seed lambda) :
    ∃ a : Out lambda s wit rnd,
      out.state = .done (data.1, data.2.1, Function.update data.2.2 (lastIndex htau) a.1) ∧
      ∀ d : Out lambda s wit rnd,
        out.hashTable (outerString salt (Function.update data.2.2 (lastIndex htau) a.1)) = some d →
          prefixBad (digestMention (mentions lambda tau)) out.trace = true := by
  obtain ⟨a, hstate, htrace, _⟩ := lastRow_shape htau family mid data hmid hfresh out hout
  refine ⟨a, hstate, fun d hd => ?_⟩
  rw [htrace] at htraced ⊢
  exact outer_stored_mention hl out.hashTable _ _ htraced (fun e i => data.2.1 (e, i)) (lastIndex htau) rfl salt _
    (by simp) d hd

end
end SDitH.Proofs.HeadLastRun
