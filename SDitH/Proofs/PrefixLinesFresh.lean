import SDitH.Proofs.CommitSplitRun
import SDitH.Proofs.ThreeHashShape
import SDitH.Proofs.StoredLinesMention
import SDitH.Proofs.HashCipherTrace

/-! The lines input is fresh after the prefix unless a mention event. The
prefix's last three queries (outer, auxiliary, mask) run from the head's
result; when they are fresh, the result's trace is the three entries over
the head's trace, its state carries the three answers, and the table
traces its stored inputs. A lines input of the auxiliary answer stored at
that point differs from the mask input and the auxiliary query, so its
entry is older and mentions the auxiliary answer: the charged mention
event. Hence under its negation the lines input is absent, whatever the
witness. -/

namespace SDitH.Proofs.PrefixLinesFresh

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCHashChain Spec.HashCipherProgram Spec.SharedSigner
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind ThreeHashShape StoredLinesMention LinesMention QueryPrefixes
open scoped Classical

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The head's data: tree nodes, leaf commitments and row hashes. -/
abbrev HeadData (lambda tau kappa : Nat) :=
  (Nat → Seed lambda) × (Fin tau × Fin (2 ^ kappa) → Digest lambda) × (Fin tau → Digest lambda)

/-- The prefix's last three queries from the head's data. -/
def prefixTail {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (S : SignerSetting F lambda tau kappa s wit rnd)
    (salt : Bits lambda) (head : HeadData lambda tau kappa) :
    SignerProgram lambda s wit rnd (PrefixData lambda tau kappa s wit rnd) :=
  let nodes := head.1
  let commits := head.2.1
  let rowHashes := head.2.2
  Program.hash (outerString salt rowHashes) fun outer =>
    Program.hash (Spec.BLCHashChain.auxQuery outer.1 (Spec.BLCHashChain.sourceTail S.encoding
        (Spec.BLCCommit.positiveCorrections (Spec.BLC.correction Spec.GrayCode.grayFieldRow
          (Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)))))
      fun auxiliary =>
      Program.hash (maskInput auxiliary.1) fun maskAnswer =>
        Program.done (nodes, commits, rowHashes, outer, auxiliary, maskAnswer)

/-- The auxiliary query input of the head's data at an outer answer. -/
def auxInputOf {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (S : SignerSetting F lambda tau kappa s wit rnd)
    (salt : Bits lambda) (head : HeadData lambda tau kappa) (outer : Out lambda s wit rnd) : List Bool :=
  Spec.BLCHashChain.auxQuery outer.1 (Spec.BLCHashChain.sourceTail S.encoding
    (Spec.BLCCommit.positiveCorrections (Spec.BLC.correction Spec.GrayCode.grayFieldRow
      (Spec.BLCCommit.randomTable S.p salt (fun e i => head.1 (leafNode e i).val) S.randomCount S.enough))))

/-- After the prefix's last three fresh queries, a stored lines input of the
auxiliary answer raises the mention event. -/
theorem prefixTail_lines_mention {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (head : HeadData lambda tau kappa)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (t0 : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Entry (List Bool) (Out lambda s wit rnd)))
    (htraced : Traced t0 log) (hord : Ordered log) (hfresh : Fresh log) (hext : ∀ entry ∈ log, Extends entry.before t0)
    (hstored : ∀ entry ∈ log, t0 entry.input = some entry.answer)
    (h0 : t0 (outerString salt head.2.2) = none)
    (h1 : ∀ o, @Function.update (List Bool) (fun _ => Option (Out lambda s wit rnd))
      (fun a b => Classical.propDecidable (a = b)) t0 (outerString salt head.2.2) (some o) (auxInputOf S salt head o) = none)
    (h2 : ∀ o a, @Function.update (List Bool) (fun _ => Option (Out lambda s wit rnd))
      (fun a b => Classical.propDecidable (a = b))
      (@Function.update (List Bool) (fun _ => Option (Out lambda s wit rnd)) (fun a b => Classical.propDecidable (a = b))
        t0 (outerString salt head.2.2) (some o)) (auxInputOf S salt head o) (some a) (maskInput a.1) = none)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd)))
    (hout : out ∈ (runFixed procedure family 3 (prefixTail S salt head) t0 hashes ciphers log).support) :
    ∃ o a m : Out lambda s wit rnd, out.state = .done (head.1, head.2.1, head.2.2, o, a, m) ∧
      ∀ (tail : List Bool) (d : Out lambda s wit rnd), out.hashTable (linesQuery a.1 tail) = some d →
        prefixBad (digestMention (mentions lambda tau)) out.trace = true := by
  obtain ⟨o, a, m, hstate, htable, htrace⟩ := three_hash_support family (outerString salt head.2.2)
    (auxInputOf S salt head) (fun _ a => maskInput a.1) (fun o a m => (head.1, head.2.1, head.2.2, o, a, m)) t0 hashes
    ciphers log h0 h1 h2 out hout
  obtain ⟨htr, _, _, _, _, _⟩ := HashCipherTrace.run_invariants procedure family 3 (prefixTail S salt head) t0 hashes ciphers
    log out hout htraced hord hfresh hext hstored
  refine ⟨o, a, m, hstate, fun tail d hd => ?_⟩
  rw [htrace] at htr ⊢
  exact prefixBad_of_stored (mentions lambda tau) out.hashTable _ _ _ htr (linesQuery a.1 tail) d hd
    (linesQuery_ne_maskInput a.1 a.1 tail) (linesQuery_ne_auxQuery a.1 o.1 tail _)
    (auxiliary_mem_mentions_lines a.1 tail)

end
end SDitH.Proofs.PrefixLinesFresh
