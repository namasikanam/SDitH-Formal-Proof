import SDitH.Proofs.PrefixHeadSplit

/-! The lines input after a whole prefix run. The prefix's run is the head's
run continued by the last three queries; a continuation result at a
finished head state is a run of the three queries from the head's result
with the collision flag combined, so its state, table and trace are those
of that run. With the head's run invariants (from the starting world's) and
the three queries fresh at the head's result, a stored lines input of the
auxiliary answer raises the mention event. -/

namespace SDitH.Proofs.PrefixLinesFreshRun

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCHashChain Spec.HashCipherProgram Spec.SharedSigner
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind PrefixLinesFresh PrefixHeadSplit CommitSplitRun
open scoped Classical

noncomputable section

variable {Input Digest Key Block A B : Type*} [Fintype Digest] [Nonempty Digest]

/-- A continuation result at a finished state is a run of the continuation
from that state's result, with the collision flag combined. -/
theorem continueRun_done_support (family : Spec.IdealCipher.Family Key Block) (m : Nat)
    (f : A → Program Input Digest Key Block B) (mid : Result Input Digest Key Block (Program Input Digest Key Block A))
    (v : A) (hmid : mid.state = .done v) (out : Result Input Digest Key Block (Program Input Digest Key Block B))
    (hout : out ∈ (continueRun family m f mid).support) :
    ∃ out' ∈ (runFixed procedure family m (f v) mid.hashTable mid.hashHistory mid.cipherHistory mid.trace).support,
      out.state = out'.state ∧ out.hashTable = out'.hashTable ∧ out.trace = out'.trace := by
  unfold continueRun at hout
  rw [hmid] at hout
  obtain ⟨out', hout', heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  subst heq
  exact ⟨out', hout', rfl, rfl, rfl⟩

variable {lambda tau kappa s wit rnd : Nat}

/-- After the prefix's last three fresh queries from a head result with the
run invariants, a stored lines input of the auxiliary answer raises the
mention event. -/
theorem prefix_lines_mention {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (mid : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (head : HeadData lambda tau kappa) (hmid : mid.state = .done head)
    (htraced : Traced mid.hashTable mid.trace) (hord : Ordered mid.trace) (hfresh : Fresh mid.trace)
    (hext : ∀ entry ∈ mid.trace, Extends entry.before mid.hashTable)
    (hstored : ∀ entry ∈ mid.trace, mid.hashTable entry.input = some entry.answer)
    (h0 : mid.hashTable (outerString salt head.2.2) = none)
    (h1 : ∀ o, @Function.update (List Bool) (fun _ => Option (Out lambda s wit rnd))
      (fun a b => Classical.propDecidable (a = b)) mid.hashTable (outerString salt head.2.2) (some o)
      (auxInputOf S salt head o) = none)
    (h2 : ∀ o a, @Function.update (List Bool) (fun _ => Option (Out lambda s wit rnd))
      (fun a b => Classical.propDecidable (a = b))
      (@Function.update (List Bool) (fun _ => Option (Out lambda s wit rnd)) (fun a b => Classical.propDecidable (a = b))
        mid.hashTable (outerString salt head.2.2) (some o)) (auxInputOf S salt head o) (some a) (maskInput a.1) = none)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd)))
    (hout : out ∈ (continueRun family 3 (prefixTail S salt) mid).support) :
    ∃ o a m : Out lambda s wit rnd, out.state = .done (head.1, head.2.1, head.2.2, o, a, m) ∧
      ∀ (tail : List Bool) (d : Out lambda s wit rnd), out.hashTable (linesQuery a.1 tail) = some d →
        prefixBad (digestMention (mentions lambda tau)) out.trace = true := by
  obtain ⟨out', hout', hstate, htable, htrace⟩ := continueRun_done_support family 3 (prefixTail S salt) mid head hmid out hout
  obtain ⟨o, a, m, hstate', hmention⟩ := prefixTail_lines_mention S salt head family mid.hashTable mid.hashHistory
    mid.cipherHistory mid.trace htraced hord hfresh hext hstored h0 h1 h2 out' hout'
  refine ⟨o, a, m, hstate.trans hstate', fun tail d hd => ?_⟩
  rw [htrace]
  exact hmention tail d (htable ▸ hd)

end
end SDitH.Proofs.PrefixLinesFreshRun
