import SDitH.Proofs.RowStoredCount
import SDitH.Proofs.HashCipherTrace
import SDitH.Proofs.SharedResample

/-! The row-stored event after the last call, under the posterior family at
the split. From the split point's result (finished with the data before
the last call, its table traced by its trace), the fixed set is the trace's
inputs with the other executions' row queries, which do not depend on the
last block; the run after the last call under a family drawn from the
posterior of the split point's history has the row-stored event only when
the last execution's row query lies in that set; so, unless the last call
is stale in the split point's history, the event's probability is at most
the fiber bound times the set's size over the remaining block count. -/

namespace SDitH.Proofs.RowStoredAfter

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.RandomOracleTrace Spec.RandomOracleTrap
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open IdealCipherFresh HeadCommitSplit RowsSupport RowStoredReduce RowStoredCount CommitLinesEvents OuterFresh
open PrefixLinesFresh CipherResample PosteriorFresh RunBind
open scoped Classical ENNReal

noncomputable section

section Generic

variable {A : Type*}

/-- A map's truth is monotone in the map on the support. -/
theorem map_true_mono (p : PMF A) (g g' : A → Bool) (h : ∀ a ∈ p.support, g a = true → g' a = true) :
    (p.map g) true ≤ (p.map g') true := by
  rw [RandomOracleTrap.map_true_eq, RandomOracleTrap.map_true_eq]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · refine mul_le_mul' le_rfl ?_
    cases hg : g a
    · simp [indicator]
    · rw [h a ha hg]
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

/-- A constant map's truth is the indicator. -/
theorem map_const_true (p : PMF A) (b : Bool) : (p.map fun _ => b) true = indicator b := by
  rw [RandomOracleTrap.map_true_eq, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- A map's truth is at most the indicator of a condition implied by its
truth on the support. -/
theorem map_true_le_indicator (p : PMF A) (g : A → Bool) (P : Prop) (h : ∀ a ∈ p.support, g a = true → P) :
    (p.map g) true ≤ indicator (decide P) := by
  rw [← map_const_true p (decide P)]
  exact map_true_mono p g (fun _ => decide P) fun a ha hg => decide_eq_true (h a ha hg)

/-- Binds are pointwise monotone at a value. -/
theorem bind_true_le_bind_true (p : PMF A) (f g : A → PMF Bool) (h : ∀ a ∈ p.support, (f a) true ≤ (g a) true) :
    (p.bind f) true ≤ (p.bind g) true := by
  have hc := PrefixFromHead.bind_le_bind_add_cost p f g (fun _ => 0) true (fun a ha => by simpa using h a ha)
  simpa using hc

end Generic

variable {lambda tau kappa s wit rnd : Nat}

/-- The last call is stale in a history: the history has its key and input. -/
def stale {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (v : BeforeData lambda tau kappa)
    (history : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) : Bool :=
  decide (∃ e ∈ history, e.key = lastKey (kappa := kappa) S.layout htau v.1 ∧
    e.input = S.layout.input (cipherInput S.variant salt (lastAddress (kappa := kappa) htau) true))

/-- The fixed set: the trace's inputs and the other executions' row queries. -/
def fixedSet (v : BeforeData lambda tau kappa)
    (trace : List (Entry (List Bool) (Out lambda s wit rnd))) : Finset (List Bool) :=
  (trace.map Entry.input).toFinset ∪
    ((List.finRange tau).dropLast.map fun e => Spec.BAVCBinding.rowQuery (fun e i => v.2.1 (e, i)) e).toFinset

theorem fixedSet_card_le (v : BeforeData lambda tau kappa)
    (trace : List (Entry (List Bool) (Out lambda s wit rnd))) :
    (fixedSet v trace).card ≤ trace.length + tau := by
  unfold fixedSet
  refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
  · exact (List.toFinset_card_le _).trans (by rw [List.length_map])
  · refine (List.toFinset_card_le _).trans ?_
    simp only [List.length_map, List.length_dropLast, List.length_finRange]
    omega

/-- The other executions' row queries do not depend on the last block. -/
theorem rowQuery_other (htau : tau ≠ 0) (v : BeforeData lambda tau kappa) (b : Bits lambda) (e : Fin tau)
    (he : e ≠ lastIndex htau) :
    Spec.BAVCBinding.rowQuery (fun e i => commitsWith htau v b (e, i)) e =
      Spec.BAVCBinding.rowQuery (fun e i => v.2.1 (e, i)) e := by
  unfold Spec.BAVCBinding.rowQuery
  congr 1
  unfold Spec.BAVC.serializeArray
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  unfold commitsWith
  have hne : (e, i) ≠ lastPair (kappa := kappa) htau := by
    intro h
    exact he (by rw [← lastPair_fst htau, ← h])
  simp [Function.update, hne]

/-- The row-stored event after the last call lies in the fixed set. -/
theorem rowStored_mem {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (v : BeforeData lambda tau kappa)
    (family : Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Entry (List Bool) (Out lambda s wit rnd))) (htraced : Traced table log)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (hout : out ∈ (runFixed procedure family tau (headAfter htau S salt v) table hashes ciphers log).support)
    (hrow : rowStored htau out = true) :
    lastRowQuery htau v (lastBlock htau S salt v family) ∈ fixedSet v log := by
  rcases rowStored_reduce htau S salt v family table hashes ciphers log out hout hrow with h | ⟨e, he, heq⟩
  · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp h
    obtain ⟨entry, hentry, hinput, -⟩ := htraced.1 _ answer hanswer
    unfold fixedSet
    refine Finset.mem_union_left _ ?_
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨entry, hentry, hinput⟩
  · have hne : e ≠ lastIndex htau := by
      intro h
      have hnil : List.finRange tau ≠ [] := List.ne_nil_of_length_pos (by rw [List.length_finRange]; omega)
      have hnd : (List.finRange tau).Nodup := List.nodup_finRange tau
      rw [← List.dropLast_append_getLast hnil] at hnd
      exact List.disjoint_of_nodup_append hnd he (List.mem_singleton.mpr h)
    unfold fixedSet
    refine Finset.mem_union_right _ ?_
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨e, he, by rw [← rowQuery_other htau v _ e hne, heq]⟩

end
end SDitH.Proofs.RowStoredAfter
