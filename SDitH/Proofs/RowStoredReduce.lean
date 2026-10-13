import SDitH.Proofs.RowsSupport
import SDitH.Proofs.CommitLinesEvents
import SDitH.Proofs.BAVCBinding
import SDitH.Proofs.SeedPrimitives

/-! The row-stored event reduced to the last commitment block. The last
leaf pair lies in the last execution; after the run following the last
call, the commitments are those before with the last completed by the
last call's output, and the row-stored event says the last execution's
row query is defined in the starting table or equals one of the other
executions' row queries. The last execution's row query is injective in
the last block, so the event is the last block's membership in a set
fixed before the last call. -/

namespace SDitH.Proofs.RowStoredReduce

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open HeadCommitSplit RowsSupport CommitLinesEvents OuterFresh PrefixLinesFresh
open scoped Classical

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The last leaf pair is the last execution with the last leaf. -/
theorem lastPair_eq (htau : tau ≠ 0) :
    lastPair (kappa := kappa) htau =
      (lastIndex htau, (List.finRange (2 ^ kappa)).getLast
        (List.ne_nil_of_length_pos (by rw [List.length_finRange]; exact Nat.two_pow_pos kappa))) := by
  have hne : List.finRange tau ≠ [] := List.ne_nil_of_length_pos (by rw [List.length_finRange]; omega)
  have hne' : List.finRange (2 ^ kappa) ≠ [] :=
    List.ne_nil_of_length_pos (by rw [List.length_finRange]; exact Nat.two_pow_pos kappa)
  have hsplit : Spec.SharedSlopeExec.allPairs tau kappa =
      (List.finRange tau).dropLast.flatMap (fun e => (List.finRange (2 ^ kappa)).map fun i => (e, i)) ++
        (List.finRange (2 ^ kappa)).map fun i => (lastIndex htau, i) := by
    unfold Spec.SharedSlopeExec.allPairs lastIndex
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [List.flatMap_append, List.flatMap_singleton]
  unfold lastPair
  rw [List.getLast_congr _ (by simp [hne']) hsplit, List.getLast_append_of_ne_nil _ (by simp [hne']),
    List.getLast_map]

theorem lastPair_fst (htau : tau ≠ 0) : (lastPair (kappa := kappa) htau).1 = lastIndex htau := by
  rw [lastPair_eq htau]

/-- The last commitment block: the layout's output of the family's answer
to the last call. -/
def lastBlock {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (v : BeforeData lambda tau kappa)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) : Bits lambda :=
  S.layout.output (Spec.IdealCipher.answer family (.encrypt (lastKey (kappa := kappa) S.layout htau v.1)
    (S.layout.input (cipherInput S.variant salt (lastAddress (kappa := kappa) htau) true))))

/-- The commitments completed by a last block. -/
def commitsWith (htau : tau ≠ 0) (v : BeforeData lambda tau kappa) (b : Bits lambda) :
    Fin tau × Fin (2 ^ kappa) → Digest lambda :=
  Function.update v.2.1 (lastPair (kappa := kappa) htau) (concatenate v.2.2 b)

/-- The last execution's row query at a last block. -/
def lastRowQuery (htau : tau ≠ 0) (v : BeforeData lambda tau kappa) (b : Bits lambda) : List Bool :=
  Spec.BAVCBinding.rowQuery (fun e i => commitsWith htau v b (e, i)) (lastIndex htau)

/-- After the run following the last call, the row-stored event says the
last execution's row query is defined in the starting table or equals
another execution's row query. -/
theorem rowStored_reduce {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (v : BeforeData lambda tau kappa)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd)))
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (hout : out ∈ (runFixed procedure family tau (headAfter htau S salt v) table hashes ciphers log).support)
    (hrow : rowStored htau out = true) :
    table (lastRowQuery htau v (lastBlock htau S salt v family)) ≠ none ∨
      ∃ e ∈ (List.finRange tau).dropLast, lastRowQuery htau v (lastBlock htau S salt v family) =
        Spec.BAVCBinding.rowQuery (fun e i => commitsWith htau v (lastBlock htau S salt v family) (e, i)) e := by
  have hout' : out ∈ (runFixed procedure family (tau - 1 + 1) (headAfter htau S salt v) table hashes ciphers log).support := by
    rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero htau)]
  unfold headAfter at hout'
  simp only [runFixed, step_cipher, PMF.pure_bind] at hout'
  simp only [rowStored, decide_eq_true_eq] at hrow
  obtain ⟨data, hstate, hdef⟩ := hrow
  obtain ⟨partialRows, hdata⟩ := runFixed_bind_done family _ _ _ _ _ _ _ out hout' data hstate
  subst hdata
  exact rows_defined family _ _ _ _ _ _ _ _ _ out hout' _ hdef

/-- The last execution's row query is injective in the last block. -/
theorem lastRowQuery_injective (htau : tau ≠ 0) (v : BeforeData lambda tau kappa) :
    Function.Injective (lastRowQuery htau v) := by
  intro b b' h
  unfold lastRowQuery at h
  have hrows := BAVCBinding.rowQuery_injective _ _ _ h
  have hpair := congrFun hrows (lastPair (kappa := kappa) htau).2
  have h1 : ∀ c, commitsWith htau v c (lastIndex htau, (lastPair (kappa := kappa) htau).2) = concatenate v.2.2 c := by
    intro c
    have hp : (lastIndex htau, (lastPair (kappa := kappa) htau).2) = lastPair (kappa := kappa) htau := by
      rw [← lastPair_fst htau]
    unfold commitsWith
    rw [hp, Function.update_self]
  rw [h1, h1] at hpair
  funext j
  have := congrFun hpair ⟨lambda + j.val, by have := j.isLt; omega⟩
  rwa [SeedPrimitives.concatenate_right, SeedPrimitives.concatenate_right] at this

end
end SDitH.Proofs.RowStoredReduce
