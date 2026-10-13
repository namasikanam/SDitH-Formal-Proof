import SDitH.Spec.BAVCChainInputs
import SDitH.Proofs.OracleChain
import SDitH.Proofs.BAVC

/-! Layout facts for the concrete chain strings: lengths, the digest
windows the mention parser extracts, pairwise distinctness of the chain
inputs and the mask input, and the resulting instance of the dependency
chain dichotomy: for every execution, the auxiliary, outer and row strings
are present in the table before the mask input was answered, or a fresh
digest hit a mentioned value. -/

namespace SDitH.Proofs.BAVCChainInputs

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.OracleChain
open Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle
open scoped Classical
noncomputable section

variable {lambda tau N : Nat}

theorem byteBits_length (b : Byte) : (byteBits b).length = 8 := by simp [byteBits]

theorem byteBits_one_ne_two : byteBits 1 ≠ byteBits 2 := by decide

theorem rowString_length (row : Fin N → Digest lambda) : (rowString row).length = 8 + N * (2 * lambda) := by
  simp [rowString, byteBits_length, BAVC.serializeArray_length]

theorem outerString_length (salt : Seed lambda) (rowHashes : Fin tau → Digest lambda) :
    (outerString salt rowHashes).length = 8 + (lambda + tau * (2 * lambda)) := by
  simp [outerString, byteBits_length, BAVC.serializeArray_length]

theorem auxString_length (root : Digest lambda) (tail : List Bool) :
    (auxString root tail).length = 8 + (2 * lambda + tail.length) := by
  simp [auxString, Spec.BLCHashChain.auxQuery, byteBits_length]

theorem maskInput_length (auxiliary : Digest lambda) : (maskInput auxiliary).length = 2 * lambda := by
  simp [maskInput]

theorem getD_append_right (l r : List Bool) (k : Nat) :
    (l ++ r).getD (l.length + k) false = r.getD k false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  congr 2
  omega

theorem getD_append_left (l r : List Bool) (k : Nat) (hk : k < l.length) :
    (l ++ r).getD k false = l.getD k false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getD_ofFn {n : Nat} (v : Fin n → Bool) (i : Fin n) : (List.ofFn v).getD i.val false = v i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem serializeArray_getD {n bits : Nat} (v : Fin n → Bits bits) (e : Fin n) (i : Fin bits) :
    (serializeArray v).getD (bits * e.val + i.val) false = v e i := by
  induction n with
  | zero => exact Fin.elim0 e
  | succ n ih =>
    have hs : serializeArray v = List.ofFn (v 0) ++ serializeArray (fun j => v j.succ) := by
      simp only [serializeArray, List.ofFn_succ, List.flatMap_cons]
    rw [hs]
    refine Fin.cases ?_ (fun e' => ?_) e
    · simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add]
      rw [getD_append_left _ _ _ (by simp [i.isLt]), getD_ofFn]
    · have hidx : bits * (e'.succ).val + i.val = (List.ofFn (v 0)).length + (bits * e'.val + i.val) := by
        simp only [Fin.val_succ, List.length_ofFn]
        ring
      rw [hidx, getD_append_right]
      exact ih (fun j => v j.succ) e'

theorem window_auxString (root : Digest lambda) (tail : List Bool) : window (auxString root tail) 8 = root := by
  funext i
  simp only [window, auxString, Spec.BLCHashChain.auxQuery]
  rw [show 8 = (byteBits 2).length from (byteBits_length 2).symm, getD_append_right,
    getD_append_left _ _ _ (by simp [i.isLt]), getD_ofFn]

theorem window_outerString (salt : Seed lambda) (rowHashes : Fin tau → Digest lambda) (e : Fin tau) :
    window (outerString salt rowHashes) (rowOffset lambda e.val) = rowHashes e := by
  funext i
  simp only [window, outerString, rowOffset]
  rw [show 8 + lambda + 2 * lambda * e.val + i.val = (byteBits 1).length + ((List.ofFn salt).length + (2 * lambda * e.val + i.val)) from by
      simp [byteBits_length]; ring,
    getD_append_right, getD_append_right, serializeArray_getD]

theorem window_maskInput (auxiliary : Digest lambda) : window (maskInput auxiliary) 0 = auxiliary := by
  funext i
  simp only [window, maskInput, Nat.zero_add]
  exact getD_ofFn auxiliary i

theorem root_mem_mentions (root : Digest lambda) (tail : List Bool) :
    root ∈ mentions lambda tau (auxString root tail) := by
  exact Finset.mem_image.mpr ⟨8, by simp [offsets], window_auxString root tail⟩

theorem rowHash_mem_mentions (salt : Seed lambda) (rowHashes : Fin tau → Digest lambda) (e : Fin tau) :
    rowHashes e ∈ mentions lambda tau (outerString salt rowHashes) := by
  refine Finset.mem_image.mpr ⟨rowOffset lambda e.val, ?_, window_outerString salt rowHashes e⟩
  simp only [offsets, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  exact Or.inr ⟨e.val, e.isLt, rfl⟩

theorem auxiliary_mem_mentions (auxiliary : Digest lambda) :
    auxiliary ∈ mentions lambda tau (maskInput auxiliary) := by
  exact Finset.mem_image.mpr ⟨0, by simp [offsets], window_maskInput auxiliary⟩

theorem mentions_card_le (s : List Bool) : (mentions lambda tau s).card ≤ tau + 2 := by
  refine (Finset.card_image_le).trans ?_
  simp only [offsets]
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : ({0, 8} : Finset Nat).card ≤ 2 := by decide
  have h2 : ((Finset.range tau).image (rowOffset lambda)).card ≤ tau :=
    Finset.card_image_le.trans (by simp)
  omega

theorem take_eight (b : Byte) (rest : List Bool) : (byteBits b ++ rest).take 8 = byteBits b := by
  rw [← byteBits_length b, List.take_left]

theorem auxString_ne_outerString (root : Digest lambda) (tail : List Bool) (salt : Seed lambda)
    (rowHashes : Fin tau → Digest lambda) : auxString root tail ≠ outerString salt rowHashes := by
  intro h
  have ht := congrArg (List.take 8) h
  simp only [auxString, Spec.BLCHashChain.auxQuery, outerString, take_eight] at ht
  exact byteBits_one_ne_two ht.symm

theorem auxString_ne_rowString (root : Digest lambda) (tail : List Bool) (row : Fin N → Digest lambda) :
    auxString root tail ≠ rowString row := by
  intro h
  have ht := congrArg (List.take 8) h
  simp only [auxString, Spec.BLCHashChain.auxQuery, rowString, take_eight] at ht
  exact byteBits_one_ne_two ht.symm

theorem outerString_ne_rowString (hlambda : 0 < lambda) (salt : Seed lambda) (rowHashes : Fin tau → Digest lambda)
    (row : Fin N → Digest lambda) : outerString salt rowHashes ≠ rowString row := by
  intro h
  have hl := congrArg List.length h
  rw [outerString_length, rowString_length] at hl
  have : lambda * (1 + 2 * tau) = lambda * (2 * N) := by
    have := hl
    ring_nf at this ⊢
    omega
  have hodd := Nat.eq_of_mul_eq_mul_left hlambda this
  omega

theorem maskInput_ne_auxString (auxiliary root : Digest lambda) (tail : List Bool) :
    auxString root tail ≠ maskInput auxiliary := by
  intro h
  have hl := congrArg List.length h
  rw [auxString_length, maskInput_length] at hl
  omega

theorem maskInput_ne_outerString (htau : 0 < tau) (auxiliary : Digest lambda) (salt : Seed lambda)
    (rowHashes : Fin tau → Digest lambda) : outerString salt rowHashes ≠ maskInput auxiliary := by
  intro h
  have hl := congrArg List.length h
  rw [outerString_length, maskInput_length] at hl
  nlinarith

theorem maskInput_ne_rowString (hN : 0 < N) (auxiliary : Digest lambda) (row : Fin N → Digest lambda) :
    rowString row ≠ maskInput auxiliary := by
  intro h
  have hl := congrArg List.length h
  rw [rowString_length, maskInput_length] at hl
  nlinarith

theorem chain_linked (salt : Seed lambda) (rows : Fin tau → Fin N → Digest lambda) (rowHashes : Fin tau → Digest lambda)
    (root : Digest lambda) (tail : List Bool) (auxiliary : Digest lambda) (e : Fin tau) :
    LinkedTo (mentions lambda tau) (maskInput auxiliary) (chain salt rows rowHashes root tail auxiliary e) ∧
      Linked (mentions lambda tau) (chain salt rows rowHashes root tail auxiliary e) := by
  refine ⟨auxiliary_mem_mentions auxiliary, ?_⟩
  exact ⟨root_mem_mentions root tail, rowHash_mem_mentions salt rowHashes e, trivial⟩

theorem chain_distinct (hlambda : 0 < lambda) (htau : 0 < tau) (hN : 0 < N) (salt : Seed lambda)
    (rows : Fin tau → Fin N → Digest lambda) (rowHashes : Fin tau → Digest lambda)
    (root : Digest lambda) (tail : List Bool) (auxiliary : Digest lambda) (e : Fin tau) :
    (∀ p ∈ chain salt rows rowHashes root tail auxiliary e, p.1 ≠ maskInput auxiliary) ∧
      (chain salt rows rowHashes root tail auxiliary e).Pairwise (fun p q => p.1 ≠ q.1) := by
  constructor
  · intro p hp
    simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact maskInput_ne_auxString auxiliary root tail
    · exact maskInput_ne_outerString htau auxiliary salt rowHashes
    · exact maskInput_ne_rowString hN auxiliary (rows e)
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact auxString_ne_outerString root tail salt rowHashes
      · exact auxString_ne_rowString root tail (rows e)
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl
      exact outerString_ne_rowString hlambda salt rowHashes (rows e)
    · intro q hq
      simp at hq

/-- Relation to the existing reconstruction program strings. -/
theorem rowInput_eq (row : Vector (ReconstructedLeaf lambda) N) :
    Spec.BAVCReconstructionProgram.rowInput row = rowString (fun i : Fin N => row[i].commitment) := rfl

theorem outerInput_eq (salt : Seed lambda) (rows : Spec.BAVCReconstructionProgram.Rows lambda N tau) :
    Spec.BAVCReconstructionProgram.outerInput salt rows = outerString salt (fun e : Fin tau => rows.hashes[e]) := rfl

section Experiment

variable {M State : Type*} [Fintype M] [Nonempty M]

/-- For every execution, the auxiliary, outer and row strings are present in
the table before the mask input was answered, or a fresh digest hit a
mentioned value. The stored-chain premises are facts about the final table. -/
theorem chain_present_or_mention (hlambda : 0 < lambda) (htau : 0 < tau) (hN : 0 < N)
    (procedure : Spec.RandomOracleCollision.Procedure (List Bool) (Digest lambda × M) State)
    (budget : Nat) (initial : State) (out : Result (List Bool) (Digest lambda × M) State)
    (hout : out ∈ (experiment procedure budget initial).support)
    (salt : Seed lambda) (rows : Fin tau → Fin N → Digest lambda) (rowHashes : Fin tau → Digest lambda)
    (root : Digest lambda) (tail : List Bool) (auxiliary : Digest lambda)
    (hrows : ∀ e, ∃ pair, out.table (rowString (rows e)) = some pair ∧ pair.1 = rowHashes e)
    (houter : ∃ pair, out.table (outerString salt rowHashes) = some pair ∧ pair.1 = root)
    (haux : ∃ pair, out.table (auxString root tail) = some pair ∧ pair.1 = auxiliary)
    (em : Entry (List Bool) (Digest lambda × M)) (hem : em ∈ out.trace) (hemi : em.input = maskInput auxiliary) :
    ((∀ e, (em.before (rowString (rows e))).isSome) ∧ (em.before (outerString salt rowHashes)).isSome ∧
        (em.before (auxString root tail)).isSome) ∨
      prefixBad (digestMention (mentions lambda tau)) out.trace = true := by
  obtain ⟨hord, hfresh, _, _⟩ := OracleChain.experiment_ordered procedure budget initial out hout
  have htraced := RandomOracleTrace.experiment_invariants procedure budget initial out hout
  by_cases hbad : prefixBad (digestMention (mentions lambda tau)) out.trace = true
  · exact Or.inr hbad
  left
  have hall : ∀ e : Fin tau, Present em.before (chain salt rows rowHashes root tail auxiliary e) := by
    intro e
    obtain ⟨hto, hlinked⟩ := chain_linked salt rows rowHashes root tail auxiliary e
    obtain ⟨hne, hpair⟩ := chain_distinct hlambda htau hN salt rows rowHashes root tail auxiliary e
    have hstored : Stored out.table (chain salt rows rowHashes root tail auxiliary e) := by
      intro p hp
      simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact haux
      · exact houter
      · exact hrows e
    rcases OracleChain.chain_present_or_mention (mentions lambda tau) out.trace out.table hord hfresh htraced
      (chain salt rows rowHashes root tail auxiliary e) (maskInput auxiliary) hto hlinked hne hpair hstored
      em hem hemi with hpresent | hbad'
    · exact hpresent
    · exact absurd hbad' hbad
  obtain ⟨e0, _⟩ : ∃ e : Fin tau, True := ⟨⟨0, htau⟩, trivial⟩
  refine ⟨fun e => hall e (rowString (rows e), rowHashes e) (by simp [chain]),
    hall e0 (outerString salt rowHashes, root) (by simp [chain]),
    hall e0 (auxString root tail, auxiliary) (by simp [chain])⟩

end Experiment

end
end SDitH.Proofs.BAVCChainInputs
