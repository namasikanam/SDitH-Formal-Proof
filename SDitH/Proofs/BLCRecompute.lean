import SDitH.Spec.BLCRecompute
import SDitH.Proofs.BAVCReconstruction
import SDitH.Proofs.BLCArithmetic

namespace SDitH.Proofs.BLCRecompute

open Spec.BLCRecompute Spec.DomainSeparation
open scoped BigOperators

theorem readSeed_ok_iff {lambda tau kappa : Nat} (seed : Option (SeedArray lambda tau kappa))
    (e : Fin tau) (i : Fin (2 ^ kappa)) (value : Bits lambda) :
    readSeed seed e i = .ok value ↔ ∃ values, seed = some values ∧ values e i = some value := by
  cases seed with
  | none => simp [readSeed]
  | some values => cases h : values e i <;> simp [readSeed, h]

/-- An update never manufactures an initial share. -/
theorem addShare_present {ell kappa : Nat} (initial : Option (Share ell kappa))
    (random : Fin ell → ZMod 2) (hidden i : Fin (2 ^ kappa))
    (out : Option (Share ell kappa)) (h : addShare initial random hidden i = .ok out) :
    ∃ value, initial = some value := by
  cases initial with
  | none => simp [addShare] at h
  | some value => exact ⟨value, rfl⟩

/-- A successful inner loop with an absent share leaves it absent; it can
only have skipped all indices it inspected. -/
theorem foldLeaves_absent {lambda tau kappa s wit rnd : Nat}
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (seed : Option (SeedArray lambda tau kappa)) (e : Fin tau) (hidden : Fin (2 ^ kappa))
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (count : Nat) (hc : count ≤ 2 ^ kappa) (out : Option (Share (s + (wit + rnd)) kappa))
    (h : foldLeavesThrough p salt seed e hidden none randomCount enough count hc = .ok out) :
    out = none := by
  induction count generalizing out with
  | zero => exact (Except.ok.inj h).symm
  | succ count ih =>
    obtain ⟨current, hp, hs⟩ := (BAVCReconstruction.bind_ok_iff _ _ out).mp h
    have he := ih (by omega) current hp
    subst current
    dsimp only at hs
    split at hs
    · exact (Except.ok.inj hs).symm
    · obtain ⟨value, _, ha⟩ := (BAVCReconstruction.bind_ok_iff _ _ out).mp hs
      simp [addShare] at ha

def prefixSum {kappa ell : Nat} (random : Fin (2 ^ kappa) → Fin ell → ZMod 2)
    (hidden : Fin (2 ^ kappa)) (count : Nat) (c : Fin ell) (j : Fin kappa) : ZMod 2 :=
  ∑ i, if i.val < count then
    random i c * (Spec.GrayCode.grayFieldRow hidden j - Spec.GrayCode.grayFieldRow i j) else 0

theorem prefixSum_succ {kappa ell : Nat} (random : Fin (2 ^ kappa) → Fin ell → ZMod 2)
    (hidden : Fin (2 ^ kappa)) (count : Nat) (hc : count < 2 ^ kappa)
    (c : Fin ell) (j : Fin kappa) :
    prefixSum random hidden (count + 1) c j = prefixSum random hidden count c j +
      random ⟨count, hc⟩ c *
        (Spec.GrayCode.grayFieldRow hidden j - Spec.GrayCode.grayFieldRow ⟨count, hc⟩ j) := by
  let term := fun i => random i c *
    (Spec.GrayCode.grayFieldRow hidden j - Spec.GrayCode.grayFieldRow i j)
  have step (i : Fin (2 ^ kappa)) :
      (if i.val < count + 1 then term i else 0) =
        (if i.val < count then term i else 0) + (if i = ⟨count, hc⟩ then term i else 0) := by
    by_cases hlt : i.val < count
    · have hne : i ≠ ⟨count, hc⟩ := by
        intro he
        have hv : i.val = count := congrArg Fin.val he
        omega
      simp [hlt, show i.val < count + 1 by omega, hne]
    · by_cases he : i = ⟨count, hc⟩
      · subst i; simp
      · have hn : ¬ i.val < count + 1 := by
          intro hsmall
          exact he (Fin.ext (show i.val = count by omega))
        simp [hlt, he, hn]
  change (∑ i, if i.val < count + 1 then term i else 0) =
    (∑ i, if i.val < count then term i else 0) + term ⟨count, hc⟩
  simp_rw [step]
  rw [Finset.sum_add_distrib]
  simp

/-- Exact coordinate sums of the real PRG/sampling loop under explicit
initialized bindings. The hidden summand is zero, not a hidden-seed read. -/
theorem foldLeaves_sum {lambda tau kappa s wit rnd : Nat}
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (seeds : Fin tau → Fin (2 ^ kappa) → Bits lambda) (e : Fin tau) (hidden : Fin (2 ^ kappa))
    (initial : Share (s + (wit + rnd)) kappa)
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (count : Nat) (hc : count ≤ 2 ^ kappa) :
    foldLeavesThrough p salt (some fun e i => some (seeds e i)) e hidden (some initial)
      randomCount enough count hc = .ok (some fun c j => initial c j +
        prefixSum (Spec.BLCCommit.randomTable p salt seeds randomCount enough e) hidden count c j) := by
  induction count with
  | zero => simp [foldLeavesThrough, prefixSum]
  | succ count ih =>
    simp only [foldLeavesThrough, ih (by omega), Bind.bind, Except.bind]
    split
    · rename_i he
      congr 2
      funext c j
      rw [prefixSum_succ _ _ _ (by omega), he]
      simp
    · simp only [readSeed, addShare]
      congr 2
      funext c j
      rw [prefixSum_succ _ _ _ (by omega)]
      change initial c j + prefixSum _ _ count c j + _ = initial c j + (prefixSum _ _ count c j + _)
      exact add_assoc _ _ _

theorem prefixSum_full {kappa ell : Nat} (random : Fin (2 ^ kappa) → Fin ell → ZMod 2)
    (hidden : Fin (2 ^ kappa)) (c : Fin ell) (j : Fin kappa) :
    prefixSum random hidden (2 ^ kappa) c j =
      ∑ i ∈ Finset.univ.erase hidden,
        random i c * (Spec.GrayCode.grayFieldRow hidden j - Spec.GrayCode.grayFieldRow i j) := by
  simp [prefixSum]

/-- Success preserves the actual zero initialization of reval, independent
of the separate externally supplied rshare. -/
theorem foldExecution_evaluation_zero {lambda tau kappa s wit rnd : Nat}
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (bindings : Bindings lambda tau kappa (s + (wit + rnd)))
    (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa))
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount) (e : Fin tau)
    (out : FoldedExecution (s + (wit + rnd)) kappa)
    (h : foldExecution p salt bindings aux hidden randomCount enough e = .ok out) :
    out.evaluation = 0 := by
  obtain ⟨current, _, hs⟩ := (BAVCReconstruction.bind_ok_iff _ _ out).mp h
  obtain ⟨corrected, _, ho⟩ := (BAVCReconstruction.bind_ok_iff _ _ out).mp hs
  have he := Except.ok.inj ho
  cases he
  rfl

theorem foldExecutions_coordinate {lambda tau kappa s wit rnd : Nat}
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (bindings : Bindings lambda tau kappa (s + (wit + rnd)))
    (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa))
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (count : Nat) (hc : count ≤ tau)
    (out : Vector (FoldedExecution (s + (wit + rnd)) kappa) count)
    (h : foldExecutionsThrough p salt bindings aux hidden randomCount enough count hc = .ok out)
    (e : Nat) (he : e < count) :
    foldExecution p salt bindings aux hidden randomCount enough ⟨e, he.trans_le hc⟩ = .ok out[e] := by
  induction count with
  | zero => omega
  | succ count ih =>
    obtain ⟨previous, hp, hs⟩ := (BAVCReconstruction.bind_ok_iff _ _ out).mp h
    obtain ⟨last, hl, ho⟩ := (BAVCReconstruction.bind_ok_iff _ _ out).mp hs
    have heq : previous.push last = out := Except.ok.inj ho
    subst out
    by_cases hlt : e < count
    · rw [Vector.getElem_push_lt hlt]
      exact ih (by omega) previous hp hlt
    · have heq : e = count := by omega
      subst e
      rw [Vector.getElem_push_eq]
      exact hl

theorem collectShares_coordinate {ell kappa count : Nat}
    (rows : Vector (FoldedExecution ell kappa) count) (out : Vector (Share ell kappa) count)
    (h : collectShares rows = .ok out) (e : Nat) (he : e < count) :
    rows[e].share = some out[e] := by
  induction count with
  | zero => omega
  | succ count ih =>
    obtain ⟨previous, hp, hs⟩ := (BAVCReconstruction.bind_ok_iff _ _ out).mp h
    cases hl : rows[count].share with
    | none => simp [hl] at hs
    | some value =>
      simp only [hl] at hs
      have heq : previous.push value = out := Except.ok.inj hs
      subst out
      by_cases hlt : e < count
      · rw [Vector.getElem_push_lt hlt]
        have hr := ih rows.pop previous hp hlt
        simpa using hr
      · have heq : e = count := by omega
        subst e
        simpa using hl

/-- Both loop contributions, including the externally supplied initial share
and the distinct phi_mu value, are retained in the exact result. -/
theorem foldExecution_sum {lambda tau kappa s wit rnd : Nat}
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (nodes : Spec.BAVC.NodesBinding lambda tau (2 ^ kappa))
    (seeds : Fin tau → Fin (2 ^ kappa) → Bits lambda)
    (initial : Fin tau → Share (s + (wit + rnd)) kappa)
    (phi : Fin tau → Fin (2 ^ kappa) → Fin kappa → ZMod 2)
    (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa))
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount) (e : Fin tau) :
    foldExecution p salt ⟨nodes, some (fun e i => some (seeds e i)),
      (fun e => some (initial e)), some phi⟩ aux hidden randomCount enough e =
      .ok ⟨0, some fun c j => initial e c j +
        (∑ i ∈ Finset.univ.erase (hidden e),
          Spec.BLCCommit.randomTable p salt seeds randomCount enough e i c *
            (Spec.GrayCode.grayFieldRow (hidden e) j - Spec.GrayCode.grayFieldRow i j)) +
        (if he : 0 < e.val then aux.corrections (correctionIndex e he) c * phi e (hidden e) j else 0)⟩ := by
  by_cases he : 0 < e.val
  · simp only [foldExecution, foldLeaves_sum, Bind.bind, Except.bind, addCorrection, dif_pos he]
    congr 3
    funext c j
    rw [prefixSum_full]
  · simp only [foldExecution, foldLeaves_sum, Bind.bind, Except.bind, addCorrection, dif_neg he]
    congr 3
    funext c j
    rw [prefixSum_full, add_zero]

section Prefix

variable {F : Type} [Field F] [DecidableEq F]
  {lambda tau kappa B wit rnd wpow : Nat}
  (p : Spec.BLCCommit.Primitives lambda tau kappa (lambda + B) wit rnd)
  (salt : Bits lambda) (aux : Spec.BLCCommit.Auxiliary tau (lambda + B) wit rnd)
  (decomposition : Spec.BLCRetry.Counter × Spec.BAVC.Opening lambda tau)
  (expand : Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
  (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
  (bindings : Bindings lambda tau kappa ((lambda + B) + (wit + rnd)))
  (randomCount consistencyCount : Nat)
  (hrandom : (lambda + B) + (wit + rnd) ≤ 8 * randomCount)
  (hconsistency : wit + rnd ≤ 8 * consistencyCount)

theorem prepare_header_rejected
    (h : ¬ (Spec.BLCRetry.GrindingPassed (expand decomposition.1).grinding ∧
      encode (expand decomposition.1).hidden ≠ 0)) :
    prepareWithBindings p salt aux decomposition expand encode Topen bindings
      randomCount consistencyCount hrandom hconsistency = .error .headerRejected := by
  simp only [prepareWithBindings, if_neg h]

/-- This is a characterization of reaching the unresolved line-21 operands,
not of completing Algorithm 12. It exposes every subroutine run equation. -/
theorem prepare_ok_iff (state : ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd) :
    prepareWithBindings p salt aux decomposition expand encode Topen bindings
      randomCount consistencyCount hrandom hconsistency = .ok state ↔
    Spec.BLCRetry.GrindingPassed (expand decomposition.1).grinding ∧
    encode (expand decomposition.1).hidden ≠ 0 ∧
    ∃ reconstruction folded shares,
      Spec.BAVC.reconstructWithNodes
        (Spec.SeedPrimitives.bavcPrimitives (tau * (2 ^ kappa)) p.grinding p.encStar p.hash)
        salt (expand decomposition.1).hidden decomposition.2 Topen bindings.nodes = .ok reconstruction ∧
      foldExecutionsThrough p salt bindings aux (expand decomposition.1).hidden
        randomCount hrandom tau le_rfl = .ok folded ∧
      collectShares folded = .ok shares ∧
      state =
        let Q := concatenate shares
        let haux := p.hashAux ⟨reconstruction.hcom, aux.corrections⟩
        let binaryMatrix := Spec.ByteSampling.expandConsistency (p.xof haux) lambda B
          (wit + rnd) consistencyCount hconsistency
        let M := fun i j => Spec.BLCCommit.bitField (binaryMatrix.value i j)
        ⟨encode (expand decomposition.1).hidden, (encode (expand decomposition.1).hidden)⁻¹,
          aux, reconstruction, Q, haux, M, Spec.BLC.consistencyColumns M Q⟩ := by
  constructor
  · intro h
    unfold prepareWithBindings at h
    dsimp only at h
    split at h
    · rename_i hg
      cases hb : Spec.BAVC.reconstructWithNodes
        (Spec.SeedPrimitives.bavcPrimitives (tau * (2 ^ kappa)) p.grinding p.encStar p.hash)
        salt (expand decomposition.1).hidden decomposition.2 Topen bindings.nodes with
      | error error => simp only [hb, Bind.bind, Except.bind] at h; contradiction
      | ok reconstruction =>
        simp only [hb, Bind.bind, Except.bind] at h
        obtain ⟨folded, hfolded, hs⟩ := (BAVCReconstruction.bind_ok_iff _ _ state).mp h
        obtain ⟨shares, hc, ho⟩ := (BAVCReconstruction.bind_ok_iff _ _ state).mp hs
        exact ⟨hg.1, hg.2, reconstruction, folded, shares, rfl, hfolded, hc, (Except.ok.inj ho).symm⟩
    · contradiction
  · rintro ⟨hg, hd, reconstruction, folded, shares, hr, hf, hc, ho⟩
    have hgood : Spec.BLCRetry.GrindingPassed (expand decomposition.1).grinding ∧
        encode (expand decomposition.1).hidden ≠ 0 := ⟨hg, hd⟩
    simp only [prepareWithBindings, if_pos hgood, hr, Bind.bind, Except.bind, hf, hc]
    exact congrArg Except.ok ho.symm

theorem prepare_delta_nonzero (state : ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd)
    (h : prepareWithBindings p salt aux decomposition expand encode Topen bindings
      randomCount consistencyCount hrandom hconsistency = .ok state) :
    state.deltaInv = encode (expand decomposition.1).hidden ∧
    state.delta = state.deltaInv⁻¹ ∧ state.delta ≠ 0 := by
  obtain ⟨_, hn, reconstruction, folded, shares, _, _, _, rfl⟩ :=
    (prepare_ok_iff p salt aux decomposition expand encode Topen bindings
      randomCount consistencyCount hrandom hconsistency state).mp h
  exact ⟨rfl, rfl, inv_ne_zero hn⟩

/-- Source reconstruction errors remain the cause of an undefined pair read
at line 8. They are not converted into the explicit header-rejection branch. -/
theorem prepare_reconstruction_error (cause : Spec.BAVC.ReconstructionError)
    (hg : Spec.BLCRetry.GrindingPassed (expand decomposition.1).grinding ∧
      encode (expand decomposition.1).hidden ≠ 0)
    (hb : Spec.BAVC.reconstructWithNodes
      (Spec.SeedPrimitives.bavcPrimitives (tau * (2 ^ kappa)) p.grinding p.encStar p.hash)
      salt (expand decomposition.1).hidden decomposition.2 Topen bindings.nodes = .error cause) :
    prepareWithBindings p salt aux decomposition expand encode Topen bindings
      randomCount consistencyCount hrandom hconsistency = .error (.undefinedReconstructionResult cause) := by
  simp only [prepareWithBindings, if_pos hg, hb, Bind.bind, Except.bind]

include hrandom hconsistency in
/-- With no supplied source bindings, a positive execution count and at
least two leaves cannot reach line 21, by the actual reconstruction body. -/
theorem prepare_absent_no_return (ht : 0 < tau) (hn : 1 < 2 ^ kappa)
    (state : ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd) :
    prepare p salt aux decomposition expand encode Topen
      randomCount consistencyCount hrandom hconsistency ≠ .ok state := by
  intro h
  obtain ⟨_, _, reconstruction, _, _, hr, _⟩ :=
    (prepare_ok_iff p salt aux decomposition expand encode Topen absentBindings
      randomCount consistencyCount hrandom hconsistency state).mp h
  exact BAVCReconstruction.reconstruct_undeclared_no_return _ _ _ _ _ ht hn reconstruction hr

end Prefix

/-- The checked Category-I opening's literal capacity rejection propagates
to the line-8 undefined pair read, for every external binding environment. -/
theorem categoryI_recomputation_failure {F : Type} [Field F] [DecidableEq F]
    {B wit rnd wpow : Nat}
    (p : Spec.BLCCommit.Primitives 128 11 11 (128 + B) wit rnd) (salt : Bits 128)
    (aux : Spec.BLCCommit.Auxiliary 11 (128 + B) wit rnd)
    (key : Spec.BAVC.Key 128 11 2048) (ctr : Spec.BLCRetry.Counter)
    (expand : Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge 11 2048 wpow)
    (encode : (Fin 11 → Fin 2048) → F)
    (hh : (expand ctr).hidden = BAVC.categoryIHidden)
    (hg : Spec.BLCRetry.GrindingPassed (expand ctr).grinding ∧ encode (expand ctr).hidden ≠ 0)
    (bindings : Bindings 128 11 11 ((128 + B) + (wit + rnd)))
    (randomCount consistencyCount : Nat)
    (hrandom : (128 + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount) :
    prepareWithBindings p salt aux (ctr, BAVC.categoryIOpening key) expand encode 109 bindings
      randomCount consistencyCount hrandom hconsistency =
        .error (.undefinedReconstructionResult .boundRejected) := by
  apply prepare_reconstruction_error p salt aux (ctr, BAVC.categoryIOpening key) expand encode 109
    bindings randomCount consistencyCount hrandom hconsistency .boundRejected hg
  dsimp only
  rw [hh]
  exact BAVCReconstruction.categoryI_full_rejection key _ salt bindings.nodes

/-- The suffix computes the printed witness/randomness slices for any given
base. Only the digest consumes that base; no line-21 equation is assumed. -/
theorem suffix_values {F : Type*} [Field F] [Algebra (ZMod 2) F]
    {lambda tau kappa s wit rnd : Nat} (xi : F)
    (hashLines : LinesHashInput lambda tau kappa s → Spec.BLCCommit.Digest lambda)
    (state : ConsistencyBoundary F lambda tau kappa s wit rnd)
    (base : Fin s → Fin tau → Fin kappa → ZMod 2) :
    (suffix xi hashLines state base).delta = state.delta ∧
    (∀ j, (suffix xi hashLines state base).witness j =
      algebraMap (ZMod 2) F (state.auxiliary.witnessCorrection j) +
        state.delta * Spec.BLC.psi xi (state.Q (Spec.BLC.witnessIndex j))) ∧
    (∀ j, (suffix xi hashLines state base).randomness j =
      state.delta * Spec.BLC.psi xi (state.Q (Spec.BLC.randomnessIndex j))) ∧
    (suffix xi hashLines state base).lines =
      hashLines ⟨state.auxiliaryDigest, state.auxiliary.plain, base⟩ :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem concrete_hash_layout (category : Spec.FieldRepresentation.Category) {tau kappa s : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s)
    (input : LinesHashInput (Spec.FieldRepresentation.width category) tau kappa s) :
    concreteHashLines category encoding input = Spec.SHAKE.hash category
      (Spec.BAVC.byteBits 3 ++ (List.ofFn input.auxiliary ++ encoding.vector input.plain ++
        encoding.base input.base)) := rfl

/-- For the real typed hash inputs the exact omitted payload is the encoded
witness correction. This compares messages, not hash outputs. -/
theorem lines_payload_difference {category : Spec.FieldRepresentation.Category} {tau kappa s wit : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s)
    (input : Spec.BLCCommit.LinesHashInput (Spec.FieldRepresentation.width category) tau kappa s wit) :
    Spec.ConcreteBLC.linesPayload encoding input =
      linesPayload encoding ⟨input.auxiliary, input.plain, input.base⟩ ++
        encoding.vector input.witnessCorrection := rfl

theorem lines_payload_ne {category : Spec.FieldRepresentation.Category} {tau kappa s wit : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s)
    (input : Spec.BLCCommit.LinesHashInput (Spec.FieldRepresentation.width category) tau kappa s wit)
    (hn : 0 < (encoding.vector input.witnessCorrection).length) :
    Spec.ConcreteBLC.linesPayload encoding input ≠
      linesPayload encoding ⟨input.auxiliary, input.plain, input.base⟩ := by
  rw [lines_payload_difference]
  intro h
  have hl := congrArg List.length h
  simp only [List.length_append] at hl
  omega

end SDitH.Proofs.BLCRecompute
