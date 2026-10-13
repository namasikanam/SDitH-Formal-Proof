import SDitH.Spec.ChallengeEncoding
import SDitH.Proofs.ConcreteEncodings
import SDitH.Proofs.IntegerSamplingProbability
import SDitH.Proofs.BLCRetry
import SDitH.Proofs.FieldIrreducibility

namespace SDitH.Proofs.ChallengeEncoding

open Spec.ChallengeEncoding Spec.FieldRepresentation
open scoped Classical

theorem binaryRow_injective {kappa : Nat} :
    Function.Injective (Spec.GrayCode.binaryRow (kappa := kappa)) := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < kappa
  · let j : Fin kappa := ⟨kappa - 1 - k, by omega⟩
    have he := congrFun h j
    have hr : kappa - 1 - j.val = k := by dsimp [j]; omega
    simpa only [Spec.GrayCode.binaryRow, hr] using he
  · have hp : 2 ^ kappa ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hp), Nat.testBit_lt_two_pow (b.isLt.trans_le hp)]

theorem binaryFieldRow_injective {kappa : Nat} :
    Function.Injective (binaryFieldRow (kappa := kappa)) := by
  intro a b h
  apply binaryRow_injective
  funext j
  have he := congrFun h j
  simp only [binaryFieldRow] at he
  cases ha : Spec.GrayCode.binaryRow a j <;> cases hb : Spec.GrayCode.binaryRow b j <;> simp_all

theorem grayIndex_injective {kappa : Nat} : Function.Injective (grayIndex (kappa := kappa)) := by
  intro a b h
  exact Fin.ext (GrayCode.grayWord_injective (congrArg Fin.val h))

theorem grayIndices_bijective {tau kappa : Nat} :
    Function.Bijective (grayIndices (tau := tau) (kappa := kappa)) := by
  have hinj : Function.Injective (grayIndices (tau := tau) (kappa := kappa)) := by
    intro a b h
    funext e
    exact grayIndex_injective (congrFun h e)
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem binary_grayIndex {kappa : Nat} (i : Fin (2 ^ kappa)) :
    binaryFieldRow (grayIndex i) = Spec.GrayCode.grayFieldRow i := rfl

theorem grayMerge_relabel (category : Category) {tau kappa : Nat}
    (hidden : Fin tau → Fin (2 ^ kappa)) :
    grayMerge category hidden = binaryMerge category (grayIndices hidden) := rfl

/-- Equality on one integer is exceptional: the right-shift contribution
vanishes exactly for indices zero and one. -/
theorem grayIndex_eq_iff {kappa : Nat} (i : Fin (2 ^ kappa)) : grayIndex i = i ↔ i.val < 2 := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    change i.val ^^^ (i.val / 2) = i.val at hv
    have hz := congrArg (fun x => i.val ^^^ x) hv
    have he : i.val / 2 = 0 := by simpa [← Nat.xor_assoc] using hz
    omega
  · intro h
    apply Fin.ext
    change i.val ^^^ (i.val / 2) = i.val
    simp [show i.val / 2 = 0 by omega]

theorem binary_gray_row_eq_iff {kappa : Nat} (i : Fin (2 ^ kappa)) :
    binaryFieldRow i = Spec.GrayCode.grayFieldRow i ↔ i.val < 2 := by
  rw [← binary_grayIndex, binaryFieldRow_injective.eq_iff, eq_comm, grayIndex_eq_iff]

theorem binaryMerge_injective (category : Category) {tau kappa : Nat}
    (hsize : tau * kappa ≤ width category) :
    Function.Injective (binaryMerge category (tau := tau) (kappa := kappa)) := by
  intro a b h
  have he := ConcreteEncodings.psi_injective category hsize h
  funext e
  exact binaryFieldRow_injective (congrFun he e)

theorem grayMerge_injective (category : Category) {tau kappa : Nat}
    (hsize : tau * kappa ≤ width category) :
    Function.Injective (grayMerge category (tau := tau) (kappa := kappa)) := by
  intro a b h
  exact grayIndices_bijective.1 (binaryMerge_injective category hsize h)

/-- Exact pointwise correspondence in each submitted polynomial quotient.
The source's intended raw/Gray identification is not an assumption. -/
theorem merged_eq_iff (category : Category) {tau kappa : Nat}
    (hsize : tau * kappa ≤ width category) (hidden : Fin tau → Fin (2 ^ kappa)) :
    binaryMerge category hidden = grayMerge category hidden ↔ ∀ e, (hidden e).val < 2 := by
  rw [grayMerge_relabel, (binaryMerge_injective category hsize).eq_iff]
  constructor
  · intro h e
    exact (grayIndex_eq_iff (hidden e)).mp (congrFun h e).symm
  · intro h
    funext e
    exact ((grayIndex_eq_iff (hidden e)).mpr (h e)).symm

theorem inverse_merged_eq_iff (category : Category) {tau kappa : Nat}
    (hsize : tau * kappa ≤ width category) (hidden : Fin tau → Fin (2 ^ kappa)) :
    (binaryMerge category hidden)⁻¹ = (grayMerge category hidden)⁻¹ ↔
      ∀ e, (hidden e).val < 2 := by
  rw [inv_inj, merged_eq_iff category hsize]

theorem binaryMerge_zero (category : Category) {tau kappa : Nat} :
    binaryMerge category (fun _ : Fin tau => zeroIndex kappa) = 0 := by
  have hrow : Spec.BLC.challengeRow binaryFieldRow (fun _ : Fin tau => zeroIndex kappa) = 0 := by
    funext e j
    simp [Spec.BLC.challengeRow, binaryFieldRow, Spec.GrayCode.binaryRow, zeroIndex]
  unfold binaryMerge
  rw [hrow, map_zero]

theorem grayMerge_zero (category : Category) {tau kappa : Nat} :
    grayMerge category (fun _ : Fin tau => zeroIndex kappa) = 0 := by
  rw [grayMerge_relabel]
  have hg : grayIndices (fun _ : Fin tau => zeroIndex kappa) = fun _ => zeroIndex kappa := by
    funext e
    exact (grayIndex_eq_iff _).mpr (by simp [zeroIndex])
  rw [hg, binaryMerge_zero]

theorem binaryMerge_eq_zero_iff (category : Category) {tau kappa : Nat}
    (hsize : tau * kappa ≤ width category) (hidden : Fin tau → Fin (2 ^ kappa)) :
    binaryMerge category hidden = 0 ↔ hidden = fun _ => zeroIndex kappa := by
  rw [← binaryMerge_zero category (tau := tau) (kappa := kappa),
    (binaryMerge_injective category hsize).eq_iff]

theorem grayMerge_eq_zero_iff (category : Category) {tau kappa : Nat}
    (hsize : tau * kappa ≤ width category) (hidden : Fin tau → Fin (2 ^ kappa)) :
    grayMerge category hidden = 0 ↔ hidden = fun _ => zeroIndex kappa := by
  rw [← grayMerge_zero category (tau := tau) (kappa := kappa),
    (grayMerge_injective category hsize).eq_iff]

/-- A concrete index vector separates both nonzero merged points whenever
the execution set is nonempty and index 2 exists. It is not asserted to be a
SHAKE output or a full signature transcript. -/
theorem distinct_nonzero_merges (category : Category) {tau kappa : Nat}
    (hsize : tau * kappa ≤ width category) (ht : 0 < tau) (hk : 2 < 2 ^ kappa) :
    let hidden := fun _ : Fin tau => (⟨2, hk⟩ : Fin (2 ^ kappa))
    binaryMerge category hidden ≠ grayMerge category hidden ∧
      binaryMerge category hidden ≠ 0 ∧ grayMerge category hidden ≠ 0 := by
  dsimp only
  have hnonzero : (fun _ : Fin tau => (⟨2, hk⟩ : Fin (2 ^ kappa))) ≠ fun _ => zeroIndex kappa := by
    intro he
    have hv := congrArg Fin.val (congrFun he ⟨0, ht⟩)
    norm_num [zeroIndex] at hv
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hi := (merged_eq_iff category hsize _).mp he ⟨0, ht⟩
    norm_num at hi
  · exact fun he => hnonzero ((binaryMerge_eq_zero_iff category hsize _).mp he)
  · exact fun he => hnonzero ((grayMerge_eq_zero_iff category hsize _).mp he)

/-- The images coincide by an explicit finite relabeling, even though the
two maps generally disagree on a particular challenge vector. -/
theorem merged_ranges_equal (category : Category) (tau kappa : Nat) :
    Set.range (binaryMerge category (tau := tau) (kappa := kappa)) =
      Set.range (grayMerge category (tau := tau) (kappa := kappa)) := by
  ext x
  constructor
  · rintro ⟨hidden, rfl⟩
    obtain ⟨preimage, hp⟩ := grayIndices_bijective.2 hidden
    exact ⟨preimage, by rw [grayMerge_relabel, hp]⟩
  · rintro ⟨hidden, rfl⟩
    exact ⟨grayIndices hidden, rfl⟩

theorem merged_image_card (category : Category) (tau kappa : Nat)
    (hsize : tau * kappa ≤ width category) :
    Nat.card (Set.range (binaryMerge category (tau := tau) (kappa := kappa))) = 2 ^ (tau * kappa) := by
  calc
    _ = Nat.card (Fin tau → Fin (2 ^ kappa)) :=
      (Nat.card_congr (Equiv.ofInjective _ (binaryMerge_injective category hsize))).symm
    _ = _ := by simp [Nat.card_eq_fintype_card, ← pow_mul, Nat.mul_comm]

/-- A law of explicitly uniform index vectors, not SHAKE-generated values:
relabeling preserves the pushforward distribution on the common merge image. -/
theorem uniform_merge_law (category : Category) (tau kappa : Nat) :
    (PMF.uniformOfFintype (Fin tau → Fin (2 ^ kappa))).map (grayMerge category) =
      (PMF.uniformOfFintype (Fin tau → Fin (2 ^ kappa))).map (binaryMerge category) := by
  let relabel : (Fin tau → Fin (2 ^ kappa)) ≃ (Fin tau → Fin (2 ^ kappa)) :=
    Equiv.ofBijective grayIndices grayIndices_bijective
  have hfun : grayMerge category = (binaryMerge category) ∘ relabel := rfl
  rw [hfun, ← PMF.map_comp, IntegerSamplingProbability.map_uniform_equiv relabel]

/-- Both index interpretations make the same retry decision and open the
same hidden leaves. Their actual nonzero field points can still differ. -/
theorem retry_attempt_equal (category : Category) {tau kappa wpow : Nat}
    (hsize : tau * kappa ≤ width category)
    (key : Spec.BAVC.Key (width category) tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (counter : Spec.BLCRetry.Counter) :
    Spec.BLCRetry.attempt key Topen expand (binaryMerge category) counter =
      Spec.BLCRetry.attempt key Topen expand (grayMerge category) counter := by
  unfold Spec.BLCRetry.attempt
  dsimp only
  cases hb : Spec.BAVC.openCommitment key (expand counter).hidden Topen with
  | error error => cases error <;> rfl
  | ok opening =>
    simp only [ne_eq, binaryMerge_eq_zero_iff category hsize, grayMerge_eq_zero_iff category hsize]

theorem retry_observations_equal (category : Category) {tau kappa wpow : Nat}
    (hsize : tau * kappa ≤ width category)
    (key : Spec.BAVC.Key (width category) tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow) (fuel : Nat) :
    Spec.BLCRetry.openRandomEvaluation key Topen expand (binaryMerge category) fuel =
      Spec.BLCRetry.openRandomEvaluation key Topen expand (grayMerge category) fuel := by
  have he : Spec.BLCRetry.attempt key Topen expand (binaryMerge category) =
      Spec.BLCRetry.attempt key Topen expand (grayMerge category) :=
    funext (retry_attempt_equal category hsize key Topen expand)
  simp only [Spec.BLCRetry.openRandomEvaluation, he]

theorem submitted_encoding_bounds :
    let categories : List Category := [.i, .i, .iii, .iii, .v, .v]
    (∀ row ∈ categories.zip Spec.hashProofParameters,
      row.2.tau * row.2.kappa ≤ width row.1 ∧ 0 < row.2.tau ∧ 2 < 2 ^ row.2.kappa) ∧
    (∀ row ∈ categories.zip Spec.cipherProofParameters,
      row.2.tau * row.2.kappa ≤ width row.1 ∧ 0 < row.2.tau ∧ 2 < 2 ^ row.2.kappa) := by
  decide

end SDitH.Proofs.ChallengeEncoding
