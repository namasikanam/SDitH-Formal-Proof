import SDitH.Proofs.FieldBytes
import SDitH.Proofs.FieldIrreducibility
import SDitH.Proofs.UniformVectors

/-! Explicit uniform-byte laws for the representation-parameterized field
sampler. No concrete PRG, XOF, hash, or serializer is asserted to have this law.
The consumed byte counts and coefficient ordering remain visible arguments.
-/

namespace SDitH.Proofs.FieldByteProbability

open Spec.DomainSeparation Spec.FieldRepresentation Spec.FieldBytes Spec.ByteSampling
open FieldBytes IntegerSamplingProbability
open scoped Classical

theorem decode_uniform (category : Category) (order : ByteOrder category) :
    (PMF.uniformOfFintype (Fin (byteCount category) → Byte)).map (decode category order) =
      PMF.uniformOfFintype (QuotientRing category) := by
  have he : decode category order = packEquiv category order := by
    funext bytes
    exact (packEquiv_apply category order bytes).symm
  rw [he]
  exact map_uniform_equiv (packEquiv category order)

def splitPacks (b n : Nat) : (Fin (n * b) → Byte) ≃ (Fin n → Fin b → Byte) where
  toFun bytes i j := bytes (finProdFinEquiv (i, j))
  invFun packs j := packs (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  left_inv bytes := by funext j; exact congrArg bytes (finProdFinEquiv.apply_symm_apply j)
  right_inv packs := by funext i j; simp

noncomputable def vectorPackEquiv (category : Category) (order : ByteOrder category) (n : Nat) :
    (Fin (n * byteCount category) → Byte) ≃ (Fin n → QuotientRing category) :=
  (splitPacks (byteCount category) n).trans (Equiv.piCongrRight (fun _ => packEquiv category order))

theorem vectorPackEquiv_apply (category : Category) (order : ByteOrder category) (n : Nat)
    (bytes : Fin (n * byteCount category) → Byte) (i : Fin n) :
    vectorPackEquiv category order n bytes i =
      decode category order (fun j => bytes (finProdFinEquiv (i, j))) :=
  packEquiv_apply category order _

private theorem sample_finiteReader (category : Category) (order : ByteOrder category)
    (n count : Nat) (enough : n * byteCount category ≤ count) (bytes : Fin count → Byte) :
    (sample category order (finiteReader bytes) n count enough).value =
      vectorPackEquiv category order n (fun j => bytes (Fin.castLE enough j)) := by
  funext i
  rw [sample_coordinate, vectorPackEquiv_apply]
  congr 1
  funext j
  have hj : i.val * byteCount category + j.val < count := by
    have hi := i.isLt
    have hj := j.isLt
    have hm := Nat.mul_le_mul_right (byteCount category) hi
    simp only [Nat.succ_mul] at hm
    omega
  simp [finiteReader, hj]
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- n field samples are jointly uniform from an explicit uniform consumed-byte
array. This includes counts larger than the number of bytes actually used. -/
theorem sample_uniform (category : Category) (order : ByteOrder category)
    (n count : Nat) (enough : n * byteCount category ≤ count) :
    (PMF.uniformOfFintype (Fin count → Byte)).map
      (fun bytes => (sample category order (finiteReader bytes) n count enough).value) =
      PMF.uniformOfFintype (Fin n → QuotientRing category) := by
  simp_rw [sample_finiteReader]
  change (PMF.uniformOfFintype (Fin count → Byte)).map
    (vectorPackEquiv category order n ∘ (fun bytes j => bytes (Fin.castLE enough j))) = _
  rw [← PMF.map_comp, UniformVectors.map_uniform_restrict (Fin.castLE enough)
    (Fin.castLE_injective enough)]
  exact map_uniform_equiv (vectorPackEquiv category order n)

private def pairIndex {a b c d : Nat} (ha : a ≤ c) (hb : b ≤ d) :
    Fin a ⊕ Fin b → Fin (c + d)
  | .inl i => ⟨i.val, by have hi := i.isLt; omega⟩
  | .inr j => ⟨c + j.val, by have hj := j.isLt; omega⟩

private theorem pairIndex_injective {a b c d : Nat} (ha : a ≤ c) (hb : b ≤ d) :
    Function.Injective (pairIndex ha hb) := by
  intro x y h
  have hv := congrArg Fin.val h
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (Fin.ext hv)
    | inr j => have hi := i.isLt; simp only [pairIndex] at hv; omega
  | inr i =>
    cases y with
    | inl j => have hj := j.isLt; simp only [pairIndex] at hv; omega
    | inr j => exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel hv))

private noncomputable def pairPackEquiv (category : Category) (order : ByteOrder category)
    (g w : Nat) :
    (Fin (g * byteCount category) ⊕ Fin (w * byteCount category) → Byte) ≃
      (Fin g → QuotientRing category) × (Fin w → QuotientRing category) :=
  (Equiv.sumArrowEquivProdArrow _ _ _).trans
    (Equiv.prodCongr (vectorPackEquiv category order g) (vectorPackEquiv category order w))

private theorem batching_finiteReader (category : Category) (order : ByteOrder category)
    (g w count₁ count₂ : Nat) (h₁ : g * byteCount category ≤ count₁)
    (h₂ : w * byteCount category ≤ count₂) (bytes : Fin (count₁ + count₂) → Byte) :
    (Spec.FieldBytes.expandBatching category order (finiteReader bytes).stream
      g w count₁ count₂ h₁ h₂).value =
      pairPackEquiv category order g w (fun j => bytes (pairIndex h₁ h₂ j)) := by
  rw [(batching_layout category order (finiteReader bytes).stream g w count₁ count₂ h₁ h₂).1]
  apply Prod.ext
  · funext i
    change decode category order _ = vectorPackEquiv category order g _ i
    rw [vectorPackEquiv_apply]
    congr 1
    funext j
    have hj : i.val * byteCount category + j.val < count₁ + count₂ := by
      have hi := i.isLt
      have hj := j.isLt
      have hm := Nat.mul_le_mul_right (byteCount category) hi
      simp only [Nat.succ_mul] at hm
      omega
    simp [finiteReader, hj, pairIndex]
    congr 1
    apply Fin.ext
    simp [Nat.mul_comm, Nat.add_comm]
  · funext i
    change decode category order _ = vectorPackEquiv category order w _ i
    rw [vectorPackEquiv_apply]
    congr 1
    funext j
    have hj : count₁ + (i.val * byteCount category + j.val) < count₁ + count₂ := by
      have hi := i.isLt
      have hj := j.isLt
      have hm := Nat.mul_le_mul_right (byteCount category) hi
      simp only [Nat.succ_mul] at hm
      omega
    simp [finiteReader, hj, pairIndex]
    congr 1
    apply Fin.ext
    simp [Nat.mul_comm, Nat.add_comm]

/-- The two actual sequential batching calls return the uniform law on the
product of both challenge spaces. Their byte ranges are disjoint even when
either call consumes extra unused bytes. The ordering is fixed before sampling. -/
theorem batching_uniform (category : Category) (order : ByteOrder category)
    (g w count₁ count₂ : Nat) (h₁ : g * byteCount category ≤ count₁)
    (h₂ : w * byteCount category ≤ count₂) :
    (PMF.uniformOfFintype (Fin (count₁ + count₂) → Byte)).map
      (fun bytes => (Spec.FieldBytes.expandBatching category order (finiteReader bytes).stream
        g w count₁ count₂ h₁ h₂).value) =
      PMF.uniformOfFintype
        ((Fin g → QuotientRing category) × (Fin w → QuotientRing category)) := by
  simp_rw [batching_finiteReader]
  change (PMF.uniformOfFintype (Fin (count₁ + count₂) → Byte)).map
    (pairPackEquiv category order g w ∘ (fun bytes j => bytes (pairIndex h₁ h₂ j))) = _
  rw [← PMF.map_comp, UniformVectors.map_uniform_restrict (pairIndex h₁ h₂)
    (pairIndex_injective h₁ h₂)]
  exact map_uniform_equiv (pairPackEquiv category order g w)

end SDitH.Proofs.FieldByteProbability
