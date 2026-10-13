import SDitH.Proofs.FieldRepresentation
import SDitH.Proofs.BLCArithmetic
import SDitH.Proofs.Batching
import SDitH.Spec.Parameters

namespace SDitH.Proofs.ConcreteEncodings

open Spec.FieldRepresentation
open scoped BigOperators

/-- The actual psi map is injective whenever its tau*kappa input bits fit in
the submitted basis. This proves the property previously left at a field boundary. -/
theorem psi_injective (category : Category) {tau kappa : Nat}
    (hsize : tau * kappa ≤ width category) :
    Function.Injective (Spec.BLC.psi (K := ZMod 2) (tau := tau) (kappa := kappa)
      (generator category)) := by
  let index : Fin tau × Fin kappa → Fin (width category) := fun p =>
    ⟨p.1.val * kappa + p.2.val, by
      have hi := p.1.isLt
      have hj := p.2.isLt
      have hm := Nat.mul_le_mul_right kappa hi
      rw [Nat.succ_mul] at hm
      omega⟩
  have hinj : Function.Injective index := by
    intro p q h
    have hv := congrArg Fin.val h
    dsimp [index] at hv
    apply finProdFinEquiv.injective
    apply Fin.ext
    simpa [finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using hv
  intro a b hab
  have he : (∑ p : Fin tau × Fin kappa,
      algebraMap (ZMod 2) (QuotientRing category) (a p.1 p.2) * generator category ^ (index p).val) =
      ∑ p : Fin tau × Fin kappa,
      algebraMap (ZMod 2) (QuotientRing category) (b p.1 p.2) * generator category ^ (index p).val := by
    simpa only [BLC.psi_formula, Fintype.sum_prod_type, index] using hab
  have hc := FieldRepresentation.indexed_power_sum_injective category index hinj he
  funext e j
  exact congrFun hc (e, j)

theorem packBlock_eq_encode (category : Category) {r : Nat}
    (block : Fin (Spec.Batching.blockCount r (width category))) (v : Fin r → ZMod 2) :
    Spec.Batching.packBlockLinear (lambda := width category) (generator category) block v =
      encodeCoefficients category (fun j : Fin (width category) =>
        if h : block.val * width category + j.val < r then
          v ⟨block.val * width category + j.val, h⟩ else 0) := by
  rw [Batching.packBlock_formula]
  unfold encodeCoefficients
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h <;> simp [h, mul_comm]

theorem containing_block_bound {r lambda : Nat} (hl : 0 < lambda) (i : Fin r) :
    i.val / lambda < Spec.Batching.blockCount r lambda := by
  apply (Nat.div_lt_iff_lt_mul hl).mpr
  have hm := Nat.mod_lt (r + lambda - 1) hl
  have he := Nat.mod_add_div (r + lambda - 1) lambda
  have hi := i.isLt
  unfold Spec.Batching.blockCount
  rw [Nat.mul_comm]
  omega

/-- The source's full zero-padded Phi embedding is injective in each exact
Table-2 quotient, including a partial final block. -/
theorem packVector_injective (category : Category) {r : Nat} :
    Function.Injective (Spec.Batching.packVector (K := ZMod 2) (r := r)
      (lambda := width category) (generator category)) := by
  have hl : 0 < width category := lt_of_lt_of_le (by decide) (FieldRepresentation.width_ge_128 category)
  intro a b hab
  funext i
  let block : Fin (Spec.Batching.blockCount r (width category)) :=
    ⟨i.val / width category, containing_block_bound hl i⟩
  let column : Fin (width category) := ⟨i.val % width category, Nat.mod_lt _ hl⟩
  have he := congrFun hab block
  change Spec.Batching.packBlockLinear (generator category) block a =
    Spec.Batching.packBlockLinear (generator category) block b at he
  rw [packBlock_eq_encode, packBlock_eq_encode] at he
  have hc := FieldRepresentation.encodeCoefficients_injective category le_rfl he
  have hi : block.val * width category + column.val = i.val := by
    dsimp [block, column]
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div i.val (width category)
  have hb : block.val * width category + column.val < r := by rw [hi]; exact i.isLt
  have hv := congrFun hc column
  simp only [dif_pos hb] at hv
  have heq : (⟨block.val * width category + column.val, hb⟩ : Fin r) = i := Fin.ext hi
  simpa only [heq] using hv

/-- Both submitted proof-parameter tables satisfy the input-size condition of
psi_injective. Category order is the two rows per security level in Tables 4/5. -/
theorem submitted_merge_dimensions :
    let categories : List Category := [.i, .i, .iii, .iii, .v, .v]
    (∀ row ∈ categories.zip Spec.hashProofParameters,
      row.2.tau * row.2.kappa ≤ width row.1) ∧
    (∀ row ∈ categories.zip Spec.cipherProofParameters,
      row.2.tau * row.2.kappa ≤ width row.1) := by decide

/-- The actual Table-3 arities satisfy the hypotheses of the packed unitary
proof. This is separate from their inconsistent tensor-size equation. -/
theorem submitted_unitary_dimensions :
    ∀ p ∈ [Spec.RSDParameters.categoryI, Spec.RSDParameters.categoryIII, Spec.RSDParameters.categoryV],
      p.arities.length ≤ 4 ∧ ∀ a ∈ p.arities, a - 1 ≤ 3 := by decide

end SDitH.Proofs.ConcreteEncodings
