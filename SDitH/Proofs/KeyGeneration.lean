import SDitH.Spec.KeyGeneration
import SDitH.Proofs.PRGSampling
import SDitH.Proofs.WitnessExpansion
import SDitH.Proofs.UniformVectors

namespace SDitH.Proofs.KeyGeneration

open Spec.DomainSeparation Spec.FieldRepresentation Spec.KeyGeneration
open scoped BigOperators ENNReal

theorem sampleSeeds_uniform (lambda : Nat) :
    sampleSeeds lambda = PMF.uniformOfFintype (Bits lambda × Bits lambda) :=
  UniformVectors.uniform_pair

theorem sampleSeeds_probability (lambda : Nat) (secret publicPart : Bits lambda) :
    sampleSeeds lambda (secret, publicPart) = ((2 : ℝ≥0∞) ^ (2 * lambda))⁻¹ := by
  rw [sampleSeeds_uniform, PMF.uniformOfFintype_apply]
  simp only [Bits, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_add, two_mul]

/-- Deterministic expansions of the independently sampled seeds are
independent as distributions. Their individual distributions are the actual
pushforwards, not presumed uniform matrices or uniform witnesses. -/
theorem expanded_seed_law {A B : Type*} (lambda : Nat) (expandSecret : Bits lambda → A)
    (expandPublic : Bits lambda → B) :
    (sampleSeeds lambda).map (fun seeds => (expandSecret seeds.1, expandPublic seeds.2)) =
      ((PMF.uniformOfFintype (Bits lambda)).map expandSecret).bind (fun secret =>
        ((PMF.uniformOfFintype (Bits lambda)).map expandPublic).map (fun publicPart => (secret, publicPart))) := by
  simp only [sampleSeeds, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]

theorem expandMatrix_coordinate (category : Category) (seed : Bits (width category))
    (r k count : Nat) (enough : r ≤ 8 * count) (i : Fin r) (j : Fin k) :
    expandMatrix category seed r k count enough i j =
      Spec.BLCCommit.bitField ((Spec.PRG.stream category seed (fun _ => false)
        (j.val * count + i.val / 8)).val.testBit (i.val % 8)) := by
  rw [expandMatrix, ByteSampling.expandHColumns_coordinate]

theorem expandMatrix_from_run (category : Category) (variant : Grinding) (size : Spec.PRG.BlockSize)
    (seed : Bits (width category)) (nbytes : Nat) (out : Vector Byte nbytes)
    (hr : Spec.PRG.run category variant size seed none none nbytes = some out)
    (r k count : Nat) (within : k * count ≤ nbytes) (enough : r ≤ 8 * count) :
    expandMatrix category seed r k count enough = fun i j =>
      Spec.BLCCommit.bitField ((Spec.ByteSampling.expandHColumns
        (Spec.ByteSampling.finiteReader (count := nbytes) (fun p => out[p])).stream r k count enough).value i j) := by
  have he := PRGSampling.expandHColumns_from_run category variant size seed nbytes out hr r k count within enough
  funext i j
  exact congrArg Spec.BLCCommit.bitField (congrFun (congrFun he.symm i) j)

theorem prepared_weight_and_length (category : Category) {r k w m d : Nat}
    (seed : Bits (width category)) (widths : Fin d → Nat) (positions : Fin w → Fin m)
    (count : Nat) (enough : r ≤ 8 * count) :
    let prepared := prepareAfterPositions (k := k) category seed widths positions count enough
    Spec.hammingWeight prepared.expanded.solution = w ∧
      prepared.expanded.witness.length = w * ∑ j, widths j :=
  ⟨WitnessExpansion.expansion_weight widths positions, WitnessExpansion.expansion_witness_length widths positions⟩

theorem hammingWeight_cast {a b : Nat} (h : a = b) (x : Fin b → ZMod 2) :
    Spec.hammingWeight (fun i : Fin a => x (Fin.cast h i)) = Spec.hammingWeight x := by
  subst b
  rfl

theorem generated_solution_weight (category : Category) {r k w m d : Nat}
    (seed : Bits (width category)) (widths : Fin d → Nat) (positions : Fin w → Fin m)
    (count : Nat) (enough : r ≤ 8 * count) (lengthEq : r + k = w * m) :
    Spec.hammingWeight (generatedSolution
      (prepareAfterPositions category seed widths positions count enough) lengthEq) = w := by
  unfold generatedSolution
  rw [hammingWeight_cast]
  exact WitnessExpansion.expansion_weight widths positions

theorem instanceOf_solution_iff {r k w : Nat} (H' : Matrix (Fin r) (Fin k) (ZMod 2))
    (y : Fin r → ZMod 2) (x : Fin (r + k) → ZMod 2) :
    Spec.SDSolution (instanceOf H' y) w x ↔
      (Spec.Batching.systematicLeft H').mulVec x = y ∧ Spec.hammingWeight x = w := by
  constructor
  · rintro ⟨he, hw⟩
    refine ⟨?_, hw⟩
    funext i
    exact congrFun he (Fin.cast (Nat.add_sub_cancel r k).symm i)
  · rintro ⟨he, hw⟩
    refine ⟨?_, hw⟩
    funext i
    exact congrFun he (Fin.cast (Nat.add_sub_cancel r k) i)

theorem systematicLeft_mulVec {K : Type*} [CommRing K] {r k : Nat}
    (H' : Matrix (Fin r) (Fin k) K) (x : Fin (r + k) → K) (i : Fin r) :
    (Spec.Batching.systematicLeft H').mulVec x i =
      x (i.castAdd k) + H'.mulVec (fun j => x (j.natAdd r)) i := by
  classical
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Spec.Batching.systematicLeft]

theorem systematicRight_mulVec {K : Type*} [CommRing K] {r k : Nat}
    (H' : Matrix (Fin r) (Fin k) K) (x : Fin (k + r) → K) (i : Fin r) :
    (systematicRight H').mulVec x i =
      H'.mulVec (fun j => x (j.castAdd r)) i + x (i.natAdd k) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, systematicRight]

theorem systematicLeft_surjective {K : Type*} [CommRing K] {r k : Nat}
    (H' : Matrix (Fin r) (Fin k) K) : Function.Surjective (Spec.Batching.systematicLeft H').mulVec := by
  intro y
  refine ⟨Fin.addCases y (fun _ => 0), ?_⟩
  funext i
  rw [systematicLeft_mulVec]
  simp only [Fin.addCases_left, Fin.addCases_right]
  simp [Matrix.mulVec, dotProduct]

/-- The prose and code orientations agree after this explicit block swap.
It is not inserted into the submitted algorithm. -/
theorem orientations_after_swap {K : Type*} [CommRing K] {r k : Nat}
    (H' : Matrix (Fin r) (Fin k) K) (x : Fin (r + k) → K) :
    (systematicRight H').mulVec (swapBlocks x) = (Spec.Batching.systematicLeft H').mulVec x := by
  funext i
  rw [systematicRight_mulVec, systematicLeft_mulVec]
  simp only [swapBlocks, Fin.addCases_left, Fin.addCases_right]
  exact add_comm _ _

/-- With the same coordinate order the two source formulas can disagree.
This small matrix is an algebraic counterexample, not a PRG-generated key. -/
theorem orientations_differ :
    let H' : Matrix (Fin 1) (Fin 1) (ZMod 2) := fun _ _ => 0
    let x : Fin 2 → ZMod 2 := ![1, 0]
    (Spec.Batching.systematicLeft H').mulVec x ≠ (systematicRight H').mulVec x := by
  decide

theorem unbound_xA {category : Category} {r k w m : Nat}
    (state : Prefix category r k w m) : finishWithBinding state none = none := rfl

theorem bound_xA {category : Category} {r k w m : Nat}
    (state : Prefix category r k w m) (xA : Fin (r + k) → ZMod 2) :
    finishWithBinding state (some xA) =
      some ⟨⟨state.publicSeed, (Spec.Batching.systematicLeft state.matrix).mulVec xA⟩,
        state.expanded.witness⟩ := rfl

/-- The exact missing relation needed for the generated vector to satisfy
the syndrome assigned from x_A. Equality x_A=x is sufficient but not assumed;
the actual condition is equality modulo the matrix kernel. -/
theorem syndrome_agreement_iff {K : Type*} [CommRing K] {r k : Nat}
    (H' : Matrix (Fin r) (Fin k) K) (x xA : Fin (r + k) → K) :
    (Spec.Batching.systematicLeft H').mulVec x = (Spec.Batching.systematicLeft H').mulVec xA ↔
      (Spec.Batching.systematicLeft H').mulVec (xA - x) = 0 := by
  rw [Matrix.mulVec_sub, sub_eq_zero, eq_comm]

/-- A returned typed key and the actual expanded witness satisfy SD exactly
when the undefined x_A binding differs from the generated vector by a kernel
element. The exact weight is proved from Algorithm 1, not assumed in a contract. -/
theorem issued_key_solution_iff (category : Category) {r k w m d : Nat}
    (seed : Bits (width category)) (widths : Fin d → Nat) (positions : Fin w → Fin m)
    (count : Nat) (enough : r ≤ 8 * count) (lengthEq : r + k = w * m)
    (xA : Fin (r + k) → ZMod 2) (key : SecretKey (width category) r)
    (hk : finishWithBinding (prepareAfterPositions category seed widths positions count enough) (some xA) = some key) :
    let state := prepareAfterPositions (k := k) category seed widths positions count enough
    Spec.SDSolution (instanceOf state.matrix key.publicPart.syndrome) w (generatedSolution state lengthEq) ↔
      (Spec.Batching.systematicLeft state.matrix).mulVec (xA - generatedSolution state lengthEq) = 0 := by
  dsimp only
  have he := Option.some.inj ((bound_xA _ xA).symm.trans hk)
  subst key
  rw [instanceOf_solution_iff, generated_solution_weight category seed widths positions count enough lengthEq]
  constructor
  · intro h
    exact (syndrome_agreement_iff _ _ _).mp h.1
  · intro h
    exact ⟨(syndrome_agreement_iff _ _ _).mpr h, rfl⟩

theorem secret_initialization_public (category : Category) {r k : Nat}
    (key : SecretKey (width category) r) (count : Nat) (enough : r ≤ 8 * count) :
    (initializeSecret (k := k) category key count enough).publicPart =
      initializePublic category key.publicPart count enough := rfl

theorem initialized_matrix_matches_generation (category : Category) {r k w m d : Nat}
    (seed : Bits (width category)) (widths : Fin d → Nat) (positions : Fin w → Fin m)
    (count : Nat) (enough : r ≤ 8 * count) (xA : Fin (r + k) → ZMod 2)
    (key : SecretKey (width category) r)
    (hk : finishWithBinding (prepareAfterPositions category seed widths positions count enough) (some xA) = some key) :
    (initializeSecret (k := k) category key count enough).publicPart.matrix =
      (prepareAfterPositions (k := k) category seed widths positions count enough).matrix := by
  have he := Option.some.inj ((bound_xA _ xA).symm.trans hk)
  subst key
  rfl

end SDitH.Proofs.KeyGeneration
