import SDitH.Spec.PartialKeyGeneration
import SDitH.Proofs.IntegerSamplingTrace
import SDitH.Proofs.KeyGeneration

namespace SDitH.Proofs.PartialKeyGeneration

open Spec.PartialKeyGeneration Spec.DomainSeparation Spec.FieldRepresentation
open Spec.ByteSampling Spec.IntegerSampling Spec.KeyGeneration
open scoped BigOperators

theorem afterSampling_returned_iff {w m d : Nat} (widths : Fin d → Nat)
    (observation : VectorObservation m w) (expanded : Spec.WitnessExpansion.Expanded (ZMod 2) w m) :
    afterSampling widths observation = .returned expanded ↔
      ∃ positions cursor, observation = .returned positions cursor ∧
        Spec.WitnessExpansion.expandAfterSampling widths (fun i => positions[i]) = expanded := by
  cases observation <;> simp [afterSampling]

theorem afterSampling_trace {w m d : Nat} (widths : Fin d → Nat)
    (observation : VectorObservation m w) :
    expansionTrace (afterSampling widths observation) = afterSamplingTrace widths (vectorTrace observation) := by
  cases observation <;> rfl

/-- Correspondence covers every rejected candidate as well as the first
undefined read or a return. It requires an actual successful finite PRG run. -/
theorem expansion_trace_from_run (category : Category) (variant : Grinding) (size : Spec.PRG.BlockSize)
    (seed : Bits (width category)) (nbytes : Nat) (out : Vector Byte nbytes)
    (hr : Spec.PRG.run category variant size seed none none nbytes = some out)
    {w m d : Nat} (widths : Fin d → Nat) (hm : 0 < m) (binding : Option Nat)
    (fuel : Nat) (within : 4 * fuel ≤ nbytes) :
    expansionTrace (expandFromReader (w := w) widths hm binding fuel
      (finiteReader (count := nbytes) (fun i => out[i]))) =
      expansionTrace (expandWithBinding category seed widths hm binding fuel) := by
  simp only [expandWithBinding, expandFromReader, afterSampling_trace]
  exact congrArg (afterSamplingTrace widths)
    (IntegerSampling.sampleVector_trace_from_run category variant size seed nbytes out hr m hm w binding fuel within)

theorem expansion_returned_weight_length {w m d : Nat} (widths : Fin d → Nat) (hm : 0 < m)
    (binding : Option Nat) (fuel : Nat) (src : Reader)
    (expanded : Spec.WitnessExpansion.Expanded (ZMod 2) w m)
    (h : expandFromReader widths hm binding fuel src = .returned expanded) :
    Spec.hammingWeight expanded.solution = w ∧ expanded.witness.length = w * ∑ j, widths j := by
  obtain ⟨positions, _, _, rfl⟩ := (afterSampling_returned_iff widths _ expanded).mp h
  exact ⟨WitnessExpansion.expansion_weight widths (fun i => positions[i]),
    WitnessExpansion.expansion_witness_length widths (fun i => positions[i])⟩

theorem expansion_returned_stable {w m d : Nat} (widths : Fin d → Nat) (hm : 0 < m)
    (binding : Option Nat) (fuel extra : Nat) (src : Reader)
    (expanded : Spec.WitnessExpansion.Expanded (ZMod 2) w m)
    (h : expandFromReader widths hm binding fuel src = .returned expanded) :
    expandFromReader widths hm binding (fuel + extra) src = .returned expanded := by
  obtain ⟨positions, cursor, hs, he⟩ := (afterSampling_returned_iff widths _ expanded).mp h
  apply (afterSampling_returned_iff widths _ expanded).mpr
  exact ⟨positions, cursor, IntegerSampling.observeVector_returned_stable m hm w binding fuel extra
    ⟨[], by simp, src⟩ positions cursor hs, he⟩

theorem expandFromReader_unbound_no_return {w m d : Nat} (widths : Fin d → Nat) (hm : 0 < m)
    (hw : 0 < w) (fuel : Nat) (src : Reader)
    (expanded : Spec.WitnessExpansion.Expanded (ZMod 2) w m) :
    expandFromReader widths hm none fuel src ≠ .returned expanded := by
  intro h
  obtain ⟨positions, cursor, hs, _⟩ := (afterSampling_returned_iff widths _ expanded).mp h
  exact IntegerSampling.sampleVector_unbound_no_return m hm w fuel hw src positions cursor hs

/-- Table-3 ranges need rejection sampling; no power-of-two shortcut is used
in this theorem, which applies to every positive range and every PRG stream. -/
theorem expand_no_return (category : Category) {w m d : Nat} (seed : Bits (width category))
    (widths : Fin d → Nat) (hm : 0 < m) (hw : 0 < w) (fuel : Nat)
    (expanded : Spec.WitnessExpansion.Expanded (ZMod 2) w m) :
    expand category seed widths hm fuel ≠ .returned expanded :=
  expandFromReader_unbound_no_return widths hm hw fuel _ expanded

theorem afterExpansion_returned_iff (category : Category) {r k w m : Nat}
    (seed : Bits (width category)) (count : Nat) (enough : r ≤ 8 * count)
    (xA : Option (Fin (r + k) → ZMod 2)) (observation : ExpansionObservation w m)
    (key : SecretKey (width category) r) :
    afterExpansion category seed count enough xA observation = .returned key ↔
      ∃ expanded, observation = .returned expanded ∧
        finishWithBinding (⟨seed, expanded, expandMatrix category seed r k count enough⟩ :
          Prefix category r k w m) xA = some key := by
  cases observation with
  | pending state => simp [afterExpansion]
  | undefinedIntegerAssignment state candidate => simp [afterExpansion]
  | returned expanded =>
    simp only [afterExpansion, ExpansionObservation.returned.injEq]
    cases hf : finishWithBinding (⟨seed, expanded, expandMatrix category seed r k count enough⟩ :
      Prefix category r k w m) xA <;> simp [hf]

section KeyCaller

variable (category : Category) {r k w m d : Nat}
  (secretSeed publicSeed : Bits (width category)) (widths : Fin d → Nat) (hm : 0 < m)
  (integerBinding : Option Nat) (xA : Option (Fin (r + k) → ZMod 2))
  (fuel count : Nat) (enough : r ≤ 8 * count)

/-- Exact returned-key provenance, with the real sampler, post-position
expansion and matrix/syndrome computation exposed as run equations. -/
theorem runWithBindings_returned_iff (key : SecretKey (width category) r) :
    runWithBindings (k := k) (w := w) category secretSeed publicSeed widths hm integerBinding xA fuel count enough =
      .returned key ↔
      ∃ positions cursor,
        sampleVectorWithBinding m hm w integerBinding fuel
          (Spec.PRG.reader category secretSeed (fun _ => false)) = .returned positions cursor ∧
        finishWithBinding (prepareAfterPositions (k := k) category publicSeed widths
          (fun i => positions[i]) count enough) xA = some key := by
  rw [runWithBindings, afterExpansion_returned_iff]
  constructor
  · rintro ⟨expanded, he, hk⟩
    obtain ⟨positions, cursor, hs, rfl⟩ := (afterSampling_returned_iff widths _ expanded).mp he
    exact ⟨positions, cursor, hs, hk⟩
  · rintro ⟨positions, cursor, hs, hk⟩
    refine ⟨_, ?_, hk⟩
    exact (afterSampling_returned_iff widths _ _).mpr ⟨positions, cursor, hs, rfl⟩

theorem runWithBindings_integer_unbound (hw : 0 < w) (key : SecretKey (width category) r) :
    runWithBindings (k := k) (w := w) category secretSeed publicSeed widths hm none xA fuel count enough ≠ .returned key := by
  intro h
  obtain ⟨positions, cursor, hs, _⟩ := (runWithBindings_returned_iff category secretSeed publicSeed
    widths hm none xA fuel count enough key).mp h
  exact IntegerSampling.sampleVector_unbound_no_return m hm w fuel hw _ positions cursor hs

theorem runWithBindings_xA_unbound (key : SecretKey (width category) r) :
    runWithBindings (k := k) (w := w) category secretSeed publicSeed widths hm integerBinding none fuel count enough ≠
      .returned key := by
  intro h
  obtain ⟨_, _, _, hk⟩ := (runWithBindings_returned_iff category secretSeed publicSeed widths hm
    integerBinding none fuel count enough key).mp h
  simp [finishWithBinding] at hk

theorem run_no_return (key : SecretKey (width category) r) :
    run (k := k) (w := w) category secretSeed publicSeed widths hm fuel count enough ≠ .returned key :=
  runWithBindings_xA_unbound category secretSeed publicSeed widths hm none fuel count enough key

/-- An actually returned key has the proved weight property. Its SD validity
still requires exactly the missing x_A relation, not an assumed equality x_A=x. -/
theorem issued_key_condition (lengthEq : r + k = w * m)
    (boundXA : Fin (r + k) → ZMod 2) (key : SecretKey (width category) r)
    (h : runWithBindings (k := k) (w := w) category secretSeed publicSeed widths hm integerBinding (some boundXA)
      fuel count enough = .returned key) :
    ∃ positions : Vector (Fin m) w,
      let state := prepareAfterPositions (k := k) category publicSeed widths (fun i => positions[i]) count enough
      Spec.hammingWeight (generatedSolution state lengthEq) = w ∧
      (Spec.SDSolution (instanceOf state.matrix key.publicPart.syndrome) w (generatedSolution state lengthEq) ↔
        (Spec.Batching.systematicLeft state.matrix).mulVec (boundXA - generatedSolution state lengthEq) = 0) := by
  obtain ⟨positions, _, _, hk⟩ := (runWithBindings_returned_iff category secretSeed publicSeed widths hm
    integerBinding (some boundXA) fuel count enough key).mp h
  exact ⟨positions, KeyGeneration.generated_solution_weight category publicSeed widths
      (fun i => positions[i]) count enough lengthEq,
    KeyGeneration.issued_key_solution_iff category publicSeed widths (fun i => positions[i])
      count enough lengthEq boundXA key hk⟩

end KeyCaller

/-- Independent seed expansion remains independent even when the witness
output is a pending/fault observation. Neither marginal is presumed uniform. -/
theorem expansion_seed_law (category : Category) {r k w m d : Nat}
    (widths : Fin d → Nat) (hm : 0 < m) (fuel count : Nat) (enough : r ≤ 8 * count) :
    (sampleSeeds (width category)).map (fun seeds =>
      (expand (w := w) category seeds.1 widths hm fuel, expandMatrix category seeds.2 r k count enough)) =
      ((PMF.uniformOfFintype (Bits (width category))).map (fun seed => expand (w := w) category seed widths hm fuel)).bind
        (fun witness => ((PMF.uniformOfFintype (Bits (width category))).map
          (fun seed => expandMatrix category seed r k count enough)).map (fun matrix => (witness, matrix))) :=
  KeyGeneration.expanded_seed_law (width category)
    (fun seed => expand (w := w) category seed widths hm fuel)
    (fun seed => expandMatrix category seed r k count enough)

theorem keygen_returned_zero (category : Category) {r k w m d : Nat}
    (widths : Fin d → Nat) (hm : 0 < m) (fuel count : Nat) (enough : r ≤ 8 * count)
    (key : SecretKey (width category) r) :
    keygen (k := k) (w := w) category widths hm fuel count enough (.returned key) = 0 := by
  classical
  rw [keygen, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro seeds
  exact if_neg (fun h => run_no_return category seeds.1 seeds.2 widths hm fuel count enough key h.symm)

theorem encodedKeygen_returned_zero (category : Category) {r k w m d : Nat}
    (encoding : Serialization (width category) r) (widths : Fin d → Nat) (hm : 0 < m)
    (fuel count : Nat) (enough : r ≤ 8 * count) (keys : List Bool × List Bool) :
    encodedKeygen (k := k) (w := w) category encoding widths hm fuel count enough (.returned keys) = 0 := by
  classical
  rw [encodedKeygen, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro observation
  cases observation with
  | witnessPending state => simp [mapReturned]
  | undefinedIntegerAssignment state candidate => simp [mapReturned]
  | undefinedXA state => simp [mapReturned]
  | returned key => simp [mapReturned, keygen_returned_zero]

theorem table3_sampling_ranges :
    (Spec.RSDParameters.categoryI.n / Spec.RSDParameters.categoryI.w = 185) ∧
    (Spec.RSDParameters.categoryIII.n / Spec.RSDParameters.categoryIII.w = 252) ∧
    (Spec.RSDParameters.categoryV.n / Spec.RSDParameters.categoryV.w = 191) ∧
    (∀ p ∈ [Spec.RSDParameters.categoryI, Spec.RSDParameters.categoryIII, Spec.RSDParameters.categoryV],
      0 < p.w ∧ 0 < p.n / p.w ∧ p.n / p.w ≤ Spec.IntegerSampling.wordBound) := by decide

end SDitH.Proofs.PartialKeyGeneration
