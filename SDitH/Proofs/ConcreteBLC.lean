import SDitH.Spec.ConcreteBLC
import SDitH.Proofs.BLCCommit
import SDitH.Proofs.PRGSampling
import SDitH.Proofs.HashPrimitives
import SDitH.Spec.VariantParameters

namespace SDitH.Proofs.ConcreteBLC

open Spec.DomainSeparation Spec.FieldRepresentation Spec.ConcreteBLC

theorem executionStream_in_range (category : Category) (variant : Grinding)
    (seed salt : Bits (width category)) (execution : Nat) (he : execution < 256) :
    executionStream category variant seed salt execution =
      Spec.PRG.stream category seed (tweakSalt variant salt (Spec.PRG.shiftedTweak ⟨execution, he⟩) false) := by
  rw [executionStream, dif_pos he]

/-- Every execution in the main parameter tables uses the defined branch.
The same numerical bound is checked for the three tabulated variants. -/
theorem submitted_tweak_ranges :
    (∀ p ∈ Spec.hashProofParameters, p.tau ≤ 256) ∧
    (∀ p ∈ Spec.cipherProofParameters, p.tau ≤ 256) ∧
    (∀ p ∈ Spec.VariantParameters.table8, p.proof.tau ≤ 256) ∧
    (∀ p ∈ Spec.VariantParameters.table9, p.proof.tau ≤ 256) ∧
    (∀ p ∈ Spec.VariantParameters.table10, p.proof.tau ≤ 256) := by
  decide

theorem execution_tweak_valid {tau : Nat} (h : tau ≤ 256) (e : Fin tau) : e.val < 256 :=
  e.isLt.trans_le h

/-- The prepared stream is exactly a finite Algorithm-6 result wherever
the literal byte assignment is well-formed and the explicit block-size value
allocates enough bytes. Category III is intentionally excluded. -/
theorem executionStream_finite (category : Category) (hc : category ≠ .iii)
    (variant : Grinding) (size : Spec.PRG.BlockSize)
    (hsize : size.bits ≤ Spec.CipherPrimitives.ciphertextWidth category)
    (seed salt : Bits (width category)) (execution : Nat) (he : execution < 256) (nbytes : Nat) :
    Spec.PRG.run category variant size seed (some salt) (some ⟨execution, he⟩) nbytes =
      some (Vector.ofFn fun j : Fin nbytes => executionStream category variant seed salt execution j.val) := by
  rw [executionStream_in_range category variant seed salt execution he]
  exact PRG.run_nonIII category hc variant size hsize seed (some salt) (some ⟨execution, he⟩)
    nbytes _ rfl

theorem bavc_primitives (category : Category) (variant : Grinding) {tau kappa s wit rnd : Nat}
    (encoding : Serialization tau kappa s) (leafCount : Nat) :
    Spec.SeedPrimitives.bavcPrimitives leafCount (primitives category variant (wit := wit) (rnd := rnd) encoding).grinding
      (primitives category variant (wit := wit) (rnd := rnd) encoding).encStar
      (primitives category variant (wit := wit) (rnd := rnd) encoding).hash =
      Spec.CipherPrimitives.bavcPrimitives category leafCount variant := rfl

/-- The outer transcript layout is fixed even while the vector/matrix wire
encodings remain supplied functions. Witness correction is included exactly
as in Algorithm 10 line 24; it is not silently removed to match Algorithm 12. -/
theorem hash_inputs (category : Category) (variant : Grinding) {tau kappa s wit rnd : Nat}
    (encoding : Serialization tau kappa s)
    (aux : Spec.BLCCommit.AuxHashInput (width category) tau (s + (wit + rnd)))
    (lines : Spec.BLCCommit.LinesHashInput (width category) tau kappa s wit) :
    (primitives category variant encoding).hashAux aux =
      Spec.SHAKE.hash category (Spec.BAVC.byteBits 2 ++
        (List.ofFn aux.commitment ++ (List.ofFn fun j => encoding.vector (aux.corrections j)).flatten)) ∧
    (primitives category variant (rnd := rnd) encoding).hashLines lines =
      Spec.SHAKE.hash category (Spec.BAVC.byteBits 3 ++
        (List.ofFn lines.auxiliary ++ encoding.vector lines.plain ++ encoding.base lines.base ++
          encoding.vector lines.witnessCorrection)) := ⟨rfl, rfl⟩

theorem randomTable_coordinate (category : Category) (variant : Grinding) {tau kappa s wit rnd : Nat}
    (encoding : Serialization tau kappa s) (ht : tau ≤ 256) (salt : Bits (width category))
    (seeds : Fin tau → Fin (2 ^ kappa) → Bits (width category))
    (count : Nat) (enough : s + (wit + rnd) ≤ 8 * count)
    (e : Fin tau) (i : Fin (2 ^ kappa)) (j : Fin (s + (wit + rnd))) :
    Spec.BLCCommit.randomTable (primitives category variant encoding) salt seeds count enough e i j =
      Spec.BLCCommit.bitField ((Spec.PRG.stream category (seeds e i)
        (tweakSalt variant salt (Spec.PRG.shiftedTweak ⟨e.val, execution_tweak_valid ht e⟩) false)
        (j.val / 8)).val.testBit (j.val % 8)) := by
  rw [BLCCommit.randomTable_coordinate]
  change Spec.BLCCommit.bitField ((executionStream category variant (seeds e i) salt e.val _).val.testBit _) = _
  rw [executionStream_in_range category variant (seeds e i) salt e.val (execution_tweak_valid ht e)]

/-- Each row in the folding table agrees with binary sampling of an actual
successful finite PRG result. The premise is the actual run equation, not a
PRG correctness or randomness assumption. -/
theorem randomTable_from_run (category : Category) (variant : Grinding) (size : Spec.PRG.BlockSize)
    {tau kappa s wit rnd : Nat} (encoding : Serialization tau kappa s) (ht : tau ≤ 256)
    (salt : Bits (width category)) (seeds : Fin tau → Fin (2 ^ kappa) → Bits (width category))
    (count : Nat) (enough : s + (wit + rnd) ≤ 8 * count)
    (bytes : Fin tau → Fin (2 ^ kappa) → Vector Byte count)
    (hr : ∀ e i, Spec.PRG.run category variant size (seeds e i) (some salt)
      (some ⟨e.val, execution_tweak_valid ht e⟩) count = some (bytes e i)) :
    Spec.BLCCommit.randomTable (primitives category variant encoding) salt seeds count enough =
      fun e i j => Spec.BLCCommit.bitField ((Spec.ByteSampling.sampleBinary
        (Spec.ByteSampling.finiteReader (count := count) (fun k => (bytes e i)[k]))
        (s + (wit + rnd)) count enough).value j) := by
  funext e i j
  rw [randomTable_coordinate category variant encoding ht salt seeds count enough]
  have hj : j.val / 8 < count := by have := j.isLt; omega
  have ho := PRG.run_output_coordinate category variant size (seeds e i) (some salt)
    (some ⟨e.val, execution_tweak_valid ht e⟩) count (bytes e i) _ rfl (hr e i) ⟨j.val / 8, hj⟩
  simp only [Spec.ByteSampling.sampleBinary, Spec.ByteSampling.readBytes, Spec.ByteSampling.finiteReader,
    Nat.zero_add, dif_pos hj, Fin.getElem_fin]
  rw [show (bytes e i)[j.val / 8] = _ from ho]

/-- The consistency matrix's coordinates are bits of the actual submitted
SHAKE instance. Whole-byte advancement is retained between row calls. -/
theorem consistency_coordinate (category : Category) (variant : Grinding) {tau kappa s wit rnd : Nat}
    (encoding : Serialization tau kappa s) (digest : Bits (2 * width category))
    (B ell count : Nat) (enough : ell ≤ 8 * count) (i : Fin (width category + B)) (j : Fin ell) :
    (Spec.ByteSampling.expandConsistency
      ((primitives category variant (wit := wit) (rnd := rnd) encoding).xof digest)
      (width category) B ell count enough).value i j =
      Spec.SHAKE.bitStream category (List.ofFn digest) (8 * (i.val * count) + j.val) := by
  rw [ByteSampling.expandConsistency_coordinate]
  change (Spec.SHAKE.byteStream category (List.ofFn digest) (i.val * count + j.val / 8)).val.testBit _ = _
  rw [SHAKE.byteStream_bit category (List.ofFn digest) _ ⟨j.val % 8, Nat.mod_lt _ (by decide)⟩]
  congr 1
  dsimp
  omega

end SDitH.Proofs.ConcreteBLC
