import SDitH.Proofs.TableSupport
import SDitH.Proofs.ProductOracle
import SDitH.Proofs.TailLinesDigest

/-! Hitting a supported table through an injective map, and the tail's
output at a fresh lines input. A uniform digest sent through an injective
map into the inputs of a table supported by n inputs is stored with
probability at most n over the digest count. At a fresh lines input the
tail's committed result, through any function, is distributed as that
function of the committed result at a uniform lines answer. -/

namespace SDitH.Proofs.HitCount

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.HashCipherTrace Spec.RandomOracle
open Spec.SlopeConsistencyGame (Out)
open TableSupport CommitDecomposition RunBind TailLinesDigest
open scoped Classical ENNReal

noncomputable section

section Counting

variable {Input D M Output : Type*} [Fintype D] [Nonempty D] [Fintype M] [Nonempty M]

/-- A uniform digest through an injective map hits a table supported by n
inputs with probability at most n over the digest count. -/
theorem uniform_hit_le (table : Input → Option Output) (f : D → Input) (hf : Function.Injective f) {n : Nat}
    (h : Supported table n) :
    ((PMF.uniformOfFintype (D × M)).map fun lines => decide (table (f lines.1) ≠ none)) true ≤
      (n : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹ := by
  obtain ⟨s, hs, hmem⟩ := h
  set T : Finset D := Finset.univ.filter (fun d => table (f d) ≠ none) with hT
  have hfun : (fun lines : D × M => decide (table (f lines.1) ≠ none)) = fun lines => decide (lines.1 ∈ T) := by
    funext lines
    simp [hT]
  rw [hfun, ProductOracle.uniform_fst_mem_mass T]
  refine mul_le_mul' ((Nat.cast_le (α := ℝ≥0∞)).mpr ?_) le_rfl
  have himage : T.image f ⊆ s := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact hmem (f d) (by simpa [hT] using hd)
  calc T.card = (T.image f).card := (Finset.card_image_of_injective T hf).symm
    _ ≤ s.card := Finset.card_le_card himage
    _ ≤ n := hs

end Counting

variable {lambda tau kappa s wit rnd : Nat}

/-- The committed output of a run result through a function. -/
def committedOutput {F : Type*} [CommRing F] {B : Type*} (G : Committed F lambda tau kappa s wit rnd → B)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd))) :
    Option B :=
  match out.state with
  | .done committed => some (G committed)
  | _ => none

/-- At a fresh lines input the tail's committed result, through any function,
is that function of the committed result at a uniform lines answer. -/
theorem tail_output_uniform {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] {B : Type*}
    (G : Committed F lambda tau kappa s wit rnd → B)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd)))
    (data : PrefixData lambda tau kappa s wit rnd) (hstate : out.state = .done data)
    (hfresh : out.hashTable (linesInput S salt witness data) = none) :
    (continueRun family 1 (commitTail S salt witness) out).map (committedOutput G) =
      (PMF.uniformOfFintype (Out lambda s wit rnd)).map (fun lines => some (G (committedOf S salt witness data lines))) := by
  have hstep : (procedure : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd))).step
        (.hash (linesInput S salt witness data) fun lines => Program.done (committedOf S salt witness data lines)) =
      PMF.pure (.hash (linesInput S salt witness data) fun lines => Program.done (committedOf S salt witness data lines)) :=
    rfl
  unfold continueRun
  rw [hstate]
  simp only [commitTail_eq, runFixed, hstep, PMF.pure_bind, PMF.map_bind, PMF.map_comp]
  rw [← FreshHashUniform.query_fresh_uniform out.hashTable (linesInput S salt witness data) hfresh, PMF.map_comp]
  congr 1
  · congr
    exact Subsingleton.elim _ _
  · funext result
    simp [PMF.pure_map, mark, committedOutput]

end
end SDitH.Proofs.HitCount
