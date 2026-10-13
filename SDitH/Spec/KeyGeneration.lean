import SDitH.Spec.PRG
import SDitH.Spec.WitnessExpansion
import SDitH.Spec.Batching
import SDitH.Spec.BLCCommit
import Mathlib.Probability.Distributions.Uniform

/-! Algorithm 2 and its initialization dependencies, printed pp. 11–13.
This is a staged transcription, not a completed key-generation algorithm.
SampleIntegers still has an undefined accepted-value assignment, and line 5
uses x_A without defining it. Neither gap is filled with an intended value.

The seed draws, actual post-position witness expansion, actual cipher-stream
ExpandH column loop, printed syndrome assignment and ordered key fields are
exposed separately. Finite-PRG correspondence retains Algorithm-6 obligations.
Structured key serialization remains a parameter, with no codec contract.
-/

namespace SDitH.Spec.KeyGeneration

open DomainSeparation FieldRepresentation

noncomputable def sampleSeeds (lambda : Nat) : PMF (Bits lambda × Bits lambda) :=
  (PMF.uniformOfFintype (Bits lambda)).bind fun secret =>
    (PMF.uniformOfFintype (Bits lambda)).map fun publicPart => (secret, publicPart)

structure PublicKey (lambda r : Nat) where
  seed : Bits lambda
  syndrome : Fin r → ZMod 2

structure SecretKey (lambda r : Nat) where
  publicPart : PublicKey lambda r
  witness : List (ZMod 2)

/-- The unspecified serializers receive typed ordered fields. Their names do
not assert injectivity, length, a byte order or decoding round trips. -/
structure Serialization (lambda r : Nat) where
  encodePublic : PublicKey lambda r → List Bool
  encodeSecret : SecretKey lambda r → List Bool

/-- ExpandH's printed column loop, from the concrete unsalted cipher stream.
This is separately related to successful finite PRG executions; the Category-III
Parse inconsistency is not repaired by defining this mathematical stream. -/
def expandMatrix (category : Category) (seed : Bits (width category))
    (r k count : Nat) (enough : r ≤ 8 * count) : Matrix (Fin r) (Fin k) (ZMod 2) :=
  fun i j => BLCCommit.bitField ((ByteSampling.expandHColumns
    (PRG.stream category seed (fun _ => false)) r k count enough).value i j)

structure Prefix (category : Category) (r k w m : Nat) where
  publicSeed : Bits (width category)
  expanded : WitnessExpansion.Expanded (ZMod 2) w m
  matrix : Matrix (Fin r) (Fin k) (ZMod 2)

/-- Lines 3–4, after the unresolved position sampler. The actual Algorithm-1
body retains its w*m-sized solution; no tensor-dimension equality is imposed. -/
noncomputable def prepareAfterPositions (category : Category) {r k w m d : Nat}
    (seed : Bits (width category)) (widths : Fin d → Nat) (positions : Fin w → Fin m)
    (count : Nat) (enough : r ≤ 8 * count) : Prefix category r k w m :=
  { publicSeed := seed
    expanded := WitnessExpansion.expandAfterSampling widths positions
    matrix := expandMatrix category seed r k count enough }

/-- Only the flat length equation is used here, not the false Table-3 tensor
equation. This is a coordinate-preserving cast of the actual generated vector. -/
def generatedSolution {category : Category} {r k w m : Nat}
    (state : Prefix category r k w m) (lengthEq : r + k = w * m) : Fin (r + k) → ZMod 2 :=
  fun i => state.expanded.solution (Fin.cast lengthEq i)

def instanceOf {r k : Nat} (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2) :
    SDInstance (ZMod 2) (r + k) k :=
  { H := fun row => Batching.systematicLeft H' (Fin.cast (Nat.add_sub_cancel r k) row)
    y := fun row => y (Fin.cast (Nat.add_sub_cancel r k) row) }

/-- The right-identity orientation printed in the key-generation prose.
It remains distinct from the [I | H'] algorithmic matrix. -/
def systematicRight {K : Type*} [CommRing K] {r k : Nat} (H' : Matrix (Fin r) (Fin k) K) :
    Matrix (Fin r) (Fin (k + r)) K :=
  fun row => Fin.addCases (H' row) (fun col => if row = col then 1 else 0)

/-- The explicit coordinate reordering that relates the two orientations.
No use of this permutation is inserted into Algorithm 2. -/
def swapBlocks {K : Type*} {r k : Nat} (x : Fin (r + k) → K) : Fin (k + r) → K :=
  Fin.addCases (fun j => x (j.natAdd r)) (fun i => x (i.castAdd k))

/-- Line 5 literally uses x_A. An optional external binding records exactly
what is missing; the computed `expanded.solution` is not substituted for it.
None marks an undefined source read, not a key-generation rejection branch. -/
def finishWithBinding {category : Category} {r k w m : Nat}
    (state : Prefix category r k w m) (xA : Option (Fin (r + k) → ZMod 2)) :
    Option (SecretKey (width category) r) :=
  xA.map fun x =>
    { publicPart := ⟨state.publicSeed, (Batching.systematicLeft state.matrix).mulVec x⟩
      witness := state.expanded.witness }

def serializeKeys {lambda r : Nat} (encoding : Serialization lambda r) (secret : SecretKey lambda r) :
    List Bool × List Bool := (encoding.encodePublic secret.publicPart, encoding.encodeSecret secret)

def finishEncoded {category : Category} {r k w m : Nat}
    (encoding : Serialization (width category) r) (state : Prefix category r k w m)
    (xA : Option (Fin (r + k) → ZMod 2)) : Option (List Bool × List Bool) :=
  (finishWithBinding state xA).map (serializeKeys encoding)

/-- Typed phase-0 data once Deserialize has returned. Raw decoding is separate;
no parser or serialization law is presumed here. -/
structure InitializedPublic (category : Category) (r k : Nat) where
  key : PublicKey (width category) r
  matrix : Matrix (Fin r) (Fin k) (ZMod 2)

structure InitializedSecret (category : Category) (r k : Nat) where
  publicPart : InitializedPublic category r k
  witness : List (ZMod 2)

def initializePublic (category : Category) {r k : Nat} (key : PublicKey (width category) r)
    (count : Nat) (enough : r ≤ 8 * count) : InitializedPublic category r k :=
  ⟨key, expandMatrix category key.seed r k count enough⟩

def initializeSecret (category : Category) {r k : Nat} (key : SecretKey (width category) r)
    (count : Nat) (enough : r ≤ 8 * count) : InitializedSecret category r k :=
  ⟨initializePublic category key.publicPart count enough, key.witness⟩

end SDitH.Spec.KeyGeneration
