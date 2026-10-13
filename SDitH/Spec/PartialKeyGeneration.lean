import SDitH.Spec.KeyGeneration
import SDitH.Spec.IntegerSamplingTrace

/-! Algorithms 1/2 through the partial integer sampler. This binary instance
uses the actual unsalted cipher stream. Correspondence with finite Algorithm-6
outputs is conditional on successful finite PRG execution; neither its missing
block-size denominator nor Category-III Parse is repaired here.

The two undeclared names B and x_A have separate optional external bindings.
The literal wrappers leave both absent. Pending observation and undefined reads
are not key-generation rejection rules. Serializers remain supplied functions.
-/

namespace SDitH.Spec.PartialKeyGeneration

open DomainSeparation FieldRepresentation ByteSampling IntegerSampling KeyGeneration

inductive ExpansionObservation (w m : Nat) where
  | pending (state : PartialVector m w)
  | undefinedIntegerAssignment (state : PartialVector m w) (candidate : Candidate)
  | returned (expanded : WitnessExpansion.Expanded (ZMod 2) w m)

/-- Diagnostics without an assertion about unconsumed infinite reader tails. -/
inductive ExpansionTrace (w m : Nat) where
  | pending (values : List (Fin m)) (cursor : Nat)
  | undefinedIntegerAssignment (values : List (Fin m)) (cursor candidate nextCursor : Nat)
  | returned (expanded : WitnessExpansion.Expanded (ZMod 2) w m)

def expansionTrace {w m : Nat} : ExpansionObservation w m → ExpansionTrace w m
  | .pending state => .pending state.values state.next.position
  | .undefinedIntegerAssignment state candidate =>
      .undefinedIntegerAssignment state.values state.next.position candidate.value candidate.next.position
  | .returned expanded => .returned expanded

noncomputable def afterSamplingTrace {w m d : Nat} (widths : Fin d → Nat) :
    VectorTrace m w → ExpansionTrace w m
  | .pending values cursor => .pending values cursor
  | .undefinedAssignment values cursor candidate nextCursor =>
      .undefinedIntegerAssignment values cursor candidate nextCursor
  | .returned positions _ => .returned (WitnessExpansion.expandAfterSampling widths (fun i => positions[i]))

/-- The actual Algorithm-1 deterministic suffix runs only after positions
return. Its local position mutations cannot change the already constructed x. -/
noncomputable def afterSampling {w m d : Nat} (widths : Fin d → Nat) :
    VectorObservation m w → ExpansionObservation w m
  | .pending state => .pending state
  | .undefinedAssignment state candidate => .undefinedIntegerAssignment state candidate
  | .returned positions _ => .returned (WitnessExpansion.expandAfterSampling widths (fun i => positions[i]))

noncomputable def expandFromReader {w m d : Nat} (widths : Fin d → Nat) (hm : 0 < m)
    (binding : Option Nat) (fuel : Nat) (src : Reader) : ExpansionObservation w m :=
  afterSampling widths (sampleVectorWithBinding m hm w binding fuel src)

/-- PRG.Init(seed) at the documented ciphertext-stream boundary. All integer
attempts use the actual stream and its increasing byte cursor. -/
noncomputable def expandWithBinding (category : Category) {w m d : Nat}
    (seed : Bits (width category)) (widths : Fin d → Nat) (hm : 0 < m)
    (binding : Option Nat) (fuel : Nat) : ExpansionObservation w m :=
  expandFromReader widths hm binding fuel (PRG.reader category seed (fun _ => false))

noncomputable def expand (category : Category) {w m d : Nat}
    (seed : Bits (width category)) (widths : Fin d → Nat) (hm : 0 < m)
    (fuel : Nat) : ExpansionObservation w m :=
  expandWithBinding category seed widths hm none fuel

inductive KeyObservation (category : Category) (r k w m : Nat) (Result : Type) where
  | witnessPending (state : PartialVector m w)
  | undefinedIntegerAssignment (state : PartialVector m w) (candidate : Candidate)
  | undefinedXA (state : Prefix category r k w m)
  | returned (value : Result)

/-- Lines 4–8 after returned witness expansion. The matrix uses its own public
seed; the missing x_A is read only after both expansions. -/
noncomputable def afterExpansion (category : Category) {r k w m : Nat}
    (publicSeed : Bits (width category)) (count : Nat) (enough : r ≤ 8 * count)
    (xA : Option (Fin (r + k) → ZMod 2)) : ExpansionObservation w m →
    KeyObservation category r k w m (SecretKey (width category) r)
  | .pending state => .witnessPending state
  | .undefinedIntegerAssignment state candidate => .undefinedIntegerAssignment state candidate
  | .returned expanded =>
      let state : Prefix category r k w m :=
        ⟨publicSeed, expanded, expandMatrix category publicSeed r k count enough⟩
      match finishWithBinding state xA with
      | none => .undefinedXA state
      | some key => .returned key

noncomputable def runWithBindings (category : Category) {r k w m d : Nat}
    (secretSeed publicSeed : Bits (width category)) (widths : Fin d → Nat) (hm : 0 < m)
    (integerBinding : Option Nat) (xA : Option (Fin (r + k) → ZMod 2))
    (fuel count : Nat) (enough : r ≤ 8 * count) :
    KeyObservation category r k w m (SecretKey (width category) r) :=
  afterExpansion category publicSeed count enough xA
    (expandWithBinding category secretSeed widths hm integerBinding fuel)

noncomputable def run (category : Category) {r k w m d : Nat}
    (secretSeed publicSeed : Bits (width category)) (widths : Fin d → Nat) (hm : 0 < m)
    (fuel count : Nat) (enough : r ≤ 8 * count) :
    KeyObservation category r k w m (SecretKey (width category) r) :=
  runWithBindings category secretSeed publicSeed widths hm none none fuel count enough

def mapReturned {category : Category} {r k w m : Nat} {A B : Type} (f : A → B) :
    KeyObservation category r k w m A → KeyObservation category r k w m B
  | .witnessPending state => .witnessPending state
  | .undefinedIntegerAssignment state candidate => .undefinedIntegerAssignment state candidate
  | .undefinedXA state => .undefinedXA state
  | .returned value => .returned (f value)

/-- Both independent uniform seed draws precede the actual partial caller.
This PMF is a distribution of observations, not a presumed distribution of keys. -/
noncomputable def keygen (category : Category) {r k w m d : Nat}
    (widths : Fin d → Nat) (hm : 0 < m) (fuel count : Nat) (enough : r ≤ 8 * count) :
    PMF (KeyObservation category r k w m (SecretKey (width category) r)) :=
  (sampleSeeds (width category)).map fun seeds =>
    run category seeds.1 seeds.2 widths hm fuel count enough

/-- Algorithm 2's ordered serializer calls are reached only on returned typed
keys. No output encoding, injectivity or round-trip contract is assumed. -/
noncomputable def encodedKeygen (category : Category) {r k w m d : Nat}
    (encoding : Serialization (width category) r) (widths : Fin d → Nat) (hm : 0 < m)
    (fuel count : Nat) (enough : r ≤ 8 * count) :
    PMF (KeyObservation category r k w m (List Bool × List Bool)) :=
  (keygen (k := k) (w := w) category widths hm fuel count enough).map
    (mapReturned (serializeKeys encoding))

end SDitH.Spec.PartialKeyGeneration
