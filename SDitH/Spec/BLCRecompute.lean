import SDitH.Spec.BAVCReconstruction
import SDitH.Spec.ConcreteBLC
import SDitH.Spec.SignatureComposition

/-! Algorithm 12, printed p. 30, at typed auxiliary/opening boundaries.

The prefix runs through line 20, retaining the actual reconstruction, sampling,
folding and consistency expansion. Undeclared seed/rshare/phi_mu names have
explicit optional bindings; no alias or initialization is invented. The source
initializes reval, not rshare. Line 21 is not well typed with the displayed
scalar Delta_inv and binary-matrix result. Its operands form an explicit stopped
state. The independently defined suffix takes a binary base matrix and executes
lines 22–27; it is not asserted to be a continuation of the literal line 21.
-/

namespace SDitH.Spec.BLCRecompute

open DomainSeparation

abbrev Share (ell kappa : Nat) := Fin ell → Fin kappa → ZMod 2

abbrev SeedArray (lambda tau kappa : Nat) :=
  Fin tau → Fin (2 ^ kappa) → Option (Bits lambda)

/-- External source environments, without any correctness or aliasing contract.
The literal prefix below supplies none at every missing declaration. -/
structure Bindings (lambda tau kappa ell : Nat) where
  nodes : BAVC.NodesBinding lambda tau (2 ^ kappa)
  seed : Option (SeedArray lambda tau kappa)
  share : Fin tau → Option (Share ell kappa)
  phiMu : Option (Fin tau → Fin (2 ^ kappa) → Fin kappa → ZMod 2)

def absentBindings {lambda tau kappa ell : Nat} : Bindings lambda tau kappa ell :=
  ⟨none, none, fun _ => none, none⟩

inductive Error where
  /-- The explicit bottom tuple of line 6. -/
  | headerRejected
  /-- Line 8 tries to destructure a reconstruction which did not return a pair.
  No propagation of that error into the line-6 bottom tuple is specified. -/
  | undefinedReconstructionResult (cause : BAVC.ReconstructionError)
  | undefinedSeedArray
  | undefinedSeedRead
  | undefinedShare
  | undefinedPhiMu
  deriving DecidableEq, Repr

def readSeed {lambda tau kappa : Nat} (seed : Option (SeedArray lambda tau kappa))
    (e : Fin tau) (i : Fin (2 ^ kappa)) : Except Error (Bits lambda) :=
  match seed with
  | none => .error .undefinedSeedArray
  | some values =>
    match values e i with
    | none => .error .undefinedSeedRead
    | some value => .ok value

/-- Line 14, after the actual seed read and byte sampling. -/
def addShare {ell kappa : Nat} (initial : Option (Share ell kappa))
    (random : Fin ell → ZMod 2) (hidden i : Fin (2 ^ kappa)) :
    Except Error (Option (Share ell kappa)) :=
  match initial with
  | none => .error .undefinedShare
  | some value => .ok (some fun c j =>
    value c j + random c * (GrayCode.grayFieldRow hidden j - GrayCode.grayFieldRow i j))

/-- The increasing inner loop, skipping precisely the hidden index. There is
no read of the hidden seed and no PRG call for that index. -/
def foldLeavesThrough {lambda tau kappa s wit rnd : Nat}
    (p : BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (seed : Option (SeedArray lambda tau kappa)) (e : Fin tau) (hidden : Fin (2 ^ kappa))
    (initial : Option (Share (s + (wit + rnd)) kappa))
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount) :
    (count : Nat) → count ≤ 2 ^ kappa →
      Except Error (Option (Share (s + (wit + rnd)) kappa))
  | 0, _ => .ok initial
  | count + 1, hc => do
    let current ← foldLeavesThrough p salt seed e hidden initial randomCount enough count (by omega)
    let i : Fin (2 ^ kappa) := ⟨count, by omega⟩
    if i = hidden then .ok current
    else do
      let leafSeed ← readSeed seed e i
      let random := fun c => BLCCommit.bitField ((ByteSampling.sampleBinary
        ⟨p.prg leafSeed salt e.val, 0⟩ (s + (wit + rnd)) randomCount enough).value c)
      addShare current random hidden i

def correctionIndex {tau : Nat} (e : Fin tau) (positive : 0 < e.val) : Fin (tau - 1) :=
  ⟨e.val - 1, by have he := e.isLt; omega⟩

/-- Lines 15–16. The positive correction is aux[e], whose transmitted slot is
e-1. phi_mu is a separate undeclared name, not replaced by the Gray map. -/
def addCorrection {tau kappa s wit rnd : Nat}
    (aux : BLCCommit.Auxiliary tau s wit rnd)
    (phiMu : Option (Fin tau → Fin (2 ^ kappa) → Fin kappa → ZMod 2))
    (e : Fin tau) (hidden : Fin (2 ^ kappa))
    (current : Option (Share (s + (wit + rnd)) kappa)) :
    Except Error (Option (Share (s + (wit + rnd)) kappa)) :=
  if he : 0 < e.val then
    match current with
    | none => .error .undefinedShare
    | some value =>
      match phiMu with
      | none => .error .undefinedPhiMu
      | some phi => .ok (some fun c j => value c j +
        aux.corrections (correctionIndex e he) c * phi e hidden j)
  else .ok current

structure FoldedExecution (ell kappa : Nat) where
  /-- Binary coordinates of the initialized zero reval vector; unused later. -/
  evaluation : Share ell kappa
  share : Option (Share ell kappa)

def foldExecution {lambda tau kappa s wit rnd : Nat}
    (p : BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (bindings : Bindings lambda tau kappa (s + (wit + rnd)))
    (aux : BLCCommit.Auxiliary tau s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa))
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount) (e : Fin tau) :
    Except Error (FoldedExecution (s + (wit + rnd)) kappa) := do
  let initializedEvaluation : Share (s + (wit + rnd)) kappa := 0
  let current ← foldLeavesThrough p salt bindings.seed e (hidden e) (bindings.share e)
    randomCount enough (2 ^ kappa) le_rfl
  let corrected ← addCorrection aux bindings.phiMu e (hidden e) current
  .ok ⟨initializedEvaluation, corrected⟩

/-- The execution loop preserves source order, including faults. No global
test for missing names is substituted for their actual reads. -/
def foldExecutionsThrough {lambda tau kappa s wit rnd : Nat}
    (p : BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (bindings : Bindings lambda tau kappa (s + (wit + rnd)))
    (aux : BLCCommit.Auxiliary tau s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa))
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount) :
    (count : Nat) → count ≤ tau →
      Except Error (Vector (FoldedExecution (s + (wit + rnd)) kappa) count)
  | 0, _ => .ok #v[]
  | count + 1, hc => do
    let rows ← foldExecutionsThrough p salt bindings aux hidden randomCount enough count (by omega)
    let row ← foldExecution p salt bindings aux hidden randomCount enough ⟨count, by omega⟩
    .ok (rows.push row)

/-- Line 17 reads each share in increasing execution order. An uninitialized
share is still undefined even when its binary matrix has no coordinates. -/
def collectShares {ell kappa : Nat} : {count : Nat} →
    Vector (FoldedExecution ell kappa) count → Except Error (Vector (Share ell kappa) count)
  | 0, _ => .ok #v[]
  | count + 1, rows => do
    let previous ← collectShares rows.pop
    match (rows[count]).share with
    | none => .error .undefinedShare
    | some value => .ok (previous.push value)

def concatenate {ell tau kappa : Nat} (rows : Vector (Share ell kappa) tau) :
    Fin ell → Fin tau → Fin kappa → ZMod 2 := fun c e j => rows[e] c j

/-- Operands immediately before the ill-typed line 21. deltaInv remains a
scalar in F; alphaEvaluation is the specified binary s by tau*kappa matrix.
This record does not smuggle a binary challenge encoding or base result in. -/
structure ConsistencyBoundary (F : Type*) (lambda tau kappa s wit rnd : Nat) where
  deltaInv : F
  delta : F
  auxiliary : BLCCommit.Auxiliary tau s wit rnd
  reconstruction : BAVC.Reconstructed lambda tau (2 ^ kappa)
  Q : Fin (s + (wit + rnd)) → Fin tau → Fin kappa → ZMod 2
  auxiliaryDigest : BLCCommit.Digest lambda
  matrix : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)
  alphaEvaluation : Fin s → Fin tau → Fin kappa → ZMod 2

/-- Lines 1–20. Challenge expansion and raw-index encoding retain their
existing subroutine boundaries. The returned state requires human resolution
of line 21; it is not an Algorithm-12 successful return. -/
noncomputable def prepareWithBindings {F : Type} [Field F] [DecidableEq F]
    {lambda tau kappa B wit rnd wpow : Nat}
    (p : BLCCommit.Primitives lambda tau kappa (lambda + B) wit rnd)
    (salt : Bits lambda) (aux : BLCCommit.Auxiliary tau (lambda + B) wit rnd)
    (decomposition : BLCRetry.Counter × BAVC.Opening lambda tau)
    (expand : BLCRetry.Counter → BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
    (bindings : Bindings lambda tau kappa ((lambda + B) + (wit + rnd)))
    (randomCount consistencyCount : Nat)
    (hrandom : (lambda + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount) :
    Except Error (ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd) := do
  let challenge := expand decomposition.1
  let deltaInv := encode challenge.hidden
  if BLCRetry.GrindingPassed challenge.grinding ∧ deltaInv ≠ 0 then
    let reconstruction : BAVC.Reconstructed lambda tau (2 ^ kappa) ← match BAVC.reconstructWithNodes
      (SeedPrimitives.bavcPrimitives (tau * (2 ^ kappa)) p.grinding p.encStar p.hash)
      salt challenge.hidden decomposition.2 Topen bindings.nodes with
      | .error cause => .error (.undefinedReconstructionResult cause)
      | .ok value => .ok value
    let folded ← foldExecutionsThrough p salt bindings aux challenge.hidden
      randomCount hrandom tau le_rfl
    let shares ← collectShares folded
    let Q := concatenate shares
    let haux := p.hashAux ⟨reconstruction.hcom, aux.corrections⟩
    let binaryMatrix := ByteSampling.expandConsistency (p.xof haux) lambda B
      (wit + rnd) consistencyCount hconsistency
    let M := fun i j => BLCCommit.bitField (binaryMatrix.value i j)
    .ok ⟨deltaInv, deltaInv⁻¹, aux, reconstruction, Q, haux, M, BLC.consistencyColumns M Q⟩
  else .error .headerRejected

noncomputable def prepare {F : Type} [Field F] [DecidableEq F]
    {lambda tau kappa B wit rnd wpow : Nat}
    (p : BLCCommit.Primitives lambda tau kappa (lambda + B) wit rnd)
    (salt : Bits lambda) (aux : BLCCommit.Auxiliary tau (lambda + B) wit rnd)
    (decomposition : BLCRetry.Counter × BAVC.Opening lambda tau)
    (expand : BLCRetry.Counter → BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
    (randomCount consistencyCount : Nat)
    (hrandom : (lambda + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount) :
    Except Error (ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd) :=
  prepareWithBindings p salt aux decomposition expand encode Topen absentBindings
    randomCount consistencyCount hrandom hconsistency

/-- Line 26 has three fields. Algorithm 10's fourth witness-correction field
is absent, rather than filled with a fabricated default to reuse its hash. -/
structure LinesHashInput (lambda tau kappa s : Nat) where
  auxiliary : BLCCommit.Digest lambda
  plain : Fin s → ZMod 2
  base : Fin s → Fin tau → Fin kappa → ZMod 2

/-- The exact suffix from line 22 on, after a caller supplies the base matrix.
Supplying that matrix does not claim to implement the unresolved line 21. -/
noncomputable def suffix {F : Type*} [Field F] [Algebra (ZMod 2) F]
    {lambda tau kappa s wit rnd : Nat} (xi : F)
    (hashLines : LinesHashInput lambda tau kappa s → BLCCommit.Digest lambda)
    (state : ConsistencyBoundary F lambda tau kappa s wit rnd)
    (base : Fin s → Fin tau → Fin kappa → ZMod 2) :
    SignatureComposition.Recomputed F lambda wit rnd where
  delta := state.delta
  witness := fun j => algebraMap (ZMod 2) F (state.auxiliary.witnessCorrection j) +
    state.delta * BLC.psi xi (state.Q (BLC.witnessIndex j))
  randomness := fun j => state.delta * BLC.psi xi (state.Q (BLC.randomnessIndex j))
  lines := hashLines ⟨state.auxiliaryDigest, state.auxiliary.plain, base⟩

def linesPayload {category : FieldRepresentation.Category} {tau kappa s : Nat}
    (encoding : ConcreteBLC.Serialization tau kappa s)
    (input : LinesHashInput (FieldRepresentation.width category) tau kappa s) : List Bool :=
  List.ofFn input.auxiliary ++ encoding.vector input.plain ++ encoding.base input.base

def concreteHashLines (category : FieldRepresentation.Category) {tau kappa s : Nat}
    (encoding : ConcreteBLC.Serialization tau kappa s) :
    LinesHashInput (FieldRepresentation.width category) tau kappa s →
      BLCCommit.Digest (FieldRepresentation.width category) :=
  fun input => HashPrimitives.domainHash category 3 (linesPayload encoding input)

end SDitH.Spec.BLCRecompute
