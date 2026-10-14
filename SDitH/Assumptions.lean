import SDitH.Spec.Syndrome
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Perm
import SDitH.Spec.RandomOracle
import SDitH.Spec.HashCipher

/-!
Assumption boundary for the SDitH v3.0 formalization.

The currently established source discrepancy results require no cryptographic
assumptions. Accordingly, this file intentionally declares no axioms.

This module defines a candidate precise reading of the three §5.3 assumptions:
planted uniform SD hardness, a lazy random oracle, and ideal keyed permutations.
The joint ROM/ICM model below makes their sampling relationship explicit.
It does not assert any of them as axioms. The source does not give a machine model
or a detailed random-instance distribution; those correspondence decisions need
human review. No end-to-end security theorem currently consumes SDHardness.
The lazy oracle definition is shared with the initial abstract signature-game
lemmas; those do not establish extraction, simulation or full EUF-CMA security.

These models must be explicit definitions and hypotheses in future security
theorems. They must not be used as names for unproved reductions or conclusions.
In particular the heuristic step in §5.1 and missing EUF-CMA reduction are NOT
assumptions admitted by this file. See `audit/HUMAN_REVIEW.md`.

State at continuation 336: the composed forgery bound
`SDitH.Proofs.SeedTermDischarge.forgery_le_final_hard_C` (generic layouts),
`SDitH.Proofs.CandidateSerialization.forgery_le_final_full_enc` (the full
layout and a named bit-per-coordinate encoding) and
`SDitH.Proofs.DistributionalFinal.averaged_forgery_le_final` (averaged over an
instance distribution) carry their cryptographic hypotheses as explicit
theorem parameters, each a named definition in the proof modules:
`OffHitAssembly.DataClose` and `LeafTermBound.LeafHide` (the PRG not
idealized), the retry bound `hretry` and `SeedTermDischarge.SimulatorTermBounds5`
(the challenge and batching expansions are deterministic parameters that the
forger evaluates at every counter without a query, so these stay named until
the expansion is modelled as a counted oracle), and the hardness assumption
`InstanceHardness.InstanceHard` on the fixed public instance
`Spec.KeyGeneration.instanceOf`, or `DistributionalFinal.DistributionHard` on
an instance distribution given as a parameter. `SDHardness` below is still not
consumed: Algorithm 2's literal routine returns no key (`B`, `x_A` undefined),
so its instance law is not formed, and nothing relates it to `plantedSD`.
-/

namespace SDitH.Assumptions

open Spec
open scoped ENNReal

noncomputable section

variable {F : Type*} [Field F] [Fintype F] {n k : Nat}

/-- Candidate interpretation of "random SD instance": independent uniform H
and an exact-weight error x, with y := Hx. Uniform full matrices are different
from the seed-expanded systematic matrices in the actual key generator. -/
def plantedSD (errors : Finset (Fin n → F))
    (nonemptyErrors : errors.Nonempty) : PMF (SDInstance F n k) :=
  (PMF.uniformOfFintype (Matrix (Fin (n - k)) (Fin n) F)).bind fun H =>
    (PMF.uniformOfFinset errors nonemptyErrors).map fun x => ⟨H, H.mulVec x⟩

/-- Explicit correspondence obligation for the error sample space. -/
def ExactWeightSampleSpace (w : Nat) (errors : Finset (Fin n → F)) : Prop :=
  ∀ x, x ∈ errors ↔ hammingWeight x = w

/-- A runtime-accounted adversary family. The machine semantics and cost
function are explicit review obligations, not inferred from Lean functions. -/
structure SDSolverFamily (F : Type*) (n k : Nat) where
  Program : Type
  run : Program → SDInstance F n k → PMF (Option (Fin n → F))
  time : Program → Nat

def sdSuccess (instances : PMF (SDInstance F n k)) (w : Nat)
    (solve : SDInstance F n k → PMF (Option (Fin n → F))) : ℝ≥0∞ := by
  classical
  exact (instances.bind fun inst => (solve inst).map fun output =>
    match output with
    | none => false
    | some x => decide (SDSolution inst w x)) true

/-- The explicit quantitative hardness predicate. The desired RSD or EUF-CMA
conclusion is deliberately absent. The sample-space equation is part of the
antecedent rather than being silently presumed. -/
def SDHardness (w : Nat) (errors : Finset (Fin n → F))
    (hne : errors.Nonempty) (family : SDSolverFamily F n k)
    (ε : ℝ≥0∞) (t : Nat) : Prop :=
  ExactWeightSampleSpace w errors ∧
  ∀ program, family.time program ≤ t →
    sdSuccess (plantedSD errors hne) w (family.run program) ≤ ε

/-- One query to a lazy-sampled random oracle. Repeated queries return the same
output; fresh queries are uniform. An execution starts with `fun _ => none`.
SignatureSecurity now supplies a bounded adaptive chosen-message game using
this definition. Its full concrete correspondence and security reduction remain
unproved. The re-export preserves this standalone assumption interface. -/
def randomOracleQuery {Input Output : Type*} [DecidableEq Input]
    [Fintype Output] [Nonempty Output]
    (table : Input → Option Output) (query : Input) :
    PMF (Output × (Input → Option Output)) :=
  Spec.RandomOracle.query table query

/-- A finite ideal-cipher family consists of independently uniform keyed
permutations. Decryption uses each permutation's inverse, not a fresh oracle.
Proofs/IdealCipher connects adaptive encryption/decryption to this model.
Full source composition and signature security remain unfinished. -/
def idealCipherFamily (Key Block : Type*) [Fintype Key] [Fintype Block] :
    PMF (Key → Equiv.Perm Block) := by
  classical
  exact PMF.uniformOfFintype (Key → Equiv.Perm Block)

/-- Candidate joint ROM/ICM experiment: one sampled hidden cipher family and
independent fresh hash draws in the shared lazy table. This joint sampling
choice does not follow merely from uniform marginal models. It asserts no
correspondence with concrete SHAKE/AES/Rijndael and no security conclusion. -/
def sharedOracleModel {Input Digest Key Block State : Type*}
    [Fintype Digest] [Nonempty Digest] [Fintype Key] [Fintype Block]
    (procedure : Spec.HashCipher.Procedure Input Digest Key Block State) (budget : Nat) (initial : State) :
    PMF (Spec.IdealCipher.Family Key Block × Spec.HashCipher.Result Input Digest Key Block State) :=
  Spec.HashCipher.jointExperiment procedure budget initial

end
end SDitH.Assumptions
