import SDitH.Proofs.CommitRunLeaf
import SDitH.Proofs.RunKeys

/-! The commitment tail's run. The tail queries the hash only, so its run
does not depend on the family and keeps the cipher history; from a
finished phase it is the run of the tail at the commitments. -/

namespace SDitH.Proofs.TailRun

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open RunCongr RunHistoryShift CommitPhaseExchange TreeRunClosed RunBind CommitRunExchange CommitPhaseLeaf CommitRunLeaf RunKeys
open scoped Classical

noncomputable section

section Generic

variable {Input Digest Key Block A : Type*} [Fintype Digest] [Nonempty Digest]

/-- A hash-only program's run keeps the cipher history. -/
theorem runFixed_hashOnly_history (f : Family Key Block) :
    ∀ (fuel : Nat) (p : Program Input Digest Key Block A), QueriesIn (∅ : Set Key) p →
      ∀ (table : Input → Option Digest) (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
        (log : List (Spec.RandomOracleTrace.Entry Input Digest)) (out : Result Input Digest Key Block (Program Input Digest Key Block A)),
        out ∈ (runFixed procedure f fuel p table hashes ciphers log).support → out.cipherHistory = ciphers := by
  intro fuel
  induction fuel with
  | zero =>
    intro p _ table hashes ciphers log out hout
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst hout
    rfl
  | succ fuel ih =>
    intro p hp table hashes ciphers log out hout
    cases p with
    | done v =>
      simp only [runFixed, step_done, PMF.pure_bind, PMF.mem_support_pure_iff] at hout
      subst hout
      rfl
    | hash input next =>
      simp only [runFixed, step_hash, PMF.pure_bind, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hout
      obtain ⟨result, -, out', hout', rfl⟩ := hout
      exact ih (next result.1) (hp result.1) _ _ _ _ out' hout'
    | cipher request next => exact absurd hp.1 (Set.notMem_empty _)

/-- A hash-only program runs identically against any two families. -/
theorem runFixed_hashOnly_family (f f' : Family Key Block) (fuel : Nat) (p : Program Input Digest Key Block A)
    (hp : QueriesIn (∅ : Set Key) p) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Spec.RandomOracleTrace.Entry Input Digest)) :
    runFixed procedure f' fuel p table hashes ciphers log = runFixed procedure f fuel p table hashes ciphers log :=
  runFixed_congr_family ∅ f f' (fun _ h => absurd h (Set.notMem_empty _)) fuel p hp table hashes ciphers log

/-- The continuation from a finished first run is the continuation's run at
the value, with the collision flags combined. -/
theorem continueRun_done {B : Type*} (f : Family Key Block) (m : Nat) (F : A → Program Input Digest Key Block B)
    (out : Result Input Digest Key Block (Program Input Digest Key Block A)) (v : A) (h : out.state = .done v) :
    continueRun f m F out = (runFixed procedure f m (F v) out.hashTable out.hashHistory out.cipherHistory out.trace).map
      fun out' => { out' with hashCollided := out.hashCollided || out'.hashCollided } := by
  unfold continueRun
  rw [h]

end Generic

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {lambda tau kappa s wit rnd : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)

/-- The tail queries the hash only. -/
theorem queriesIn_commitTail_empty (nodes : Nat → Seed lambda) (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda) :
    QueriesIn (∅ : Set (Bits lambda)) (commitTail S salt witness nodes commits) :=
  queriesIn_commitTail S salt witness ∅ nodes commits

/-- The tail's run keeps the cipher history. -/
theorem commitTail_history (f : Family (Bits lambda) (Bits lambda)) (nodes : Nat → Seed lambda)
    (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda) (m : Nat) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd)))
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd)))
    (hout : out ∈ (runFixed procedure f m (commitTail S salt witness nodes commits) table hashes ciphers log).support) :
    out.cipherHistory = ciphers :=
  runFixed_hashOnly_history f m _ (queriesIn_commitTail_empty S salt witness nodes commits) table hashes ciphers log out hout

/-- The tail's run does not depend on the family. -/
theorem commitTail_family (f f' : Family (Bits lambda) (Bits lambda)) (nodes : Nat → Seed lambda)
    (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda) (m : Nat) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure f' m (commitTail S salt witness nodes commits) table hashes ciphers log =
      runFixed procedure f m (commitTail S salt witness nodes commits) table hashes ciphers log :=
  runFixed_hashOnly_family f f' m _ (queriesIn_commitTail_empty S salt witness nodes commits) table hashes ciphers log

end
end SDitH.Proofs.TailRun
