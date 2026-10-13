import SDitH.Proofs.RunBind
import SDitH.Proofs.PosteriorPrune

/-! Two generic facts about program runs. A program whose cipher requests
all have keys in a set runs identically against two families that agree on
that set; and a program followed by a pure finish runs as the program with
the finish applied to its final state. These let the commitment phase be
compared under the exchange: its calls are at the leaves' keys, which the
exchange fixes, and the exchanged tree enters only its final value. -/

namespace SDitH.Proofs.RunCongr

open Spec.HashCipherProgram (Program procedure)
open Spec.HashCipherTrace (Result runFixed mark)
open Spec.IdealCipher (Family)
open PosteriorPrune (keyOf)
open scoped Classical

noncomputable section

variable {Input Digest Key Block A B : Type*} [Fintype Digest] [Nonempty Digest]

omit [Fintype Digest] [Nonempty Digest] in
theorem step_done (v : A) :
    (procedure : Spec.HashCipher.Procedure Input Digest Key Block (Program Input Digest Key Block A)).step (.done v) =
      PMF.pure .stop := rfl

omit [Fintype Digest] [Nonempty Digest] in
theorem step_hash (input : Input) (next : Digest → Program Input Digest Key Block A) :
    (procedure : Spec.HashCipher.Procedure Input Digest Key Block (Program Input Digest Key Block A)).step (.hash input next) =
      PMF.pure (.hash input next) := rfl

omit [Fintype Digest] [Nonempty Digest] in
theorem step_cipher (request : Spec.IdealCipher.Query Key Block) (next : Block → Program Input Digest Key Block A) :
    (procedure : Spec.HashCipher.Procedure Input Digest Key Block (Program Input Digest Key Block A)).step
        (.cipher request next) = PMF.pure (.cipher request next) := rfl

/-- A program whose cipher requests all have keys in a set. -/
def QueriesIn (S : Set Key) : Program Input Digest Key Block A → Prop
  | .done _ => True
  | .hash _ next => ∀ answer, QueriesIn S (next answer)
  | .cipher request next => keyOf request ∈ S ∧ ∀ answer, QueriesIn S (next answer)

omit [Fintype Digest] [Nonempty Digest] in
theorem queriesIn_bind (S : Set Key) (p : Program Input Digest Key Block A) (g : A → Program Input Digest Key Block B)
    (hp : QueriesIn S p) (hg : ∀ v, QueriesIn S (g v)) : QueriesIn S (Spec.HashCipherProgram.bind p g) := by
  induction p with
  | done v => exact hg v
  | hash input next ih => exact fun answer => ih answer (hp answer)
  | cipher request next ih => exact ⟨hp.1, fun answer => ih answer (hp.2 answer)⟩

/-- Two families agreeing on the queried keys answer alike. -/
theorem answer_congr (S : Set Key) (f f' : Family Key Block) (hff : ∀ κ ∈ S, f' κ = f κ)
    (request : Spec.IdealCipher.Query Key Block) (hk : keyOf request ∈ S) :
    Spec.IdealCipher.answer f' request = Spec.IdealCipher.answer f request := by
  have h := hff _ hk
  cases request with
  | encrypt key input =>
    show f' key input = f key input
    rw [show f' key = f key from h]
  | decrypt key output =>
    show (f' key).symm output = (f key).symm output
    rw [show f' key = f key from h]

/-- A program querying only within a set runs identically against two
families agreeing on the set. -/
theorem runFixed_congr_family (S : Set Key) (f f' : Family Key Block) (hff : ∀ κ ∈ S, f' κ = f κ) :
    ∀ (fuel : Nat) (p : Program Input Digest Key Block A), QueriesIn S p →
      ∀ (table : Input → Option Digest) (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
        (log : List (Spec.RandomOracleTrace.Entry Input Digest)),
        runFixed procedure f' fuel p table hashes ciphers log = runFixed procedure f fuel p table hashes ciphers log := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro p hp table hashes ciphers log
    cases p with
    | done v => simp only [runFixed, step_done, PMF.pure_bind]
    | hash input next =>
      simp only [runFixed, step_hash, PMF.pure_bind]
      congr 1
      funext result
      rw [ih (next result.1) (hp result.1)]
    | cipher request next =>
      simp only [runFixed, step_cipher, PMF.pure_bind]
      rw [answer_congr S f f' hff request hp.1, ih (next _) (hp.2 _)]

/-- A program followed by a pure finish runs as the program with the finish
applied to the final state. -/
theorem runFixed_bind_done (f : Family Key Block) (g : A → B) :
    ∀ (fuel : Nat) (p : Program Input Digest Key Block A) (table : Input → Option Digest) (hashes : List (Input × Digest))
      (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Spec.RandomOracleTrace.Entry Input Digest)),
      runFixed procedure f fuel (Spec.HashCipherProgram.bind p fun v => .done (g v)) table hashes ciphers log =
        (runFixed procedure f fuel p table hashes ciphers log).map fun out =>
          { out with state := Spec.HashCipherProgram.bind out.state fun v => .done (g v) } := by
  intro fuel
  induction fuel with
  | zero => intros; simp only [runFixed, PMF.pure_map]
  | succ fuel ih =>
    intro p table hashes ciphers log
    cases p with
    | done v => simp only [Spec.HashCipherProgram.bind, runFixed, step_done, PMF.pure_bind, PMF.pure_map]
    | hash input next =>
      simp only [Spec.HashCipherProgram.bind, runFixed, step_hash, PMF.pure_bind, PMF.map_bind]
      congr 1
      funext result
      rw [ih (next result.1), PMF.map_comp, PMF.map_comp]
      rfl
    | cipher request next =>
      simp only [Spec.HashCipherProgram.bind, runFixed, step_cipher, PMF.pure_bind]
      exact ih (next _) table hashes _ log

end
end SDitH.Proofs.RunCongr
