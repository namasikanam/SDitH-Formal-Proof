import SDitH.Spec.HashCipherProgram
import SDitH.Proofs.IdealCipherProgram

namespace SDitH.Proofs.HashCipherProgram

open Spec.HashCipherProgram
open scoped Classical
noncomputable section

variable {Input Digest Key Block A : Type*}

theorem bounded_mono (program : Program Input Digest Key Block A) (small large : Nat)
    (hle : small ≤ large) (h : Bounded small program) : Bounded large program := by
  induction small generalizing program large with
  | zero =>
    cases program with
    | done value => cases large <;> trivial
    | hash input next => exact False.elim h
    | cipher request next => exact False.elim h
  | succ small ih =>
    cases program with
    | done value => cases large <;> trivial
    | hash input next =>
      cases large with
      | zero => omega
      | succ large => exact fun answer => ih (next answer) large (by omega) (h answer)
    | cipher request next =>
      cases large with
      | zero => omega
      | succ large => exact fun answer => ih (next answer) large (by omega) (h answer)

theorem bounded_bind {B : Type*} (program : Program Input Digest Key Block A)
    (next : A → Program Input Digest Key Block B) (q k : Nat)
    (hp : Bounded q program) (hn : ∀ a, Bounded k (next a)) : Bounded (q + k) (bind program next) := by
  induction q generalizing program with
  | zero =>
    cases program with
    | done value => simpa only [Spec.HashCipherProgram.bind, Nat.zero_add] using hn value
    | hash input tail => exact False.elim hp
    | cipher request tail => exact False.elim hp
  | succ q ih =>
    cases program with
    | done value => exact bounded_mono (next value) k (q + 1 + k) (by omega) (hn value)
    | hash input tail =>
      rw [Spec.HashCipherProgram.bind, Nat.add_right_comm q 1 k]
      exact fun answer => ih (tail answer) (hp answer)
    | cipher request tail =>
      rw [Spec.HashCipherProgram.bind, Nat.add_right_comm q 1 k]
      exact fun answer => ih (tail answer) (hp answer)

theorem bounded_liftHash (program : Spec.OracleProgram.Program Input Digest A) (budget : Nat)
    (h : Spec.OracleProgram.Bounded budget program) : Bounded budget (liftHash (Key := Key) (Block := Block) program) := by
  induction budget generalizing program with
  | zero => cases program <;> exact h
  | succ budget ih =>
    cases program with
    | done value => trivial
    | query input next => exact fun answer => ih (next answer) (h answer)

theorem bounded_liftCipher (program : Spec.OracleProgram.Program (Spec.IdealCipher.Query Key Block) Block A) (budget : Nat)
    (h : Spec.OracleProgram.Bounded budget program) : Bounded budget (liftCipher (Input := Input) (Digest := Digest) program) := by
  induction budget generalizing program with
  | zero => cases program <;> exact h
  | succ budget ih =>
    cases program with
    | done value => trivial
    | query request next => exact fun answer => ih (next answer) (h answer)

variable [Fintype Digest] [Nonempty Digest]

/-- Every mixed program with a proved bound completes, regardless of the
interleaving and answers. Undefined source computations must remain explicit
return values when encoded; exhaustion is not silently treated as rejection. -/
theorem run_complete (family : Spec.IdealCipher.Family Key Block) (budget : Nat)
    (program : Program Input Digest Key Block A) (hbound : Bounded budget program)
    (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (out : Spec.HashCipher.Result Input Digest Key Block (Program Input Digest Key Block A))
    (hout : out ∈ (Spec.HashCipher.runFixed procedure family budget program table hashes ciphers).support) :
    ∃ value, out.state = .done value := by
  induction budget generalizing program table hashes ciphers out with
  | zero =>
    cases program with
    | done value =>
      simp only [Spec.HashCipher.runFixed, PMF.mem_support_pure_iff] at hout
      subst out
      exact ⟨value, rfl⟩
    | hash input next => exact False.elim hbound
    | cipher request next => exact False.elim hbound
  | succ budget ih =>
    cases program with
    | done value =>
      simp only [Spec.HashCipher.runFixed, procedure, PMF.pure_bind, PMF.mem_support_pure_iff] at hout
      subst out
      exact ⟨value, rfl⟩
    | hash input next =>
      simp only [Spec.HashCipher.runFixed, procedure, PMF.pure_bind] at hout
      obtain ⟨result, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst out
      exact ih (next result.1) (hbound result.1) result.2 ((input, result.1) :: hashes) ciphers tail ht
    | cipher request next =>
      simp only [Spec.HashCipher.runFixed, procedure, PMF.pure_bind] at hout
      exact ih (next (Spec.IdealCipher.answer family request)) (hbound _) table hashes _ out hout

/-- Exact operational correspondence to the existing source hash programs,
including their table, query history, result and collision flag. -/
theorem run_liftHash (family : Spec.IdealCipher.Family Key Block) (budget : Nat)
    (program : Spec.OracleProgram.Program Input Digest A) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) :
    Spec.HashCipher.runFixed procedure family budget (liftHash program) table hashes ciphers =
      (Spec.RandomOracleCollision.run Spec.OracleProgram.procedure budget program table hashes).map (liftHashResult ciphers) := by
  induction budget generalizing program table hashes with
  | zero => simp only [Spec.HashCipher.runFixed, Spec.RandomOracleCollision.run, PMF.pure_map, liftHashResult]
  | succ budget ih =>
    cases program with
    | done value =>
      simp only [liftHash, Spec.HashCipher.runFixed, procedure, Spec.RandomOracleCollision.run,
        Spec.OracleProgram.procedure, PMF.pure_bind, PMF.pure_map, liftHashResult]
    | query input next =>
      simp only [liftHash, Spec.HashCipher.runFixed, procedure, Spec.RandomOracleCollision.run,
        Spec.OracleProgram.procedure, PMF.pure_bind, PMF.map_bind]
      congr 1
      funext result
      refine (congrArg (fun law => law.map (Spec.HashCipher.markHash
        (Spec.RandomOracleCollision.freshHit table hashes input result.1)))
        (ih (next result.1) result.2 ((input, result.1) :: hashes))).trans ?_
      simp only [PMF.map_comp, Function.comp_def, liftHashResult, Spec.HashCipher.markHash]
      rfl

/-- Exact operational correspondence to the existing source seed/cipher
programs. In particular their inverse queries and repeats still use one family. -/
theorem run_liftCipher (family : Spec.IdealCipher.Family Key Block) (budget : Nat)
    (program : Spec.OracleProgram.Program (Spec.IdealCipher.Query Key Block) Block A) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) :
    Spec.HashCipher.runFixed procedure family budget (liftCipher program) table hashes ciphers =
      (Spec.IdealCipher.runFixed Spec.IdealCipherProgram.procedure family budget program ciphers).map (liftCipherResult table hashes) := by
  induction budget generalizing program ciphers with
  | zero => simp only [Spec.HashCipher.runFixed, Spec.IdealCipher.runFixed, PMF.pure_map, liftCipherResult]
  | succ budget ih =>
    cases program with
    | done value =>
      simp only [liftCipher, Spec.HashCipher.runFixed, procedure, Spec.IdealCipher.runFixed,
        Spec.IdealCipherProgram.procedure, PMF.pure_bind, PMF.pure_map, liftCipherResult]
    | query request next =>
      simp only [liftCipher, Spec.HashCipher.runFixed, procedure, Spec.IdealCipher.runFixed,
        Spec.IdealCipherProgram.procedure, PMF.pure_bind]
      exact ih (next (Spec.IdealCipher.answer family request)) _

end
end SDitH.Proofs.HashCipherProgram
