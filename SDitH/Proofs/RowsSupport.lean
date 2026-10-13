import SDitH.Proofs.HeadCommitSplit
import SDitH.Proofs.TableSupport

/-! The defined inputs after a run of hash calls, and the finished state of
a run ending in a pure value. After running a collection of hash calls
followed by a pure finish, every defined input of the resulting table was
defined before or is one of the calls' inputs; and a run of a program
bound to a pure finish that ends finished returns the finish of some
value. These are the facts about the partial row hashes used to reduce
the row-stored event to the last commitment block's membership in a set
fixed before the last call. -/

namespace SDitH.Proofs.RowsSupport

open Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.HashCipherTrace
open Spec.BAVC (Digest)
open Spec.SlopeConsistencyGame (Out)
open TableSupport
open scoped Classical

noncomputable section

variable {lambda s wit rnd : Nat}

/-- The step of the program procedure at a hash call. -/
theorem step_hash {A : Type*} (input : List Bool)
    (next : Out lambda s wit rnd → Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A) :
    (procedure : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)).step (.hash input next) =
      PMF.pure (.hash input next) := rfl

/-- The step of the program procedure at a cipher call. -/
theorem step_cipher {A : Type*} (request : Spec.IdealCipher.Query (Bits lambda) (Bits lambda))
    (next : Bits lambda → Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A) :
    (procedure : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)).step (.cipher request next) =
      PMF.pure (.cipher request next) := rfl

/-- The step of the program procedure at a finished program. -/
theorem step_done {A : Type*} (v : A) :
    (procedure : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)).step (.done v) = PMF.pure .stop := rfl

/-- A hash call bound to a continuation is the hash with the continuation
at the digest. -/
theorem hashCall_bind {A : Type*} (input : List Bool)
    (g : Digest lambda → Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A) :
    Spec.HashCipherProgram.bind (hashCall (s := s) (wit := wit) (rnd := rnd) input) g =
      Program.hash input fun answer => g answer.1 := rfl

/-- After a run of hash calls over a list followed by a pure finish, every
defined input was defined before or is one of the calls' inputs. -/
theorem rows_defined {ι A : Type*} [DecidableEq ι] (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (q : ι → List Bool) (g : (ι → Digest lambda) → A) :
    ∀ (m : Nat) (L : List ι) (acc : ι → Digest lambda) (table : List Bool → Option (Out lambda s wit rnd))
      (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
      (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd)))
      (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
        (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)),
      out ∈ (runFixed procedure family m
        (Spec.HashCipherProgram.bind (collect (fun e => hashCall (q e)) L acc) fun v => Program.done (g v))
        table hashes ciphers log).support →
      ∀ x, out.hashTable x ≠ none → table x ≠ none ∨ ∃ e ∈ L, x = q e := by
  intro m
  induction m with
  | zero =>
    intro L acc table hashes ciphers log out hout x hx
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst hout
    exact Or.inl hx
  | succ m ih =>
    intro L acc table hashes ciphers log out hout x hx
    cases L with
    | nil =>
      simp only [collect, Spec.HashCipherProgram.bind, runFixed, step_done, PMF.pure_bind,
        PMF.mem_support_pure_iff] at hout
      subst hout
      exact Or.inl hx
    | cons k rest =>
      simp only [collect, hashCall_bind, Spec.HashCipherProgram.bind, runFixed, step_hash,
        PMF.pure_bind] at hout
      obtain ⟨result, hres, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      have hx' : inner.hashTable x ≠ none := hx
      rcases ih rest (Function.update acc k result.1.1) result.2 _ _ _ inner hinner x hx' with h | ⟨e, he, hxe⟩
      · rcases query_table table (q k) result hres with h2 | h2
        · rw [h2] at h
          exact Or.inl h
        · by_cases hxk : x = q k
          · exact Or.inr ⟨k, List.mem_cons_self .., hxk⟩
          · rw [h2] at h
            have h' : table x ≠ none := by simpa [Function.update, hxk] using h
            exact Or.inl h'
      · exact Or.inr ⟨e, List.mem_cons_of_mem k he, hxe⟩

/-- A run of a program bound to a pure finish that ends finished returns the
finish of some value. -/
theorem runFixed_bind_done {A B : Type*} (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (g : A → B) :
    ∀ (m : Nat) (p : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
      (table : List Bool → Option (Out lambda s wit rnd))
      (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
      (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd)))
      (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
        (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) B)),
      out ∈ (runFixed procedure family m (Spec.HashCipherProgram.bind p fun v => Program.done (g v))
        table hashes ciphers log).support →
      ∀ d, out.state = .done d → ∃ v, d = g v := by
  intro m
  induction m with
  | zero =>
    intro p table hashes ciphers log out hout d hd
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst hout
    cases p with
    | done v => exact ⟨v, (Program.done.inj hd).symm⟩
    | hash input next => exact absurd hd (by simp [Spec.HashCipherProgram.bind])
    | cipher request next => exact absurd hd (by simp [Spec.HashCipherProgram.bind])
  | succ m ih =>
    intro p table hashes ciphers log out hout d hd
    cases p with
    | done v =>
      simp only [Spec.HashCipherProgram.bind, runFixed, step_done, PMF.pure_bind, PMF.mem_support_pure_iff] at hout
      subst hout
      exact ⟨v, (Program.done.inj hd).symm⟩
    | hash input next =>
      simp only [Spec.HashCipherProgram.bind, runFixed, step_hash, PMF.pure_bind] at hout
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      exact ih (next result.1) _ _ _ _ inner hinner d hd
    | cipher request next =>
      simp only [Spec.HashCipherProgram.bind, runFixed, step_cipher, PMF.pure_bind] at hout
      exact ih (next _) _ _ _ _ out hout d hd

end
end SDitH.Proofs.RowsSupport
