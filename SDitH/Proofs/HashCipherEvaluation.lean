import SDitH.Spec.HashCipherEvaluation
import SDitH.Proofs.HashCipherProgram

namespace SDitH.Proofs.HashCipherEvaluation

open Spec.HashCipherProgram Spec.HashCipherEvaluation
open scoped Classical
noncomputable section

variable {Input Digest Key Block A B State : Type*}

theorem liftCipher_bind (program : Spec.OracleProgram.Program (Spec.IdealCipher.Query Key Block) Block A)
    (next : A → Spec.OracleProgram.Program (Spec.IdealCipher.Query Key Block) Block B) :
    liftCipher (Input := Input) (Digest := Digest) (Spec.OracleProgram.bind program next) =
      bind (liftCipher program) (fun value => liftCipher (next value)) := by
  induction program with
  | done value => rfl
  | query request tail ih =>
    simp only [Spec.OracleProgram.bind, liftCipher, Spec.HashCipherProgram.bind]
    congr 1
    funext answer
    exact ih answer

theorem evaluates_bind (family : Spec.IdealCipher.Family Key Block) (table : Input → Option Digest)
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (program : Program Input Digest Key Block A)
    (next : A → Program Input Digest Key Block B) (value : B) :
    Evaluates family table ciphers (bind program next) value ↔
      ∃ middle, Evaluates family table ciphers program middle ∧ Evaluates family table ciphers (next middle) value := by
  induction program with
  | done a =>
    constructor
    · exact fun h => ⟨a, .done a, h⟩
    · rintro ⟨_, h, ht⟩
      cases h
      exact ht
  | hash input tail ih =>
    constructor
    · intro h
      cases h with
      | hash _ _ answer _ stored ht =>
        obtain ⟨middle, hm, hv⟩ := (ih answer).mp ht
        exact ⟨middle, .hash input tail answer middle stored hm, hv⟩
    · rintro ⟨middle, hm, hv⟩
      cases hm with
      | hash _ _ answer _ stored ht =>
        exact .hash input _ answer value stored ((ih answer).mpr ⟨middle, ht, hv⟩)
  | cipher request tail ih =>
    constructor
    · intro h
      cases h with
      | cipher _ _ _ recorded ht =>
        obtain ⟨middle, hm, hv⟩ := (ih (Spec.IdealCipher.answer family request)).mp ht
        exact ⟨middle, .cipher request tail middle recorded hm, hv⟩
    · rintro ⟨middle, hm, hv⟩
      cases hm with
      | cipher _ _ _ recorded ht =>
        exact .cipher request _ value recorded ((ih _).mpr ⟨middle, ht, hv⟩)

theorem liftCipher_value (family : Spec.IdealCipher.Family Key Block) (table : Input → Option Digest)
    (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (program : Spec.OracleProgram.Program (Spec.IdealCipher.Query Key Block) Block A) (value : A)
    (h : Evaluates family table ciphers (liftCipher program) value)
    (history : List (Spec.IdealCipher.Entry Key Block)) :
    (Spec.IdealCipherProgram.execute family program history).1 = value := by
  induction program generalizing value history with
  | done a => cases h; rfl
  | query request next ih =>
    cases h with
    | cipher _ _ _ _ ht => exact ih _ value ht _

theorem liftCipher_history (family : Spec.IdealCipher.Family Key Block) (table : Input → Option Digest)
    (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (program : Spec.OracleProgram.Program (Spec.IdealCipher.Query Key Block) Block A) (value : A)
    (h : Evaluates family table ciphers (liftCipher program) value)
    (history : List (Spec.IdealCipher.Entry Key Block)) (hh : history ⊆ ciphers) :
    (Spec.IdealCipherProgram.execute family program history).2 ⊆ ciphers := by
  induction program generalizing value history with
  | done a => exact hh
  | query request next ih =>
    cases h with
    | cipher _ _ _ recorded ht =>
      apply ih _ value ht
      intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · exact recorded
      · exact hh he

variable [Fintype Digest] [Nonempty Digest]

theorem run_preserves (p : Spec.HashCipher.Procedure Input Digest Key Block State)
    (family : Spec.IdealCipher.Family Key Block) (fuel : Nat) (state : State)
    (table : Input → Option Digest) (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (out : Spec.HashCipher.Result Input Digest Key Block State)
    (hout : out ∈ (Spec.HashCipher.runFixed p family fuel state table hashes ciphers).support) :
    (∀ input answer, table input = some answer → out.hashTable input = some answer) ∧ ciphers ⊆ out.cipherHistory := by
  induction fuel generalizing state table hashes ciphers out with
  | zero =>
    simp only [Spec.HashCipher.runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    exact ⟨fun _ _ h => h, List.Subset.refl _⟩
  | succ fuel ih =>
    obtain ⟨action, _, ha⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      rw [PMF.mem_support_pure_iff] at ha
      subst out
      exact ⟨fun _ _ h => h, List.Subset.refl _⟩
    | cipher request next =>
      have h := ih (next (Spec.IdealCipher.answer family request)) table hashes _ out ha
      exact ⟨h.1, fun _ he => h.2 (List.mem_cons_of_mem _ he)⟩
    | hash input next =>
      obtain ⟨result, hq, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp ha
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst out
      have h := ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers tail ht
      exact ⟨fun query answer hstored => h.1 query answer
        (OracleProgram.query_preserves_answer table input query answer hstored result hq), h.2⟩

/-- Completion and coverage come from the real operational run, including
calls that were absent in the prefix and every repeated request. -/
theorem run_evaluates (family : Spec.IdealCipher.Family Key Block) (program : Program Input Digest Key Block A)
    (budget : Nat) (hbound : Bounded budget program) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (out : Spec.HashCipher.Result Input Digest Key Block (Program Input Digest Key Block A))
    (hout : out ∈ (Spec.HashCipher.runFixed procedure family budget program table hashes ciphers).support) :
    ∃ value, out.state = .done value ∧ Evaluates family out.hashTable out.cipherHistory program value := by
  induction budget generalizing program table hashes ciphers out with
  | zero =>
    cases program with
    | done value =>
      simp only [Spec.HashCipher.runFixed, PMF.mem_support_pure_iff] at hout
      subst out
      exact ⟨value, rfl, .done value⟩
    | hash _ _ => exact False.elim hbound
    | cipher _ _ => exact False.elim hbound
  | succ budget ih =>
    cases program with
    | done value =>
      simp only [Spec.HashCipher.runFixed, procedure, PMF.pure_bind, PMF.mem_support_pure_iff] at hout
      subst out
      exact ⟨value, rfl, .done value⟩
    | hash input next =>
      simp only [Spec.HashCipher.runFixed, procedure, PMF.pure_bind] at hout
      obtain ⟨result, hq, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst out
      obtain ⟨value, hv, heval⟩ := ih (next result.1) (hbound result.1) result.2 _ ciphers tail ht
      refine ⟨value, hv, .hash input next result.1 value ?_ heval⟩
      exact (run_preserves procedure family budget (next result.1) result.2 _ ciphers tail ht).1 input result.1
        (OracleProgram.query_stores_answer table input result hq)
    | cipher request next =>
      simp only [Spec.HashCipher.runFixed, procedure, PMF.pure_bind] at hout
      obtain ⟨value, hv, heval⟩ := ih (next (Spec.IdealCipher.answer family request)) (hbound _) table hashes _ out hout
      refine ⟨value, hv, .cipher request next value ?_ heval⟩
      exact (run_preserves procedure family budget (next (Spec.IdealCipher.answer family request)) table hashes _ out hout).2 (by simp)

end
end SDitH.Proofs.HashCipherEvaluation
