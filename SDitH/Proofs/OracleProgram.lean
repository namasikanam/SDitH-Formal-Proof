import SDitH.Spec.OracleProgram
import SDitH.Proofs.RandomOracleCollisionInvariant

namespace SDitH.Proofs.OracleProgram

open Spec.OracleProgram Spec.RandomOracleCollision
open scoped Classical
noncomputable section

variable {Input Output A B : Type*}

theorem bounded_bind (program : Program Input Output A) (next : A → Program Input Output B)
    (q k : Nat) (hp : Bounded q program) (hn : ∀ a, Bounded k (next a)) :
    Bounded (q + k) (bind program next) := by
  induction q generalizing program with
  | zero =>
    cases program with
    | done value => simpa only [Spec.OracleProgram.bind, Nat.zero_add] using hn value
    | query input tail => exact False.elim hp
  | succ q ih =>
    cases program with
    | done value =>
      have hmono : ∀ n (p : Program Input Output B), Bounded n p → Bounded (q + 1 + n) p := by
        intro n p h
        induction n generalizing p with
        | zero => cases p <;> simp_all [Bounded]
        | succ n ih =>
          cases p with
          | done value => trivial
          | query input tail =>
            simp only [Bounded] at h ⊢
            exact fun answer => ih (tail answer) (h answer)
      exact hmono k (next value) (hn value)
    | query input tail =>
      rw [Spec.OracleProgram.bind, Nat.add_right_comm q 1 k]
      exact fun answer => ih (tail answer) (hp answer)

theorem bounded_map (program : Program Input Output A) (f : A → B) (q : Nat) (h : Bounded q program) :
    Bounded q (map f program) := by
  simpa only [Nat.add_zero] using bounded_bind program (fun a => .done (f a)) q 0 h (fun _ => trivial)

theorem bounded_array (n : Nat) (inputs : Fin n → Input) : Bounded n (array n inputs : Program Input Output _) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    intro answer
    exact bounded_map (array n (fun i => inputs i.succ))
      (Fin.cons (α := fun _ : Fin (n + 1) => Output) answer) n
      (ih (fun i => inputs i.succ))

theorem evaluates_bind (table : Input → Option Output) (program : Program Input Output A)
    (next : A → Program Input Output B) (value : B) :
    Evaluates table (bind program next) value ↔
      ∃ intermediate, Evaluates table program intermediate ∧ Evaluates table (next intermediate) value := by
  induction program with
  | done a =>
    constructor
    · exact fun h => ⟨a, .done a, h⟩
    · rintro ⟨_, h, htail⟩
      cases h
      exact htail
  | query input tail ih =>
    constructor
    · intro h
      cases h with
      | query _ _ answer _ stored ht =>
        obtain ⟨middle, hm, hv⟩ := (ih answer).mp ht
        exact ⟨middle, .query input tail answer middle stored hm, hv⟩
    · rintro ⟨middle, hm, hv⟩
      cases hm with
      | query _ _ answer _ stored ht =>
        exact .query input _ answer value stored ((ih answer).mpr ⟨middle, ht, hv⟩)

theorem evaluates_map (table : Input → Option Output) (program : Program Input Output A)
    (f : A → B) (value : B) : Evaluates table (map f program) value ↔
      ∃ a, Evaluates table program a ∧ f a = value := by
  rw [map, evaluates_bind]
  constructor
  · rintro ⟨a, ha, hv⟩
    cases hv
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, .done _⟩

theorem evaluates_array (table : Input → Option Output) (n : Nat) (inputs : Fin n → Input)
    (answers : Fin n → Output) (h : Evaluates table (array n inputs) answers) :
    ∀ i, table (inputs i) = some (answers i) := by
  induction n with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
    cases h with
    | query _ _ answer _ stored ht =>
      obtain ⟨rest, hr, he⟩ := (evaluates_map _ _ _ _).mp ht
      subst answers
      intro i
      exact Fin.cases stored (fun j => ih _ rest hr j) i

variable [Fintype Output] [Nonempty Output]

theorem query_stores_answer (table : Input → Option Output) (input : Input)
    (result : Output × (Input → Option Output)) (hr : result ∈ (Spec.RandomOracle.query table input).support) :
    result.2 input = some result.1 := by
  unfold Spec.RandomOracle.query at hr
  cases he : table input with
  | some old =>
    rw [he, PMF.mem_support_pure_iff] at hr
    subst result
    exact he
  | none =>
    rw [he] at hr
    obtain ⟨answer, _, h⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst result
    simp

theorem query_preserves_answer (table : Input → Option Output) (input q : Input) (answer : Output)
    (hq : table q = some answer) (result : Output × (Input → Option Output))
    (hr : result ∈ (Spec.RandomOracle.query table input).support) : result.2 q = some answer := by
  unfold Spec.RandomOracle.query at hr
  cases he : table input with
  | some old =>
    rw [he, PMF.mem_support_pure_iff] at hr
    subst result
    exact hq
  | none =>
    rw [he] at hr
    obtain ⟨fresh, _, h⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst result
    have hne : q ≠ input := by
      intro heq
      subst q
      rw [he] at hq
      contradiction
    simpa [Function.update_of_ne hne] using hq

theorem run_preserves_answer (p : Procedure Input Output A) (fuel : Nat) (state : A)
    (table : Input → Option Output) (history : List (Input × Output)) (q : Input) (answer : Output)
    (hq : table q = some answer) (out : Result Input Output A)
    (hout : out ∈ (run p fuel state table history).support) : out.table q = some answer := by
  induction fuel generalizing state table history out with
  | zero =>
    simp only [run, PMF.mem_support_pure_iff] at hout
    subst out
    exact hq
  | succ fuel ih =>
    obtain ⟨action, _, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      rw [PMF.mem_support_pure_iff] at hnext
      subst out
      exact hq
    | query input next =>
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst out
      exact ih (next result.1) result.2 _ (query_preserves_answer table input q answer hq result hr) tail ht

/-- A sufficient query budget finishes the program and yields an evaluation
against the actual final table. No coverage check can discard its executions. -/
theorem run_evaluates (program : Program Input Output A) (budget : Nat) (hbound : Bounded budget program)
    (table : Input → Option Output) (history : List (Input × Output))
    (out : Result Input Output (Program Input Output A))
    (hout : out ∈ (run procedure budget program table history).support) :
    ∃ value, out.state = .done value ∧ Evaluates out.table program value := by
  induction budget generalizing program table history out with
  | zero =>
    cases program with
    | query input next => exact False.elim hbound
    | done value =>
      simp only [run, PMF.mem_support_pure_iff] at hout
      subst out
      exact ⟨value, rfl, .done value⟩
  | succ budget ih =>
    cases program with
    | done value =>
      simp only [run, procedure, PMF.pure_bind, PMF.mem_support_pure_iff] at hout
      subst out
      exact ⟨value, rfl, .done value⟩
    | query input next =>
      simp only [run, procedure, PMF.pure_bind] at hout
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst out
      obtain ⟨value, hv, heval⟩ := ih (next result.1) (hbound result.1) result.2 _ tail ht
      refine ⟨value, hv, .query input next result.1 value ?_ heval⟩
      exact run_preserves_answer procedure budget (next result.1) result.2 _ input result.1
        (query_stores_answer table input result hr) tail ht

end
end SDitH.Proofs.OracleProgram
