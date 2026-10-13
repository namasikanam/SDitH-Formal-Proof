import SDitH.Spec.IdealCipher
import SDitH.Proofs.FinitePosterior
import SDitH.Assumptions

namespace SDitH.Proofs.IdealCipher

open Spec.IdealCipher
open scoped Classical ENNReal
noncomputable section

variable {Key Block State R : Type*}

theorem entry_matches_iff (family : Family Key Block) (request : Query Key Block) (value : Block) :
    family (entry request value).key (entry request value).input = (entry request value).output ↔
      answer family request = value := by
  cases request with
  | encrypt key input => rfl
  | decrypt key output =>
    change family key value = output ↔ (family key).symm output = value
    constructor
    · intro h
      rw [← h, Equiv.symm_apply_apply]
    · intro h
      rw [← h, Equiv.apply_symm_apply]

theorem matches_cons (family : Family Key Block) (history : List (Entry Key Block))
    (request : Query Key Block) (value : Block) :
    Matches family (entry request value :: history) ↔ Matches family history ∧ answer family request = value := by
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_cons_of_mem _ he),
      (entry_matches_iff family request value).mp (h _ (List.mem_cons_self))⟩
  · rintro ⟨hf, ha⟩ e he
    rcases List.mem_cons.mp he with rfl | he
    · exact (entry_matches_iff family request value).mpr ha
    · exact hf e he

/-- New compatible families are exactly the old compatible families in the
fiber of the observed forward or inverse answer. -/
def observedEquiv (world : World Key Block) (request : Query Key Block) (sample : Candidates world) :
    Candidates (observe world request (answer sample.val request) ⟨sample.val, sample.property, rfl⟩) ≃
      FinitePosterior.Fiber (fun f : Candidates world => answer f.val request) sample where
  toFun family :=
    ⟨⟨family.val, ((matches_cons family.val world.history request _).mp family.property).1⟩,
      ((matches_cons family.val world.history request _).mp family.property).2⟩
  invFun family := ⟨family.val.val, (matches_cons _ _ _ _).mpr ⟨family.val.property, family.property⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

variable [Fintype Key] [Fintype Block]

theorem posterior_step (world : World Key Block) (request : Query Key Block)
    (next : Block → List (Entry Key Block) → Family Key Block → PMF R) :
    (PMF.uniformOfFintype (Candidates world)).bind (fun sample =>
      (PMF.uniformOfFintype (Candidates
        (observe world request (answer sample.val request) ⟨sample.val, sample.property, rfl⟩))).bind fun family =>
          next (answer sample.val request) (entry request (answer sample.val request) :: world.history) family.val) =
    (PMF.uniformOfFintype (Candidates world)).bind (fun family =>
      next (answer family.val request) (entry request (answer family.val request) :: world.history) family.val) := by
  calc
    _ = (PMF.uniformOfFintype (Candidates world)).bind (fun sample =>
        (PMF.uniformOfFintype (FinitePosterior.Fiber (fun f : Candidates world => answer f.val request) sample)).bind
          fun family => next (answer sample.val request)
            (entry request (answer sample.val request) :: world.history) family.val.val) := by
      congr 1
      funext sample
      rw [← IntegerSamplingProbability.map_uniform_equiv (observedEquiv world request sample).symm, PMF.bind_map]
      rfl
    _ = _ := FinitePosterior.fiber_bind (fun f : Candidates world => answer f.val request)
      (fun value family => next value (entry request value :: world.history) family.val)

/-- Exact adaptive equivalence. The adversary may randomize, repeat queries,
change keys and switch between encryption and decryption after every answer. -/
theorem runPosterior_eq (procedure : Procedure Key Block State) (budget : Nat)
    (state : State) (world : World Key Block) :
    runPosterior procedure budget state world =
      (PMF.uniformOfFintype (Candidates world)).bind (fun family =>
        runFixed procedure family.val budget state world.history) := by
  induction budget generalizing state world with
  | zero => simp only [runPosterior, runFixed, PMF.bind_const]
  | succ budget ih =>
    simp only [runPosterior, runFixed]
    rw [PMF.bind_comm]
    congr 1
    funext action
    cases action with
    | stop => simp only [PMF.bind_const]
    | query request next =>
      simp only [query, PMF.bind_map, Function.comp_def]
      simp_rw [ih]
      exact posterior_step world request (fun value history family => runFixed procedure family budget (next value) history)

def emptyEquiv : Candidates (empty : World Key Block) ≃ Family Key Block where
  toFun family := family.val
  invFun family := ⟨family, by simp [empty, Matches]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem experiments_eq (procedure : Procedure Key Block State) (budget : Nat) (initial : State) :
    experimentPosterior procedure budget initial = experimentFixed procedure budget initial := by
  rw [experimentPosterior, runPosterior_eq, experimentFixed,
    ← IntegerSamplingProbability.map_uniform_equiv (emptyEquiv (Key := Key) (Block := Block)), PMF.bind_map]
  rfl

/-- Link the once-sampled experiment to the existing standalone ICM model. -/
theorem experiment_assumption_model (procedure : Procedure Key Block State) (budget : Nat) (initial : State) :
    experimentPosterior procedure budget initial =
      (Assumptions.idealCipherFamily Key Block).bind (fun family => runFixed procedure family budget initial []) :=
  experiments_eq procedure budget initial

theorem query_repeat_encrypt (world : World Key Block) (key : Key) (input output : Block)
    (h : (⟨key, input, output⟩ : Entry Key Block) ∈ world.history) :
    (query world (.encrypt key input)).map Prod.fst = PMF.pure output := by
  simp only [query, PMF.map_comp, Function.comp_def]
  have he : (fun family : Candidates world => answer family.val (.encrypt key input)) = fun _ => output := by
    funext family
    exact family.property _ h
  rw [he]
  exact PMF.map_const _ _

theorem query_repeat_decrypt (world : World Key Block) (key : Key) (input output : Block)
    (h : (⟨key, input, output⟩ : Entry Key Block) ∈ world.history) :
    (query world (.decrypt key output)).map Prod.fst = PMF.pure input := by
  simp only [query, PMF.map_comp, Function.comp_def]
  have he : (fun family : Candidates world => answer family.val (.decrypt key output)) = fun _ => input := by
    funext family
    exact (entry_matches_iff family.val (.decrypt key output) input).mp (family.property _ h)
  rw [he]
  exact PMF.map_const _ _

end
end SDitH.Proofs.IdealCipher
