import SDitH.Proofs.SignStep
import SDitH.Proofs.SimulatedSign

/-! Hash tables supported by at most n inputs. A query's table is the old
table or its update at the queried input, so a query adds at most one
input; the honest signing performs one hash query, and the simulated
signing programs at most one input, so both add at most one input. This
invariant will bound the input-present event along the game. -/

namespace SDitH.Proofs.TableSupport

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open SignStep
open scoped Classical

noncomputable section

section Generic

variable {Input Output : Type*}

/-- A table supported by at most n inputs. -/
def Supported (table : Input → Option Output) (n : Nat) : Prop :=
  ∃ s : Finset Input, s.card ≤ n ∧ ∀ x, table x ≠ none → x ∈ s

theorem supported_mono {table : Input → Option Output} {n m : Nat} (h : Supported table n) (hnm : n ≤ m) :
    Supported table m :=
  let ⟨s, hs, hmem⟩ := h
  ⟨s, hs.trans hnm, hmem⟩

theorem supported_empty (n : Nat) : Supported (fun _ : Input => (none : Option Output)) n :=
  ⟨∅, by simp, fun _ hx => absurd rfl hx⟩

/-- An update at one input adds at most one input. -/
theorem supported_update {inst : DecidableEq Input} {table : Input → Option Output} {n : Nat} (h : Supported table n)
    (x : Input) (d : Output) : Supported (@Function.update Input (fun _ => Option Output) inst table x (some d)) (n + 1) := by
  obtain ⟨s, hs, hmem⟩ := h
  refine ⟨insert x s, (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hs), fun y hy => ?_⟩
  by_cases hxy : y = x
  · subst hxy
    exact Finset.mem_insert_self _ _
  · rw [Function.update_of_ne hxy] at hy
    exact Finset.mem_insert_of_mem (hmem y hy)

variable [Fintype Output] [Nonempty Output]

/-- A query's table: the old table or its update at the input. -/
theorem query_table {inst : DecidableEq Input} (table : Input → Option Output) (input : Input)
    (result : Output × (Input → Option Output))
    (hr : result ∈ (@Spec.RandomOracle.query Input Output inst _ _ table input).support) :
    result.2 = table ∨ result.2 = @Function.update Input (fun _ => Option Output) inst table input (some result.1) := by
  unfold Spec.RandomOracle.query at hr
  cases he : table input with
  | some old =>
    rw [he, PMF.mem_support_pure_iff] at hr
    subst hr
    exact Or.inl rfl
  | none =>
    rw [he] at hr
    obtain ⟨d, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    exact Or.inr rfl

/-- A query adds at most one input. -/
theorem supported_query {inst : DecidableEq Input} {table : Input → Option Output} {n : Nat} (h : Supported table n)
    (input : Input) (result : Output × (Input → Option Output))
    (hr : result ∈ (@Spec.RandomOracle.query Input Output inst _ _ table input).support) :
    Supported result.2 (n + 1) := by
  rcases query_table table input result hr with h2 | h2
  · rw [h2]
    exact supported_mono h (Nat.le_succ n)
  · rw [h2]
    exact supported_update h _ _

end Generic

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The honest signing's table is a query's table. -/
theorem honest_sign_table (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (result)
    (hr : result ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign (publicKey, witness)
      message world).support) :
    ∃ (input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (hashResult : Spec.BAVC.Digest lambda × (HashInput (List Bool) (List Bool) (Payload F lambda higherCount) →
        Option (Spec.BAVC.Digest lambda))),
      hashResult ∈ (Spec.RandomOracle.query world.hashTable input).support ∧ result.2.hashTable = hashResult.2 := by
  rw [honest_sign_eq] at hr
  obtain ⟨salt, _, h1⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨root, _, h2⟩ := (PMF.mem_support_bind_iff _ _ _).mp h1
  obtain ⟨res, _, h3⟩ := (PMF.mem_support_bind_iff _ _ _).mp h2
  obtain ⟨hashResult, hq, h4⟩ := (PMF.mem_support_bind_iff _ _ _).mp h3
  obtain ⟨opened, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp h4
  subst heq
  exact ⟨_, hashResult, hq, rfl⟩

/-- The honest signing adds at most one input to the table. -/
theorem honest_sign_supported (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    {n : Nat} (h : Supported world.hashTable n) (result)
    (hr : result ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign (publicKey, witness)
      message world).support) :
    Supported result.2.hashTable (n + 1) := by
  obtain ⟨input, hashResult, hq, heq⟩ := honest_sign_table S V verifyBudget publicKey sampleWitness witness message world
    result hr
  rw [heq]
  exact supported_query h input hashResult hq

/-- The simulated signing adds at most one input to the table. -/
theorem simulatedSign_supported (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    {n : Nat} (h : Supported world.hashTable n) (result)
    (hr : result ∈ (simulatedSign S publicKey message world).support) :
    Supported result.2.hashTable (n + 1) := by
  obtain ⟨salt, root, fake, committed, _, _, hcase⟩ := SimulatedSign.simulatedSign_support S publicKey message world result hr
  rcases hcase with ⟨_, htable⟩ | ⟨counter, opening, _, _, _, htable⟩
  · rw [htable]
    exact supported_mono h (Nat.le_succ n)
  · rw [htable]
    exact supported_update h _ _

end
end SDitH.Proofs.TableSupport
