import SDitH.Proofs.TreeRunEntries
import SDitH.Proofs.SeedTree

/-! The commitment calls' run. The commitment calls over a list of leaf
pairs record only entries whose inputs are the layout's inputs of cipher
inputs at the leaf-count-shifted offsets of listed pairs, over the
starting history, and finish; the leaf pairs are without duplicates, so a
pair of the initial segment differs from the last pair; and the
commitment addresses lie below twice the leaf count. -/

namespace SDitH.Proofs.CommitEntries

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open RowsSupport RunBind PrefixOrMention TreeRunEntries HeadCommitSplit
open scoped Classical

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The commitment call of a leaf pair from the tree. -/
def commitOf (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (nodes : Nat → Seed lambda) (pair : Fin tau × Fin (2 ^ kappa)) :
    SignerProgram lambda s wit rnd (Digest lambda) :=
  commitCall layout (tau * 2 ^ kappa) variant salt (nodes (leafNode pair.1 pair.2).val) (Spec.SeedTree.leafOffset pair.1 pair.2)

/-- The entry recorded by one of a pair's commitment calls. -/
def commitEntry (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (nodes : Nat → Seed lambda) (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (pair : Fin tau × Fin (2 ^ kappa)) (b : Bool) : Spec.IdealCipher.Entry (Bits lambda) (Bits lambda) :=
  Spec.IdealCipher.entry (.encrypt (layout.key (nodes (leafNode pair.1 pair.2).val))
      (layout.input (cipherInput variant salt (tau * 2 ^ kappa + Spec.SeedTree.leafOffset pair.1 pair.2) b)))
    (family (layout.key (nodes (leafNode pair.1 pair.2).val))
      (layout.input (cipherInput variant salt (tau * 2 ^ kappa + Spec.SeedTree.leafOffset pair.1 pair.2) b)))

/-- The inputs recorded by the commitment calls over a list of pairs. -/
def CommitInput (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (L : List (Fin tau × Fin (2 ^ kappa))) (x : Bits lambda) : Prop :=
  ∃ pair ∈ L, ∃ b : Bool, x = layout.input (cipherInput variant salt (tau * 2 ^ kappa + Spec.SeedTree.leafOffset pair.1 pair.2) b)

/-- The commitment calls over a list record only the pairs' inputs, over the
starting history. -/
theorem commit_entries (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (nodes : Nat → Seed lambda) (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (L : List (Fin tau × Fin (2 ^ kappa))) :
    ∀ (acc : Fin tau × Fin (2 ^ kappa) → Digest lambda) (table : List Bool → Option (Out lambda s wit rnd))
      (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
      (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd)))
      (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
        (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda))),
      out ∈ (runFixed procedure family (L.length * 2) (collect (commitOf layout variant salt nodes) L acc)
        table hashes ciphers log).support →
      ∃ new, out.cipherHistory = new ++ ciphers ∧ ∀ e ∈ new, CommitInput layout variant salt L e.input := by
  induction L with
  | nil =>
    intro acc table hashes ciphers log out hout
    simp only [List.length_nil, Nat.zero_mul, runFixed, PMF.mem_support_pure_iff] at hout
    subst hout
    exact ⟨[], rfl, fun e he => absurd he (List.not_mem_nil)⟩
  | cons k rest ih =>
    intro acc table hashes ciphers log out hout
    have hp : Bounded 2 (commitOf (s := s) (wit := wit) (rnd := rnd) layout variant salt nodes k) :=
      SharedSigner.commitCall_bounded layout _ variant salt _ _
    have hn : ∀ v, Bounded (rest.length * 2)
        (collect (commitOf (s := s) (wit := wit) (rnd := rnd) layout variant salt nodes) rest (Function.update acc k v)) :=
      fun _ => SharedSigner.collect_bounded _ 2 (fun pair => SharedSigner.commitCall_bounded layout _ variant salt _ _) _ _
    rw [show (k :: rest).length * 2 = 2 + rest.length * 2 by simp [List.length_cons]; ring, collect,
      runFixed_bind family 2 (rest.length * 2) _ _ hp hn] at hout
    obtain ⟨mid, hmid, hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    have hrun := expand_run_support layout variant salt _ _ (fun pair => concatenate pair.1 pair.2) family _ _ _ _ mid hmid
    subst hrun
    unfold continueRun at hcont
    simp only at hcont
    obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hcont
    subst heq
    obtain ⟨new₁, hnew₁, hform₁⟩ := ih _ _ _ _ _ inner hinner
    refine ⟨new₁ ++ [commitEntry layout variant salt nodes family k true, commitEntry layout variant salt nodes family k false],
      ?_, fun e he => ?_⟩
    · show inner.cipherHistory = _
      rw [hnew₁, List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
      rfl
    · rcases List.mem_append.mp he with h | h
      · obtain ⟨pair, hpair, b, hx⟩ := hform₁ e h
        exact ⟨pair, List.mem_cons_of_mem k hpair, b, hx⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact ⟨k, List.mem_cons_self .., true, rfl⟩
        · exact ⟨k, List.mem_cons_self .., false, rfl⟩

/-- The leaf pairs are without duplicates. -/
theorem allPairs_nodup : (Spec.SharedSlopeExec.allPairs tau kappa).Nodup := by
  unfold Spec.SharedSlopeExec.allPairs
  refine List.nodup_flatMap.mpr ⟨fun e _ => (List.nodup_finRange _).map fun i j h => (Prod.mk.inj h).2, ?_⟩
  refine (List.nodup_finRange tau).pairwise_of_forall_ne fun e₁ _ e₂ _ hne => ?_
  intro p hp₁ hp₂
  obtain ⟨i₁, -, rfl⟩ := List.mem_map.mp hp₁
  obtain ⟨i₂, -, h⟩ := List.mem_map.mp hp₂
  exact hne (Prod.mk.inj h).1.symm

/-- A pair of the initial segment differs from the last pair. -/
theorem ne_lastPair_of_mem_dropLast (htau : tau ≠ 0) (pair : Fin tau × Fin (2 ^ kappa))
    (h : pair ∈ (Spec.SharedSlopeExec.allPairs tau kappa).dropLast) : pair ≠ lastPair (kappa := kappa) htau := by
  intro heq
  have hnd := allPairs_nodup (tau := tau) (kappa := kappa)
  rw [← allPairs_split htau] at hnd
  exact List.disjoint_of_nodup_append hnd h (List.mem_singleton.mpr heq)

/-- A commitment address lies below twice the leaf count. -/
theorem commit_address_lt (pair : Fin tau × Fin (2 ^ kappa)) :
    tau * 2 ^ kappa + Spec.SeedTree.leafOffset pair.1 pair.2 < 2 * (tau * 2 ^ kappa) := by
  have := SeedTree.leafOffset_lt pair.1 pair.2
  omega

end
end SDitH.Proofs.CommitEntries
