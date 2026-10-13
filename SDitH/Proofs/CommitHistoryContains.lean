import SDitH.Proofs.CommitRunExchange
import SDitH.Proofs.TreeOfMatches

/-! The commitment run's history contains the expansion's entries. The
commitment run is the rest of the commitment from the expanded tree over
the expansion's entries appended to the starting history, and a run only
extends its history; so any family matching a history that extends the
run's final history computes the signature's hidden keys. -/

namespace SDitH.Proofs.CommitHistoryContains

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SharedScheme
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open HiddenLeafNode TreeRunClosed RunHistoryShift CommitRunExchange TreeOfMatches HiddenTuple
open scoped Classical

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)

/-- The commitment run's final history contains the expansion's entries
and the starting history. -/
theorem commitRun_contains (f : Family (Bits lambda) (Bits lambda)) (root : Bits lambda)
    (table : List Bool → Option (Out lambda s wit rnd)) (hashes : List (List Bool × Out lambda s wit rnd))
    (ciphers : List (Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd)))
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd)))
    (hout : out ∈ (runFixed procedure f (commitBudget tau kappa) (commitProgram S salt root witness) table hashes ciphers
      log).support) :
    ∀ e, e ∈ treeHistory S.layout f S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1) ++ ciphers →
      e ∈ out.cipherHistory := by
  rw [commitRun_eq, runFixed_history_shift] at hout
  obtain ⟨out₀, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  intro e he
  simp only [appendHistory, List.mem_append]
  exact Or.inr (List.mem_append.mp he)

/-- The commitment run from a world records the expansion's entries. -/
theorem commit_contains (w : World lambda s wit rnd) (root : Bits lambda)
    (r : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) ×
      World lambda s wit rnd)
    (hr : r ∈ (runProgram (commitBudget tau kappa) (commitProgram S salt root witness) w).support) :
    ∀ e, e ∈ treeHistory S.layout w.family S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1) →
      e ∈ r.2.cipherHistory := by
  simp only [runProgram, PMF.mem_support_map_iff] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  intro e he
  exact commitRun_contains S salt witness w.family root _ _ _ _ out hout e (List.mem_append_left _ he)

/-- Any family matching a history that extends the commitment run's final
history computes the signature's hidden keys. -/
theorem mem_hiddenKeysAll_commit (w : World lambda s wit rnd) (root : Bits lambda)
    (r : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) ×
      World lambda s wit rnd)
    (hr : r ∈ (runProgram (commitBudget tau kappa) (commitProgram S salt root witness) w).support)
    (H : List (Entry (Bits lambda) (Bits lambda))) (hsub : ∀ e ∈ r.2.cipherHistory, e ∈ H)
    (g' : Family (Bits lambda) (Bits lambda)) (hm : Matches g' H) (hidden : Fin tau → Fin (2 ^ kappa)) (x : Bits lambda) :
    x ∈ hiddenKeysAll S.layout g' S.variant salt root hidden ↔ x ∈ hiddenKeysAll S.layout w.family S.variant salt root hidden :=
  mem_hiddenKeysAll_of_matches S.layout w.family S.variant salt root (fun _ => root) g' H hm
    (fun e he => hsub e (commit_contains S salt witness w root r hr e he)) hidden x

end
end SDitH.Proofs.CommitHistoryContains
