import SDitH.Proofs.CommitHistoryContains
import SDitH.Proofs.GamePrune
import SDitH.Proofs.SharedResample
import SDitH.Proofs.HiddenSlice
import SDitH.Proofs.ForkOutcome
import SDitH.Proofs.PruneLawRun

/-! The bridge from a signing call to the game's pruned run. A signing call
is the commitment run on the inner world followed by a post-processing
with the outer hash table; its output's hidden keys are read from the
output world's family and the signature's hidden tuple, and they are
determined by the recorded history, so a consistent resampling of the
output world leaves them unchanged. From a resampled start, the call
followed by the game run evaluated on the pruned result is below the call
followed by the resampled pruned run with the touching indicator, by the
game's pruned-run agreement at the output's keys. -/

namespace SDitH.Proofs.SignBridge

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SharedScheme Spec.SignatureSecurity
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeysExchange HiddenTuple CommitHistoryContains GamePrune RunWorld SharedResample
open ChargeExpect CipherResample SharedPrune PruneLawRun ForkOutcome HiddenSlice GameResample
open scoped Classical ENNReal

noncomputable section

variable {HashInput Digest : Type*} [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2) (root : Bits lambda)
  {Sig : Type*}
  (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) →
    (HashInput → Option Digest) → PMF (Sig × (HashInput → Option Digest)))
  (hidden : Sig → Fin tau → Fin (2 ^ kappa))

/-- The signing-shaped oracle: the commitment run on the inner world, then
the post-processing with the outer table. -/
def commitOracle (w : GW HashInput Digest lambda s wit rnd) : PMF (Sig × GW HashInput Digest lambda s wit rnd) :=
  (runProgram (commitBudget tau kappa) (commitProgram S salt root witness) w.other).bind fun r =>
    (post r.1 w.hashTable).map fun q => (q.1, ⟨q.2, r.2⟩)

/-- The hidden keys of an output: from its world's family and its
signature's hidden tuple. -/
def outKeys (r : Sig × GW HashInput Digest lambda s wit rnd) : List (Bits lambda) :=
  hiddenKeysAll S.layout r.2.other.family S.variant salt root (hidden r.1)

omit [Fintype Digest] [Nonempty Digest] in
/-- The oracle obeys the resampling law. -/
theorem commitOracle_postLaw : PostLaw resample (commitOracle S salt witness root post) :=
  postLaw_run (commitBudget tau kappa) (commitProgram S salt root witness) post

omit [Fintype Digest] [Nonempty Digest] in
/-- The oracle keeps consistency. -/
theorem commitOracle_consistent (w : GW HashInput Digest lambda s wit rnd) (hw : Consistent w)
    (r : Sig × GW HashInput Digest lambda s wit rnd) (hr : r ∈ (commitOracle S salt witness root post w).support) :
    Consistent r.2 := by
  unfold commitOracle at hr
  obtain ⟨res, hres, hq⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨q, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hq
  simp only [runProgram, PMF.mem_support_map_iff] at hres
  obtain ⟨out, hout, rfl⟩ := hres
  exact runFixed_matches _ _ _ _ _ _ _ _ out hout hw

omit [Fintype Digest] [Nonempty Digest] in
/-- Resampling keeps the inner history. -/
theorem history_of_mem_resampleW (w w' : GW HashInput Digest lambda s wit rnd)
    (hw' : w' ∈ (resampleW resample w).support) : w'.other.cipherHistory = w.other.cipherHistory := by
  simp only [resampleW, resample, PMF.map_comp, PMF.support_map] at hw'
  obtain ⟨f, -, rfl⟩ := hw'
  rfl

omit [Fintype Digest] [Nonempty Digest] in
/-- Pruning depends on the key list only through its members. -/
theorem pruneW_congr_mem (K₁ K₂ : List (Bits lambda)) (h : ∀ x, x ∈ K₁ ↔ x ∈ K₂) (w : GW HashInput Digest lambda s wit rnd) :
    pruneW K₁ w = pruneW K₂ w := by
  simp only [pruneW, pruneShared, pruneAt_congr_mem K₁ K₂ h]

omit [Fintype Digest] [Nonempty Digest] in
/-- The output's hidden keys have the same members after a consistent
resampling of the output world. -/
theorem outKeys_congr (w : GW HashInput Digest lambda s wit rnd) (hw : Consistent w)
    (r : Sig × GW HashInput Digest lambda s wit rnd) (hr : r ∈ (commitOracle S salt witness root post w).support)
    (w' : GW HashInput Digest lambda s wit rnd) (hw' : w' ∈ (resampleW resample r.2).support) (x : Bits lambda) :
    x ∈ outKeys S salt root hidden (r.1, w') ↔ x ∈ outKeys S salt root hidden r := by
  have hcr : Consistent r.2 := commitOracle_consistent S salt witness root post w hw r hr
  have hcw' : Consistent w' := consistent_of_mem_resampleW _ _ hw' (possible_of_consistent _ hcr)
  have hhist := history_of_mem_resampleW _ _ hw'
  unfold commitOracle at hr
  obtain ⟨res, hres, hq⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨q, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hq
  unfold outKeys
  simp only at hhist ⊢
  rw [runProgram_family _ _ _ res hres]
  exact mem_hiddenKeysAll_commit S salt witness w.other root res hres w'.other.cipherHistory
    (fun e he => by rw [hhist]; exact he) w'.other.family hcw' (hidden q.1) x

variable {PublicKey SecretKey Message Query Answer State : Type*}

/-- The bridge: from a resampled start, the signing call followed by the
game run evaluated on the result pruned at the output's hidden keys is
below the call followed by the resampled pruned run with the touching
indicator, given the game's pruned-run agreement at any fixed key list. -/
theorem sign_bridge
    (scheme : Scheme PublicKey SecretKey Message Sig HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query Answer)
    (adversary : Adversary PublicKey Message Sig HashInput Digest Query Answer State)
    (hprune : ∀ (K : List (Bits lambda))
      (Φ : Terminal Message Sig HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
        GW HashInput Digest lambda s wit rnd → ℝ≥0∞), FamilyFreeT Φ → (∀ r, Φ r ≤ 1) →
      ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : GW HashInput Digest lambda s wit rnd)
        (trace : Trace Message HashInput Query), Consistent world →
        mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
          Φ (withWorld r.1 (pruneW K r.2), pruneW K r.2)) ≤
        mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
          Φ r + indicator (touchesG K r.2)))
    (Φ : Terminal Message Sig HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞) (hΦ : FamilyFreeT Φ) (hle : ∀ r, Φ r ≤ 1)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (next : Sig → State) (trace : Trace Message HashInput Query)
    (w₀ : GW HashInput Digest lambda s wit rnd) (hw₀ : Consistent w₀) :
    mean (resampleW resample w₀) (fun w => mean (commitOracle S salt witness root post w) fun r =>
        mean (runW scheme adversary fuel pk sk (next r.1) r.2 trace) fun t =>
          Φ (withWorld t.1 (pruneW (outKeys S salt root hidden r) t.2), pruneW (outKeys S salt root hidden r) t.2)) ≤
      mean (resampleW resample w₀) (fun w => mean (commitOracle S salt witness root post w) fun r =>
        mean (resampleW resample (pruneW (outKeys S salt root hidden r) r.2)) fun w' =>
          mean (runW scheme adversary fuel pk sk (next r.1) w' trace) fun t =>
            Φ t + indicator (touchesG (outKeys S salt root hidden r) t.2)) := by
  rw [postLaw_mean (commitOracle_postLaw S salt witness root post) w₀]
  refine mean_le_mean _ _ _ fun w hw => ?_
  have hcw : Consistent w := consistent_of_mem_resampleW _ _ hw (possible_of_consistent _ hw₀)
  refine mean_le_mean _ _ _ fun r hr => ?_
  have hcr : Consistent r.2 := commitOracle_consistent S salt witness root post w hcw r hr
  calc _ = mean (resampleW resample r.2) (fun w' => mean (runW scheme adversary fuel pk sk (next r.1) w' trace) fun t =>
          Φ (withWorld t.1 (pruneW (outKeys S salt root hidden r) t.2), pruneW (outKeys S salt root hidden r) t.2)) :=
        mean_congr_support _ _ _ fun w' hw' => by
          simp only [pruneW_congr_mem _ _ (outKeys_congr S salt witness root post hidden w hcw r hr w' hw')]
    _ ≤ _ := hprune (outKeys S salt root hidden r) Φ hΦ hle fuel pk sk (next r.1) r.2 trace hcr

end
end SDitH.Proofs.SignBridge
