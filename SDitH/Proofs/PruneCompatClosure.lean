import SDitH.Proofs.GamePruneGen
import SDitH.Proofs.ForkRestoreEnd
import SDitH.Proofs.HiddenSlice

/-! Closure of prune compatibility under the steps of the hybrid's
continuations: a family-free and prune-free evaluation is compatible with
the touching indicator; compatibility is kept by resampling the world
before the evaluation, by averaging over a sample, by restoring the world's
family and history into a base world, by updating the hash table, and by
the finalization of the terminal. -/

namespace SDitH.Proofs.PruneCompatClosure

open Spec.SignatureSecurity
open Spec.IdealCipher (Family)
open Spec.RandomOracleTrap (indicator)
open Spec.DomainSeparation (Bits)
open GameResample ChargeExpect ChargeCutExpect CipherResample SharedPrune HiddenEntries RunWorld GamePrune GamePruneReverse
open GamePruneGen ForkRestore ForkRestoreLemmas ForkRestoreEnd HiddenSlice
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat} (K : List (Bits lambda))

omit [Fintype Digest] [Nonempty Digest] in
/-- Resampling twice is resampling once. -/
theorem mean_resampleW_resampleW (world : GW HashInput Digest lambda s wit rnd) (G : GW HashInput Digest lambda s wit rnd → ℝ≥0∞) :
    mean (resampleW resample world) (fun w => mean (resampleW resample w) G) = mean (resampleW resample world) G := by
  refine (mean_congr_support _ _ (fun _ => mean (resampleW resample world) G) fun w hw => ?_).trans (mean_const _ _)
  obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW world w hw
  rw [resampleW_setFamily]

omit [Fintype Digest] [Nonempty Digest] in
/-- A family-free and prune-free evaluation is compatible, with the
touching indicator as its functional. -/
theorem pruneCompat_free
    (Φ : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞) (hle : ∀ r, Φ r ≤ 1) (hfam : FamilyFreeT Φ)
    (hpr : ∀ t w, Φ (withWorld t (pruneW K w), pruneW K w) = Φ (withWorld t w, w)) :
    PruneCompat K Φ (fun r => indicator (touchesG K r.2)) where
  le_one := hle
  touch_le _ := le_rfl
  forward t world _ := by
    rw [mean_resampleW_const (fun w => Φ (withWorld t w, w)) (fun w f => hfam t w f),
      mean_resampleW_const (fun w => Φ (withWorld t w, w) + indicator (touchesG K w)) (fun w f => by
        show Φ (withWorld t (setFamily w f), setFamily w f) + indicator (touchesG K (setFamily w f)) = _
        rw [hfam t w f]
        rfl), hpr]
    exact le_self_add
  reverse t world _ := by
    rw [mean_resampleW_const (fun w => Φ (withWorld t w, w)) (fun w f => hfam t w f),
      mean_resampleW_const (fun w => Φ (withWorld t w, w)) (fun w f => hfam t w f), hpr]
    exact le_self_add

omit [Fintype Digest] [Nonempty Digest] in
/-- Compatibility is kept by resampling the world before the evaluation. -/
theorem pruneCompat_resample
    (Φ T : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞) (hc : PruneCompat K Φ T) :
    PruneCompat K (fun r => mean (resampleW resample r.2) fun w' => Φ (withWorld r.1 w', w'))
      (fun r => mean (resampleW resample r.2) fun w' => T (withWorld r.1 w', w')) where
  le_one r := mean_le_const _ _ 1 fun w' _ => hc.le_one _
  touch_le r := by
    by_cases ht : touchesG K r.2 = true
    · rw [ht]
      calc indicator true = mean (resampleW resample r.2) (fun _ => (1 : ℝ≥0∞)) := by rw [mean_const]; rfl
        _ ≤ _ := mean_le_mean _ _ _ fun w' hw' => by
            have ht' := touchesG_of_mem_resampleW K r.2 w' hw' ht
            calc (1 : ℝ≥0∞) = indicator (touchesG K w') := by rw [ht']; rfl
              _ ≤ _ := hc.touch_le (withWorld r.1 w', w')
    · rw [Bool.not_eq_true] at ht
      rw [ht]
      exact zero_le _
  forward t world hw := by
    simp only [withWorld_withWorld, ← mean_add]
    rw [mean_resampleW_resampleW, mean_resampleW_resampleW]
    exact hc.forward t world hw
  reverse t world hw := by
    simp only [withWorld_withWorld]
    rw [mean_resampleW_resampleW, mean_resampleW_resampleW, mean_resampleW_resampleW]
    exact hc.reverse t world hw

omit [Fintype Digest] [Nonempty Digest] in
/-- Compatibility is kept by averaging over a sample. -/
theorem pruneCompat_sample {X : Type*} (p : PMF X)
    (Φ T : X → Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞) (hc : ∀ x, PruneCompat K (Φ x) (T x)) :
    PruneCompat K (fun r => mean p fun x => Φ x r) (fun r => mean p fun x => T x r) where
  le_one r := mean_le_const _ _ 1 fun x _ => (hc x).le_one r
  touch_le r := by
    calc indicator (touchesG K r.2) = mean p (fun _ => indicator (touchesG K r.2)) := (mean_const _ _).symm
      _ ≤ _ := mean_le_mean _ _ _ fun x _ => (hc x).touch_le r
  forward t world hw := by
    simp only [← mean_add]
    rw [mean_comm]
    conv_rhs => rw [mean_comm]
    exact mean_le_mean _ _ _ fun x _ => (hc x).forward t world hw
  reverse t world hw := by
    have hL : mean (resampleW resample (pruneW K world)) (fun w => mean p fun x => Φ x (withWorld t w, w)) =
        mean p (fun x => mean (resampleW resample (pruneW K world)) fun w => Φ x (withWorld t w, w)) := mean_comm _ _ _
    have hR1 : mean (resampleW resample world) (fun w => mean p fun x => Φ x (withWorld t w, w)) =
        mean p (fun x => mean (resampleW resample world) fun w => Φ x (withWorld t w, w)) := mean_comm _ _ _
    have hR2 : mean (resampleW resample (pruneW K world)) (fun w => mean p fun x => T x (withWorld t w, w)) =
        mean p (fun x => mean (resampleW resample (pruneW K world)) fun w => T x (withWorld t w, w)) := mean_comm _ _ _
    rw [hL, hR1, hR2, ← mean_add]
    exact mean_le_mean _ _ _ fun x _ => (hc x).reverse t world hw

omit [Fintype Digest] [Nonempty Digest] in
/-- Compatibility of a world-only evaluation is kept by restoring the
world's family and history into a base world. -/
theorem pruneCompat_restore (B : GW HashInput Digest lambda s wit rnd) (G GT : GW HashInput Digest lambda s wit rnd → ℝ≥0∞)
    (hc : PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K (fun r => G r.2) (fun r => GT r.2)) :
    PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K (fun r => G (restore B r.2))
      (fun r => GT (restore B r.2)) where
  le_one r := hc.le_one (r.1, restore B r.2)
  touch_le r := hc.touch_le (r.1, restore B r.2)
  forward t world hw := by
    have h := hc.forward t (restore B world) hw
    have hp : pruneW K (restore B world) = restore B (pruneW K world) := rfl
    rw [hp, ← mean_resampleW_restore, ← mean_resampleW_restore] at h
    exact h
  reverse t world hw := by
    have h := hc.reverse t (restore B world) hw
    have hp : pruneW K (restore B world) = restore B (pruneW K world) := rfl
    rw [hp, ← mean_resampleW_restore, ← mean_resampleW_restore, ← mean_resampleW_restore] at h
    exact h

omit [Fintype Digest] [Nonempty Digest] in
/-- Compatibility of a world-only evaluation is kept by updating the hash
table. -/
theorem pruneCompat_update (U : (HashInput → Option Digest) → (HashInput → Option Digest))
    (G GT : GW HashInput Digest lambda s wit rnd → ℝ≥0∞)
    (hc : PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K (fun r => G r.2) (fun r => GT r.2)) :
    PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
      (fun r => G { r.2 with hashTable := U r.2.hashTable }) (fun r => GT { r.2 with hashTable := U r.2.hashTable }) where
  le_one r := hc.le_one (r.1, { r.2 with hashTable := U r.2.hashTable })
  touch_le r := hc.touch_le (r.1, { r.2 with hashTable := U r.2.hashTable })
  forward t world hw := by
    have h := hc.forward t { world with hashTable := U world.hashTable } hw
    have hp : pruneW K { world with hashTable := U world.hashTable } =
        { pruneW K world with hashTable := U (pruneW K world).hashTable } := rfl
    rw [hp, ← mean_resampleW_update', ← mean_resampleW_update'] at h
    exact h
  reverse t world hw := by
    have h := hc.reverse t { world with hashTable := U world.hashTable } hw
    have hp : pruneW K { world with hashTable := U world.hashTable } =
        { pruneW K world with hashTable := U (pruneW K world).hashTable } := rfl
    rw [hp, ← mean_resampleW_update', ← mean_resampleW_update', ← mean_resampleW_update'] at h
    exact h

omit [Fintype Digest] [Nonempty Digest] in
/-- A game world with its family and cipher history replaced. -/
def adjust (w : GW HashInput Digest lambda s wit rnd) (f : Family (Bits lambda) (Bits lambda))
    (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) : GW HashInput Digest lambda s wit rnd :=
  { w with other := { w.other with family := f, cipherHistory := H } }

/-- A finalization's result carries the finalized terminal. -/
theorem finalize_terminal (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (c : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (hc : c ∈ (finalize t).support) : c.terminal = t := by
  cases t with
  | attempt a =>
    simp only [finalize, PMF.mem_support_map_iff] at hc
    obtain ⟨result, -, rfl⟩ := hc
    rfl
  | exhausted trace => simp only [finalize, PMF.mem_support_pure_iff] at hc; subst hc; rfl
  | aborted trace => simp only [finalize, PMF.mem_support_pure_iff] at hc; subst hc; rfl
  | rejected trace => simp only [finalize, PMF.mem_support_pure_iff] at hc; subst hc; rfl

/-- The finalization of a terminal with its world replaced reads only the
world's hash table: with a world of the same table, it is the finalization
with that world and the terminal's world replaced afterwards. -/
theorem finalize_withWorld_table (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (w X : GW HashInput Digest lambda s wit rnd) (h : w.hashTable = X.hashTable) :
    finalize (withWorld t w) = (finalize (withWorld t X)).map fun c => { c with terminal := withWorld c.terminal w } := by
  cases t with
  | attempt a =>
    simp only [withWorld, finalize, PMF.map_comp, Function.comp_def, h]
  | exhausted trace => simp only [withWorld, finalize, PMF.pure_map]
  | aborted trace => simp only [withWorld, finalize, PMF.pure_map]
  | rejected trace => simp only [withWorld, finalize, PMF.pure_map]

/-- Compatibility is kept by the finalization of the terminal, for an
evaluation of the checked result and the world that does not read the
checked terminal's embedded world. -/
theorem pruneCompat_finalize
    (Ψ TΨ : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query →
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞)
    (hΨ : ∀ t w' f H b₁ b₂ w, Ψ ⟨withWorld t (adjust w' f H), b₁, b₂⟩ w = Ψ ⟨withWorld t w', b₁, b₂⟩ w)
    (hTΨ : ∀ t w' f H b₁ b₂ w, TΨ ⟨withWorld t (adjust w' f H), b₁, b₂⟩ w = TΨ ⟨withWorld t w', b₁, b₂⟩ w)
    (hc : ∀ c, PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K (fun r => Ψ c r.2)
      (fun r => TΨ c r.2)) :
    PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
      (fun r => mean (finalize r.1) fun c => Ψ c r.2) (fun r => mean (finalize r.1) fun c => TΨ c r.2) where
  le_one r := mean_le_const _ _ 1 fun c _ => (hc c).le_one r
  touch_le r := by
    calc indicator (touchesG K r.2) = mean (finalize r.1) (fun _ => indicator (touchesG K r.2)) := (mean_const _ _).symm
      _ ≤ _ := mean_le_mean _ _ _ fun c _ => (hc c).touch_le r
  forward t world hw := by
    have hfin : ∀ (F : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query →
        GW HashInput Digest lambda s wit rnd → ℝ≥0∞),
        (∀ t w' f H b₁ b₂ w, F ⟨withWorld t (adjust w' f H), b₁, b₂⟩ w = F ⟨withWorld t w', b₁, b₂⟩ w) →
        ∀ (X : GW HashInput Digest lambda s wit rnd), X.hashTable = world.hashTable →
        (∀ w ∈ (resampleW resample X).support, w = adjust world w.other.family w.other.cipherHistory) →
        ∀ w ∈ (resampleW resample X).support,
        mean (finalize (withWorld t w)) (fun c => F c w) = mean (finalize (withWorld t world)) (fun c => F c w) := by
      intro F hF X hX hXadj w hw
      rw [finalize_withWorld_table t w world ((hashTable_of_mem resample X w hw).trans hX), mean_map]
      refine mean_congr_support _ _ _ fun c hc => ?_
      have hct := finalize_terminal (withWorld t world) c hc
      rcases c with ⟨ct, b₁, b₂⟩
      simp only at hct
      subst hct
      have hw' := hXadj w hw
      calc F ⟨withWorld (withWorld t world) w, b₁, b₂⟩ w
          = F ⟨withWorld t (adjust world w.other.family w.other.cipherHistory), b₁, b₂⟩ w := by
            rw [withWorld_withWorld, ← hw']
        _ = _ := hF t world _ _ b₁ b₂ w
    calc _ = mean (resampleW resample world) (fun w => mean (finalize (withWorld t world)) fun c => Ψ c w) :=
          mean_congr_support _ _ _ fun w hw => by
            dsimp only
            exact hfin Ψ hΨ world rfl (fun w hw => by obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW world w hw; rfl) w hw
      _ = mean (finalize (withWorld t world)) (fun c => mean (resampleW resample world) fun w => Ψ c w) := mean_comm _ _ _
      _ ≤ mean (finalize (withWorld t world)) (fun c => mean (resampleW resample (pruneW K world)) fun w => Ψ c w + TΨ c w) :=
          mean_le_mean _ _ _ fun c _ => (hc c).forward t world hw
      _ = mean (resampleW resample (pruneW K world)) (fun w => mean (finalize (withWorld t world)) fun c => Ψ c w + TΨ c w) :=
          mean_comm _ _ _
      _ = _ := mean_congr_support _ _ _ fun w hw => by
          dsimp only
          rw [← mean_add]
          exact (hfin (fun c w => Ψ c w + TΨ c w) (fun t w' f H b₁ b₂ w => by simp only [hΨ, hTΨ]) (pruneW K world) rfl (fun w hw => by obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW (pruneW K world) w hw; rfl) w hw).symm
  reverse t world hw := by
    have hfin : ∀ (F : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query →
        GW HashInput Digest lambda s wit rnd → ℝ≥0∞),
        (∀ t w' f H b₁ b₂ w, F ⟨withWorld t (adjust w' f H), b₁, b₂⟩ w = F ⟨withWorld t w', b₁, b₂⟩ w) →
        ∀ (X : GW HashInput Digest lambda s wit rnd), X.hashTable = world.hashTable →
        (∀ w ∈ (resampleW resample X).support, w = adjust world w.other.family w.other.cipherHistory) →
        ∀ w ∈ (resampleW resample X).support,
        mean (finalize (withWorld t w)) (fun c => F c w) = mean (finalize (withWorld t world)) (fun c => F c w) := by
      intro F hF X hX hXadj w hw
      rw [finalize_withWorld_table t w world ((hashTable_of_mem resample X w hw).trans hX), mean_map]
      refine mean_congr_support _ _ _ fun c hc => ?_
      have hct := finalize_terminal (withWorld t world) c hc
      rcases c with ⟨ct, b₁, b₂⟩
      simp only at hct
      subst hct
      have hw' := hXadj w hw
      calc F ⟨withWorld (withWorld t world) w, b₁, b₂⟩ w
          = F ⟨withWorld t (adjust world w.other.family w.other.cipherHistory), b₁, b₂⟩ w := by
            rw [withWorld_withWorld, ← hw']
        _ = _ := hF t world _ _ b₁ b₂ w
    calc _ = mean (resampleW resample (pruneW K world)) (fun w => mean (finalize (withWorld t world)) fun c => Ψ c w) :=
          mean_congr_support _ _ _ fun w hw => by
            dsimp only
            exact hfin Ψ hΨ (pruneW K world) rfl (fun w hw => by obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW (pruneW K world) w hw; rfl) w hw
      _ = mean (finalize (withWorld t world)) (fun c => mean (resampleW resample (pruneW K world)) fun w => Ψ c w) :=
          mean_comm _ _ _
      _ ≤ mean (finalize (withWorld t world)) (fun c => mean (resampleW resample world) (fun w => Ψ c w) +
            mean (resampleW resample (pruneW K world)) (fun w => TΨ c w)) :=
          mean_le_mean _ _ _ fun c _ => (hc c).reverse t world hw
      _ = mean (finalize (withWorld t world)) (fun c => mean (resampleW resample world) (fun w => Ψ c w)) +
            mean (finalize (withWorld t world)) (fun c => mean (resampleW resample (pruneW K world)) (fun w => TΨ c w)) :=
          mean_add _ _ _
      _ = mean (resampleW resample world) (fun w => mean (finalize (withWorld t world)) fun c => Ψ c w) +
            mean (resampleW resample (pruneW K world)) (fun w => mean (finalize (withWorld t world)) fun c => TΨ c w) := by
          rw [mean_comm, mean_comm (finalize (withWorld t world))]
      _ = _ := by
          refine congrArg₂ _ ?_ ?_
          · exact mean_congr_support _ _ _ fun w hw => by
              dsimp only
              exact (hfin Ψ hΨ world rfl (fun w hw => by obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW world w hw; rfl) w hw).symm
          · exact mean_congr_support _ _ _ fun w hw => by
              dsimp only
              exact (hfin TΨ hTΨ (pruneW K world) rfl (fun w hw => by obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW (pruneW K world) w hw; rfl) w hw).symm

end
end SDitH.Proofs.PruneCompatClosure
