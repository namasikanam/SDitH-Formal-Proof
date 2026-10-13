import SDitH.Proofs.GamePrune

/-! The game run from the resampled pruned world is below the run from the
resampled world evaluated on the pruned result, plus the final touching
indicator under the pruned run. This is the forward agreement applied to
the complementary event: both evaluations are probabilities, so bounding
the complement of the event from the real world bounds the event from the
pruned world. -/

namespace SDitH.Proofs.GamePruneReverse

open Spec.SignatureSecurity Spec.IdealCipher
open Spec.DomainSeparation (Bits)
open GameResample ChargeExpect ChargeCutExpect CipherResample SharedPrune HiddenEntries RunWorld GamePrune
open Spec.RandomOracleTrap (indicator)
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}

omit [Fintype Digest] [Nonempty Digest] in
/-- The mean of the complement of a bounded function. -/
theorem mean_one_sub {α : Type*} (p : PMF α) (φ : α → ℝ≥0∞) (hφ : ∀ a, φ a ≤ 1) :
    mean p (fun a => 1 - φ a) = 1 - mean p φ := by
  have h1 : mean p (fun a => 1 - φ a) + mean p φ = 1 := by
    rw [← mean_add]
    simp only [tsub_add_cancel_of_le (hφ _)]
    exact mean_const p 1
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (mean_le_const _ _ 1 fun a _ => hφ a)) h1

/-- The game run from the resampled pruned world is below the run from the
resampled world on the pruned result plus the final touching indicator
under the pruned run. -/
theorem prune_le_runW (K : List (Bits lambda))
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsignLaw : ∀ sk m, PostLaw resample (scheme.sign sk m))
    (hpubLaw : ∀ q, PostLaw resample (scheme.publicOracle q))
    (hsignP : ∀ sk m, PruneLaw K (scheme.sign sk m))
    (hpubP : ∀ q, PruneLaw K (scheme.publicOracle q))
    (hprepP : ∀ pk m sig, PruneLaw K (scheme.prepareVerification pk m sig))
    (hsignG : ∀ sk m, Grows (scheme.sign sk m)) (hpubG : ∀ q, Grows (scheme.publicOracle q))
    (hprepG : ∀ pk m sig, Grows (scheme.prepareVerification pk m sig))
    (hsignK : ∀ sk m, Keeps (scheme.sign sk m)) (hpubK : ∀ q, Keeps (scheme.publicOracle q))
    (Φ : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞)
    (hΦ : FamilyFreeT Φ) (hle : ∀ r, Φ r ≤ 1)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : GW HashInput Digest lambda s wit rnd)
    (trace : Trace Message HashInput Query) (hcons : Consistent world) :
    mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) Φ) ≤
      mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
        Φ (withWorld r.1 (pruneW K r.2), pruneW K r.2)) +
      mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
        indicator (touchesG K r.2)) := by
  have hΦ'free : FamilyFreeT fun r => 1 - Φ r := fun t w f => by
    show 1 - Φ (withWorld t (setFamily w f), setFamily w f) = 1 - Φ (withWorld t w, w)
    rw [hΦ t w f]
  have hΦ'le : ∀ r, (fun r => 1 - Φ r) r ≤ 1 := fun r => tsub_le_self
  have h := runW_le_prune K scheme adversary hsignLaw hpubLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK
    (fun r => 1 - Φ r) hΦ'free hΦ'le fuel pk sk state world trace hcons
  set a := mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
    Φ (withWorld r.1 (pruneW K r.2), pruneW K r.2)) with ha
  set b := mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) Φ)
    with hb
  set t := mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
    indicator (touchesG K r.2)) with ht
  have ha1 : a ≤ 1 := mean_le_const _ _ 1 fun w _ => mean_le_const _ _ 1 fun r _ => hle _
  have hb1 : b ≤ 1 := mean_le_const _ _ 1 fun w _ => mean_le_const _ _ 1 fun r _ => hle _
  have hL : mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
      (fun r => 1 - Φ r) (withWorld r.1 (pruneW K r.2), pruneW K r.2)) = 1 - a := by
    rw [ha, ← mean_one_sub _ _ (fun w => mean_le_const _ _ 1 fun r _ => hle _)]
    refine congrArg _ (funext fun w => ?_)
    exact mean_one_sub _ _ fun r => hle _
  have hR : mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
      (fun r => 1 - Φ r) r + indicator (touchesG K r.2)) = (1 - b) + t := by
    rw [hb, ht, ← mean_one_sub _ _ (fun w => mean_le_const _ _ 1 fun r _ => hle _), ← mean_add]
    refine congrArg _ (funext fun w => ?_)
    rw [mean_add, mean_one_sub _ _ fun r => hle _]
  rw [hL, hR] at h
  have h1 : 1 ≤ (t + a) + (1 - b) := by
    calc (1 : ℝ≥0∞) = (1 - a) + a := (tsub_add_cancel_of_le ha1).symm
      _ ≤ ((1 - b) + t) + a := add_le_add h le_rfl
      _ = (t + a) + (1 - b) := by ring
  have h2 : 1 - (1 - b) ≤ t + a := tsub_le_iff_right.mpr h1
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hb1] at h2
  rw [add_comm] at h2
  exact h2

end
end SDitH.Proofs.GamePruneReverse
