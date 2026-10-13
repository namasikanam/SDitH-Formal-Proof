import SDitH.Proofs.GamePrune
import SDitH.Proofs.GamePruneReverse

/-! The pruned-run agreement for prune-compatible continuations. The
agreement of the pruned run was stated for a family-free evaluation of the
final result read at the pruned result; the hybrid's continuations read
the history (the fork's second branch starts from the first's final
history), so the evaluation is generalised to one compatible with pruning:
with a touching functional dominating the touching indicator, its mean
over the resampled world is below its mean over the resampled pruned world
plus the touching functional's, and conversely. The game run preserves the
compatibility, with the evaluation read at the actual result. -/

namespace SDitH.Proofs.GamePruneGen

open Spec.SignatureSecurity
open Spec.IdealCipher (Family)
open Spec.RandomOracleTrap (indicator)
open Spec.DomainSeparation (Bits)
open GameResample ChargeExpect ChargeCutExpect CipherResample SharedPrune HiddenEntries RunWorld GamePrune GamePruneReverse
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}

/-- An evaluation of a terminal with its world compatible with pruning at
the keys, with its touching functional. -/
structure PruneCompat (K : List (Bits lambda))
    (Φ T : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞) : Prop where
  le_one : ∀ r, Φ r ≤ 1
  touch_le : ∀ r, indicator (touchesG K r.2) ≤ T r
  forward : ∀ (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (world : GW HashInput Digest lambda s wit rnd), Consistent world →
    mean (resampleW resample world) (fun w => Φ (withWorld t w, w)) ≤
      mean (resampleW resample (pruneW K world)) (fun w => Φ (withWorld t w, w) + T (withWorld t w, w))
  reverse : ∀ (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (world : GW HashInput Digest lambda s wit rnd), Consistent world →
    mean (resampleW resample (pruneW K world)) (fun w => Φ (withWorld t w, w)) ≤
      mean (resampleW resample world) (fun w => Φ (withWorld t w, w)) +
        mean (resampleW resample (pruneW K world)) (fun w => T (withWorld t w, w))

omit [Fintype Digest] [Nonempty Digest] in
/-- A probability's complement is below the complement's bound plus a term
exactly when the bounds exchange. -/
theorem one_sub_le_iff (a b t : ℝ≥0∞) (ha : a ≤ 1) (hb : b ≤ 1) : 1 - a ≤ (1 - b) + t ↔ b ≤ a + t := by
  constructor
  · intro h
    have h1 : 1 ≤ (t + a) + (1 - b) := by
      calc (1 : ℝ≥0∞) = (1 - a) + a := (tsub_add_cancel_of_le ha).symm
        _ ≤ ((1 - b) + t) + a := add_le_add h le_rfl
        _ = (t + a) + (1 - b) := by ring
    have h2 : 1 - (1 - b) ≤ t + a := tsub_le_iff_right.mpr h1
    rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hb, add_comm] at h2
    exact h2
  · intro h
    refine tsub_le_iff_right.mpr ?_
    calc (1 : ℝ≥0∞) = (1 - b) + b := (tsub_add_cancel_of_le hb).symm
      _ ≤ (1 - b) + (a + t) := add_le_add le_rfl h
      _ = (1 - b) + t + a := by ring

omit [Fintype Digest] [Nonempty Digest] in
/-- The complement of a compatible evaluation is compatible with the same
touching functional. -/
theorem pruneCompat_compl (K : List (Bits lambda))
    (Φ T : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞) (hc : PruneCompat K Φ T) :
    PruneCompat K (fun r => 1 - Φ r) T where
  le_one _ := tsub_le_self
  touch_le := hc.touch_le
  forward t world hw := by
    have ha : mean (resampleW resample world) (fun w => Φ (withWorld t w, w)) ≤ 1 :=
      mean_le_const _ _ 1 fun w _ => hc.le_one _
    have hb : mean (resampleW resample (pruneW K world)) (fun w => Φ (withWorld t w, w)) ≤ 1 :=
      mean_le_const _ _ 1 fun w _ => hc.le_one _
    rw [mean_one_sub _ _ (fun w => hc.le_one _), mean_add, mean_one_sub _ _ (fun w => hc.le_one _)]
    exact (one_sub_le_iff _ _ _ ha hb).mpr (hc.reverse t world hw)
  reverse t world hw := by
    have ha : mean (resampleW resample world) (fun w => Φ (withWorld t w, w)) ≤ 1 :=
      mean_le_const _ _ 1 fun w _ => hc.le_one _
    have hb : mean (resampleW resample (pruneW K world)) (fun w => Φ (withWorld t w, w)) ≤ 1 :=
      mean_le_const _ _ 1 fun w _ => hc.le_one _
    rw [mean_one_sub _ _ (fun w => hc.le_one _), mean_one_sub _ _ (fun w => hc.le_one _)]
    exact (one_sub_le_iff _ _ _ hb ha).mpr (by rw [← mean_add]; exact hc.forward t world hw)

variable (K : List (Bits lambda))
  (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (hsignLaw : ∀ sk m, PostLaw resample (scheme.sign sk m))
  (hpubLaw : ∀ q, PostLaw resample (scheme.publicOracle q))
  (hprepLaw : ∀ pk m sig, PostLaw resample (scheme.prepareVerification pk m sig))
  (hsignP : ∀ sk m, PruneLaw K (scheme.sign sk m))
  (hpubP : ∀ q, PruneLaw K (scheme.publicOracle q))
  (hprepP : ∀ pk m sig, PruneLaw K (scheme.prepareVerification pk m sig))
  (hsignG : ∀ sk m, Grows (scheme.sign sk m)) (hpubG : ∀ q, Grows (scheme.publicOracle q))
  (hprepG : ∀ pk m sig, Grows (scheme.prepareVerification pk m sig))
  (hsignK : ∀ sk m, Keeps (scheme.sign sk m)) (hpubK : ∀ q, Keeps (scheme.publicOracle q))
  (hprepK : ∀ pk m sig, Keeps (scheme.prepareVerification pk m sig))
  (Φ T : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
    GW HashInput Digest lambda s wit rnd → ℝ≥0∞)
  (hc : PruneCompat K Φ T)

include hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK hprepK hc in
/-- The game run from the resampled world, evaluated by a compatible
evaluation at its result, is below the run from the resampled pruned world
evaluated with the touching functional added. -/
theorem runW_le_prune_gen :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : GW HashInput Digest lambda s wit rnd)
      (trace : Trace Message HashInput Query), Consistent world →
      mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) Φ) ≤
      mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
        Φ r + T r) := by
  -- the touched continuation is at least one
  have htouched : ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State)
      (o : GW HashInput Digest lambda s wit rnd) (trace : Trace Message HashInput Query), touchesG K o = true →
      1 ≤ mean (resampleW resample o) (fun w' => mean (runW scheme adversary fuel pk sk state w' trace) fun r =>
        Φ r + T r) := by
    intro fuel pk sk state o trace ho
    calc (1 : ℝ≥0∞) = mean (resampleW resample o) (fun w' =>
          mean (runW scheme adversary fuel pk sk state w' trace) fun _ => 1) := by simp only [mean_const]
      _ ≤ _ := mean_le_mean _ _ _ fun w' hw' => mean_le_mean _ _ _ fun r hr => by
          have ht := touchesG_runW K scheme adversary hsignG hpubG hprepG fuel pk sk state w' trace
            (touchesG_of_mem_resampleW K o w' hw' ho) r hr
          calc (1 : ℝ≥0∞) = indicator (touchesG K r.2) := by rw [ht]; rfl
            _ ≤ T r := hc.touch_le r
            _ ≤ _ := le_add_self
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state world trace hcons
    simp only [runW, mean_pure]
    exact hc.forward (.exhausted trace) world hcons
  | succ fuel ih =>
    intro pk sk state world trace hcons
    have hposs : Possible world := possible_of_consistent world hcons
    simp only [runW, mean_bind]
    rw [mean_comm]
    conv_rhs => rw [mean_comm]
    refine mean_le_mean _ _ _ fun action _ => ?_
    cases action with
    | abort =>
      dsimp only
      simp only [mean_pure]
      exact hc.forward (.aborted trace) world hcons
    | finish message signature =>
      dsimp only
      simp only [mean_map]
      -- the terminal of a preparation result, read with a world
      set T₀ : Option HashInput → GW HashInput Digest lambda s wit rnd →
          Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query := fun a w =>
        match a with
        | none => Terminal.rejected trace
        | some input => Terminal.attempt ⟨message, signature, input, scheme.signatureDigest signature, w, trace⟩ with hT₀
      have hT₀w : ∀ a w w', withWorld (T₀ a w) w' = T₀ a w' := by
        intro a w w'
        cases a <;> rfl
      set Ψ : Option HashInput × GW HashInput Digest lambda s wit rnd → ℝ≥0∞ := fun r =>
        min 1 (mean (resampleW resample r.2) fun w' => Φ (T₀ r.1 w', w') + T (T₀ r.1 w', w')) with hΨ
      have hΨfree : FamilyFreeG Ψ := by
        intro a w f
        simp only [hΨ, resampleW_setFamily]
      have hΨle : ∀ r, Ψ r ≤ 1 := fun r => min_le_left _ _
      calc _ = mean (resampleW resample world) (fun w => mean (scheme.prepareVerification pk message signature w) fun r =>
            Φ (T₀ r.1 r.2, r.2)) := by
            refine congrArg _ (funext fun w => congrArg _ (funext fun r => ?_))
            rcases r with ⟨a, o⟩
            cases a <;> rfl
        _ = mean (resampleW resample world) (fun w => mean (scheme.prepareVerification pk message signature w) fun r =>
            mean (resampleW resample r.2) fun w' => Φ (T₀ r.1 w', w')) :=
            postLaw_mean (hprepLaw pk message signature) world (fun r => Φ (T₀ r.1 r.2, r.2))
        _ ≤ mean (resampleW resample world) (fun w => mean (scheme.prepareVerification pk message signature w) fun r =>
            Ψ (r.1, pruneW K r.2)) := by
            refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
            simp only [hΨ]
            refine le_min (mean_le_const _ _ 1 fun w' _ => hc.le_one _) ?_
            have hcr : Consistent r.2 :=
              hprepK pk message signature w r (consistent_of_mem_resampleW world w hw hposs) hr
            have h := hc.forward (T₀ r.1 r.2) r.2 hcr
            simp only [hT₀w] at h
            exact h
        _ ≤ mean (resampleW resample (pruneW K world)) (fun w =>
            mean (scheme.prepareVerification pk message signature w) fun r => if touchesG K r.2 then 1 else Ψ r) :=
            hprepP pk message signature world hposs Ψ hΨfree hΨle
        _ ≤ mean (resampleW resample (pruneW K world)) (fun w =>
            mean (scheme.prepareVerification pk message signature w) fun r =>
              mean (resampleW resample r.2) fun w' => Φ (T₀ r.1 w', w') + T (T₀ r.1 w', w')) := by
            refine mean_le_mean _ _ _ fun w _ => mean_le_mean _ _ _ fun r _ => ?_
            by_cases ht : touchesG K r.2 = true
            · rw [if_pos ht]
              calc (1 : ℝ≥0∞) = mean (resampleW resample r.2) (fun _ => 1) := (mean_const _ _).symm
                _ ≤ _ := mean_le_mean _ _ _ fun w' hw' => by
                    have ht' := touchesG_of_mem_resampleW K r.2 w' hw' ht
                    calc (1 : ℝ≥0∞) = indicator (touchesG K w') := by rw [ht']; rfl
                      _ ≤ T (T₀ r.1 w', w') := hc.touch_le _
                      _ ≤ _ := le_add_self
            · rw [if_neg ht]
              exact min_le_right _ _
        _ = mean (resampleW resample (pruneW K world)) (fun w =>
            mean (scheme.prepareVerification pk message signature w) fun r => Φ (T₀ r.1 r.2, r.2) + T (T₀ r.1 r.2, r.2)) :=
            (postLaw_mean (hprepLaw pk message signature) (pruneW K world)
              (fun r => Φ (T₀ r.1 r.2, r.2) + T (T₀ r.1 r.2, r.2))).symm
        _ = _ := by
            refine congrArg _ (funext fun w => congrArg _ (funext fun r => ?_))
            rcases r with ⟨a, o⟩
            cases a <;> rfl
    | sign message next =>
      dsimp only
      simp only [mean_bind]
      rw [postLaw_mean (hsignLaw sk message) world]
      conv_rhs => rw [postLaw_mean (hsignLaw sk message) (pruneW K world)]
      set Ψ : Signature × GW HashInput Digest lambda s wit rnd → ℝ≥0∞ := fun r =>
        min 1 (mean (resampleW resample r.2) fun w' =>
          mean (runW scheme adversary fuel pk sk (next r.1) w'
            { trace with signingRequests := message :: trace.signingRequests }) fun r' => Φ r' + T r') with hΨ
      have hΨfree : FamilyFreeG Ψ := by
        intro a w f
        simp only [hΨ, resampleW_setFamily]
      have hΨle : ∀ r, Ψ r ≤ 1 := fun r => min_le_left _ _
      calc _ ≤ mean (resampleW resample world) (fun w => mean (scheme.sign sk message w) fun r =>
            Ψ (r.1, pruneW K r.2)) := by
            refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
            simp only [hΨ]
            refine le_min (mean_le_const _ _ 1 fun w' _ => mean_le_const _ _ 1 fun r' _ => hc.le_one _) ?_
            exact ih pk sk (next r.1) r.2 _ (hsignK sk message w r (consistent_of_mem_resampleW world w hw hposs) hr)
        _ ≤ mean (resampleW resample (pruneW K world)) (fun w => mean (scheme.sign sk message w) fun r =>
            if touchesG K r.2 then 1 else Ψ r) := hsignP sk message world hposs Ψ hΨfree hΨle
        _ ≤ _ := by
            refine mean_le_mean _ _ _ fun w _ => mean_le_mean _ _ _ fun r _ => ?_
            by_cases ht : touchesG K r.2 = true
            · rw [if_pos ht]
              exact htouched fuel pk sk (next r.1) r.2 _ ht
            · rw [if_neg ht]
              exact min_le_right _ _
    | hash input next =>
      dsimp only
      simp only [mean_bind]
      rw [mean_hash_step world input (fun d w' => mean (runW scheme adversary fuel pk sk (next d) w'
        { trace with hashRequests := input :: trace.hashRequests }) Φ)]
      conv_rhs => rw [mean_hash_step (pruneW K world) input (fun d w' =>
        mean (runW scheme adversary fuel pk sk (next d) w'
          { trace with hashRequests := input :: trace.hashRequests }) fun r => Φ r + T r)]
      refine mean_le_mean _ _ _ fun r _ => ?_
      exact ih pk sk (next r.1) { world with hashTable := r.2 } _ hcons
    | query input next =>
      dsimp only
      simp only [mean_bind]
      rw [postLaw_mean (hpubLaw input) world]
      conv_rhs => rw [postLaw_mean (hpubLaw input) (pruneW K world)]
      set Ψ : Answer × GW HashInput Digest lambda s wit rnd → ℝ≥0∞ := fun r =>
        min 1 (mean (resampleW resample r.2) fun w' =>
          mean (runW scheme adversary fuel pk sk (next r.1) w'
            { trace with publicRequests := input :: trace.publicRequests }) fun r' => Φ r' + T r') with hΨ
      have hΨfree : FamilyFreeG Ψ := by
        intro a w f
        simp only [hΨ, resampleW_setFamily]
      have hΨle : ∀ r, Ψ r ≤ 1 := fun r => min_le_left _ _
      calc _ ≤ mean (resampleW resample world) (fun w => mean (scheme.publicOracle input w) fun r =>
            Ψ (r.1, pruneW K r.2)) := by
            refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
            simp only [hΨ]
            refine le_min (mean_le_const _ _ 1 fun w' _ => mean_le_const _ _ 1 fun r' _ => hc.le_one _) ?_
            exact ih pk sk (next r.1) r.2 _ (hpubK input w r (consistent_of_mem_resampleW world w hw hposs) hr)
        _ ≤ mean (resampleW resample (pruneW K world)) (fun w => mean (scheme.publicOracle input w) fun r =>
            if touchesG K r.2 then 1 else Ψ r) := hpubP input world hposs Ψ hΨfree hΨle
        _ ≤ _ := by
            refine mean_le_mean _ _ _ fun w _ => mean_le_mean _ _ _ fun r _ => ?_
            by_cases ht : touchesG K r.2 = true
            · rw [if_pos ht]
              exact htouched fuel pk sk (next r.1) r.2 _ ht
            · rw [if_neg ht]
              exact min_le_right _ _

include hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK hprepK hc in
/-- The reverse agreement: the run from the resampled pruned world is below
the run from the resampled world plus the touching functional under the
pruned run. -/
theorem prune_le_runW_gen (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State)
    (world : GW HashInput Digest lambda s wit rnd) (trace : Trace Message HashInput Query) (hcons : Consistent world) :
    mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) Φ) ≤
      mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) Φ) +
      mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) T) := by
  have h := runW_le_prune_gen K scheme adversary hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK
    hprepK (fun r => 1 - Φ r) T (pruneCompat_compl K Φ T hc) fuel pk sk state world trace hcons
  have ha : mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) Φ) ≤ 1 :=
    mean_le_const _ _ 1 fun w _ => mean_le_const _ _ 1 fun r _ => hc.le_one _
  have hb : mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) Φ) ≤ 1 :=
    mean_le_const _ _ 1 fun w _ => mean_le_const _ _ 1 fun r _ => hc.le_one _
  have hL : mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r => 1 - Φ r) =
      1 - mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) Φ) := by
    rw [← mean_one_sub _ _ (fun w => mean_le_const _ _ 1 fun r _ => hc.le_one _)]
    refine congrArg _ (funext fun w => ?_)
    exact mean_one_sub _ _ fun r => hc.le_one _
  have hR : mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
      (fun r => 1 - Φ r) r + T r) =
      (1 - mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) Φ)) +
        mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) T) := by
    rw [← mean_one_sub _ _ (fun w => mean_le_const _ _ 1 fun r _ => hc.le_one _), ← mean_add]
    refine congrArg _ (funext fun w => ?_)
    rw [mean_add, mean_one_sub _ _ fun r => hc.le_one _]
  rw [hL, hR] at h
  exact (one_sub_le_iff _ _ _ ha hb).mp h

include hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK hprepK hc in
/-- The game run with a compatible evaluation of its result is a compatible
evaluation, with the run's mean of the touching functional, for a state
and a trace read from the terminal without its embedded world. -/
theorem runW_pruneCompat (fuel : Nat) (pk : PublicKey) (sk : SecretKey)
    (st : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query → State)
    (hst : ∀ t w, st (withWorld t w) = st t)
    (tr : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query →
      Trace Message HashInput Query)
    (htr : ∀ t w, tr (withWorld t w) = tr t) :
    PruneCompat K (fun r => mean (runW scheme adversary fuel pk sk (st r.1) r.2 (tr r.1)) Φ)
      (fun r => mean (runW scheme adversary fuel pk sk (st r.1) r.2 (tr r.1)) T) where
  le_one r := mean_le_const _ _ 1 fun r' _ => hc.le_one _
  touch_le r := by
    by_cases ht : touchesG K r.2 = true
    · rw [ht]
      calc indicator true = mean (runW scheme adversary fuel pk sk (st r.1) r.2 (tr r.1)) (fun _ => 1) := by
            rw [mean_const]; rfl
        _ ≤ _ := mean_le_mean _ _ _ fun r' hr' => by
            have ht' := touchesG_runW K scheme adversary hsignG hpubG hprepG fuel pk sk (st r.1) r.2 (tr r.1) ht r' hr'
            calc (1 : ℝ≥0∞) = indicator (touchesG K r'.2) := by rw [ht']; rfl
              _ ≤ T r' := hc.touch_le r'
    · rw [Bool.not_eq_true] at ht
      rw [ht]
      exact zero_le _
  forward t world hw := by
    simp only [hst, htr, ← mean_add]
    exact runW_le_prune_gen K scheme adversary hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK
      hprepK Φ T hc fuel pk sk (st t) world (tr t) hw
  reverse t world hw := by
    simp only [hst, htr]
    exact prune_le_runW_gen K scheme adversary hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK
      hprepK Φ T hc fuel pk sk (st t) world (tr t) hw

end
end SDitH.Proofs.GamePruneGen
