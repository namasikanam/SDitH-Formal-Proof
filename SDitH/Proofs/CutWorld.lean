import SDitH.Proofs.GamePruneGen

/-! The cut with its final world, and the pruned-run agreement for it. The
replay's cut forgets the final world on its ended outcomes without an
attempt, so a touching functional of its results cannot remember the
touching; the cut with its final world pairs every outcome with the world
at the cut, projects to the cut, and the agreement of continuation 278
holds for it with prune-compatible evaluations of a cut with its world. -/

namespace SDitH.Proofs.CutWorld

open Spec.SignatureSecurity Spec.SignatureReplay
open Spec.IdealCipher (Family)
open Spec.RandomOracleTrap (indicator)
open Spec.DomainSeparation (Bits)
open GameResample ChargeExpect ChargeCutExpect CipherResample SharedPrune HiddenEntries RunWorld GamePrune GamePruneReverse
open GamePruneGen
open scoped Classical ENNReal

noncomputable section

section Generic

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- The cut with its final world. -/
def cutW (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    Nat → Nat → PublicKey → SecretKey → State → World HashInput Digest Other → Trace Message HashInput Query →
      PMF (Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State × World HashInput Digest Other)
  | _, 0, _, _, _, world, trace => PMF.pure (.ended (.exhausted trace), world)
  | index, fuel + 1, pk, sk, state, world, trace => (adversary.step pk state).bind fun action =>
      match action with
      | .abort => PMF.pure (.ended (.aborted trace), world)
      | .finish message signature =>
          (scheme.prepareVerification pk message signature world).map fun result =>
            (.ended (match result.1 with
              | none => .rejected trace
              | some input => .attempt ⟨message, signature, input, scheme.signatureDigest signature, result.2, trace⟩),
              result.2)
      | .sign message next => (scheme.sign sk message world).bind fun result =>
          cutW scheme adversary index fuel pk sk (next result.1) result.2
            { trace with signingRequests := message :: trace.signingRequests }
      | .hash input next =>
          match index with
          | 0 => PMF.pure (.saved ⟨fuel, pk, sk, input, next, world, trace⟩, world)
          | index + 1 => (Spec.RandomOracle.query world.hashTable input).bind fun result =>
              cutW scheme adversary index fuel pk sk (next result.1)
                { world with hashTable := result.2 }
                { trace with hashRequests := input :: trace.hashRequests }
      | .query input next => (scheme.publicOracle input world).bind fun result =>
          cutW scheme adversary index fuel pk sk (next result.1) result.2
            { trace with publicRequests := input :: trace.publicRequests }

/-- The cut with its final world projects to the cut. -/
theorem cutW_fst (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    ∀ (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : World HashInput Digest Other)
      (trace : Trace Message HashInput Query),
      (cutW scheme adversary index fuel pk sk state world trace).map Prod.fst =
        cut scheme adversary index fuel pk sk state world trace := by
  intro index fuel
  induction fuel generalizing index with
  | zero =>
    intro pk sk state world trace
    simp only [cutW, cut, PMF.pure_map]
  | succ fuel ih =>
    intro pk sk state world trace
    simp only [cutW, cut, PMF.map_bind]
    refine congrArg _ (funext fun action => ?_)
    cases action with
    | abort => simp only [PMF.pure_map]
    | finish message signature =>
      dsimp only
      rw [PMF.map_comp]
      rfl
    | sign message next =>
      dsimp only
      rw [PMF.map_bind]
      exact congrArg _ (funext fun r => ih index pk sk (next r.1) r.2 _)
    | hash input next =>
      dsimp only
      cases index with
      | zero => simp only [PMF.pure_map]
      | succ index =>
        dsimp only
        rw [PMF.map_bind]
        exact congrArg _ (funext fun r => ih index pk sk (next r.1) _ _)
    | query input next =>
      dsimp only
      rw [PMF.map_bind]
      exact congrArg _ (funext fun r => ih index pk sk (next r.1) r.2 _)

/-- A cut with its world replaced: the ended terminal's embedded world, or
the saved snapshot's world. -/
def withWorldC (c : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State)
    (w : World HashInput Digest Other) : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State :=
  match c with
  | .ended t => .ended (withWorld t w)
  | .saved sn => .saved { sn with world := w }

end Generic

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}

/-- Touching persists along the cut of growing oracles. -/
theorem touchesG_cutW (K : List (Bits lambda))
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsignG : ∀ sk m, Grows (scheme.sign sk m)) (hpubG : ∀ q, Grows (scheme.publicOracle q))
    (hprepG : ∀ pk m sig, Grows (scheme.prepareVerification pk m sig)) :
    ∀ (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (w : GW HashInput Digest lambda s wit rnd)
      (trace : Trace Message HashInput Query), touchesG K w = true →
      ∀ r ∈ (cutW scheme adversary index fuel pk sk state w trace).support, touchesG K r.2 = true := by
  intro index fuel
  induction fuel generalizing index with
  | zero =>
    intro pk sk state w trace hw r hr
    simp only [cutW, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact hw
  | succ fuel ih =>
    intro pk sk state w trace hw r hr
    simp only [cutW, PMF.mem_support_bind_iff] at hr
    obtain ⟨action, -, hr⟩ := hr
    cases action with
    | abort =>
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact hw
    | finish message signature =>
      simp only [PMF.support_map, Set.mem_image] at hr
      obtain ⟨result, hres, rfl⟩ := hr
      obtain ⟨new, hnew⟩ := hprepG pk message signature w result hres
      exact touchesG_of_append K w result.2 new hnew hw
    | sign message next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres, hr⟩ := hr
      obtain ⟨new, hnew⟩ := hsignG sk message w result hres
      exact ih index pk sk _ _ _ (touchesG_of_append K w result.2 new hnew hw) r hr
    | hash input next =>
      cases index with
      | zero =>
        simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
        subst hr
        exact hw
      | succ index =>
        simp only [PMF.mem_support_bind_iff] at hr
        obtain ⟨result, -, hr⟩ := hr
        exact ih index pk sk _ { w with hashTable := result.2 } _ hw r hr
    | query input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres, hr⟩ := hr
      obtain ⟨new, hnew⟩ := hpubG input w result hres
      exact ih index pk sk _ _ _ (touchesG_of_append K w result.2 new hnew hw) r hr

/-- An evaluation of a cut with its world compatible with pruning at the
keys, with its touching functional. -/
structure PruneCompatC (K : List (Bits lambda))
    (Φ T : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞) : Prop where
  le_one : ∀ r, Φ r ≤ 1
  touch_le : ∀ r, indicator (touchesG K r.2) ≤ T r
  forward : ∀ (c : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query
      State) (world : GW HashInput Digest lambda s wit rnd), Consistent world →
    mean (resampleW resample world) (fun w => Φ (withWorldC c w, w)) ≤
      mean (resampleW resample (pruneW K world)) (fun w => Φ (withWorldC c w, w) + T (withWorldC c w, w))
  reverse : ∀ (c : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query
      State) (world : GW HashInput Digest lambda s wit rnd), Consistent world →
    mean (resampleW resample (pruneW K world)) (fun w => Φ (withWorldC c w, w)) ≤
      mean (resampleW resample world) (fun w => Φ (withWorldC c w, w)) +
        mean (resampleW resample (pruneW K world)) (fun w => T (withWorldC c w, w))

omit [Fintype Digest] [Nonempty Digest] in
/-- The complement of a compatible evaluation is compatible with the same
touching functional. -/
theorem pruneCompatC_compl (K : List (Bits lambda))
    (Φ T : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞) (hc : PruneCompatC K Φ T) :
    PruneCompatC K (fun r => 1 - Φ r) T where
  le_one _ := tsub_le_self
  touch_le := hc.touch_le
  forward c world hw := by
    have ha : mean (resampleW resample world) (fun w => Φ (withWorldC c w, w)) ≤ 1 :=
      mean_le_const _ _ 1 fun w _ => hc.le_one _
    have hb : mean (resampleW resample (pruneW K world)) (fun w => Φ (withWorldC c w, w)) ≤ 1 :=
      mean_le_const _ _ 1 fun w _ => hc.le_one _
    rw [mean_one_sub _ _ (fun w => hc.le_one _), mean_add, mean_one_sub _ _ (fun w => hc.le_one _)]
    exact (one_sub_le_iff _ _ _ ha hb).mpr (hc.reverse c world hw)
  reverse c world hw := by
    have ha : mean (resampleW resample world) (fun w => Φ (withWorldC c w, w)) ≤ 1 :=
      mean_le_const _ _ 1 fun w _ => hc.le_one _
    have hb : mean (resampleW resample (pruneW K world)) (fun w => Φ (withWorldC c w, w)) ≤ 1 :=
      mean_le_const _ _ 1 fun w _ => hc.le_one _
    rw [mean_one_sub _ _ (fun w => hc.le_one _), mean_one_sub _ _ (fun w => hc.le_one _)]
    exact (one_sub_le_iff _ _ _ hb ha).mpr (by rw [← mean_add]; exact hc.forward c world hw)

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
  (Φ T : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State ×
    GW HashInput Digest lambda s wit rnd → ℝ≥0∞)
  (hc : PruneCompatC K Φ T)

include hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK hprepK hc in
theorem cutW_le_prune_gen :
    ∀ (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : GW HashInput Digest lambda s wit rnd)
      (trace : Trace Message HashInput Query), Consistent world →
      mean (resampleW resample world) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) Φ) ≤
      mean (resampleW resample (pruneW K world)) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) fun r =>
        Φ r + T r) := by
  -- the touched continuation is at least one
  have htouched : ∀ (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State)
      (o : GW HashInput Digest lambda s wit rnd) (trace : Trace Message HashInput Query), touchesG K o = true →
      1 ≤ mean (resampleW resample o) (fun w' => mean (cutW scheme adversary index fuel pk sk state w' trace) fun r =>
        Φ r + T r) := by
    intro index fuel pk sk state o trace ho
    calc (1 : ℝ≥0∞) = mean (resampleW resample o) (fun w' =>
          mean (cutW scheme adversary index fuel pk sk state w' trace) fun _ => 1) := by simp only [mean_const]
      _ ≤ _ := mean_le_mean _ _ _ fun w' hw' => mean_le_mean _ _ _ fun r hr => by
          have ht := touchesG_cutW K scheme adversary hsignG hpubG hprepG index fuel pk sk state w' trace
            (touchesG_of_mem_resampleW K o w' hw' ho) r hr
          calc (1 : ℝ≥0∞) = indicator (touchesG K r.2) := by rw [ht]; rfl
            _ ≤ T r := hc.touch_le r
            _ ≤ _ := le_add_self
  intro index fuel
  induction fuel generalizing index with
  | zero =>
    intro pk sk state world trace hcons
    simp only [cutW, mean_pure]
    exact hc.forward (.ended (.exhausted trace)) world hcons
  | succ fuel ih =>
    intro pk sk state world trace hcons
    have hposs : Possible world := possible_of_consistent world hcons
    simp only [cutW, mean_bind]
    rw [mean_comm]
    conv_rhs => rw [mean_comm]
    refine mean_le_mean _ _ _ fun action _ => ?_
    cases action with
    | abort =>
      dsimp only
      simp only [mean_pure]
      exact hc.forward (.ended (.aborted trace)) world hcons
    | finish message signature =>
      dsimp only
      simp only [mean_map]
      -- the terminal of a preparation result, read with a world
      set T₀ : Option HashInput → GW HashInput Digest lambda s wit rnd →
          Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query := fun a w =>
        match a with
        | none => Terminal.rejected trace
        | some input => Terminal.attempt ⟨message, signature, input, scheme.signatureDigest signature, w, trace⟩ with hT₀
      have hT₀w : ∀ a w w', (withWorldC (Cut.ended (T₀ a w)) w' :
          Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State) =
          Cut.ended (T₀ a w') := by
        intro a w w'
        cases a <;> rfl
      set Ψ : Option HashInput × GW HashInput Digest lambda s wit rnd → ℝ≥0∞ := fun r =>
        min 1 (mean (resampleW resample r.2) fun w' => Φ (.ended (T₀ r.1 w'), w') + T (.ended (T₀ r.1 w'), w')) with hΨ
      have hΨfree : FamilyFreeG Ψ := by
        intro a w f
        simp only [hΨ, resampleW_setFamily]
      have hΨle : ∀ r, Ψ r ≤ 1 := fun r => min_le_left _ _
      calc _ = mean (resampleW resample world) (fun w => mean (scheme.prepareVerification pk message signature w) fun r =>
            Φ (.ended (T₀ r.1 r.2), r.2)) := by
            refine congrArg _ (funext fun w => congrArg _ (funext fun r => ?_))
            rcases r with ⟨a, o⟩
            cases a <;> rfl
        _ = mean (resampleW resample world) (fun w => mean (scheme.prepareVerification pk message signature w) fun r =>
            mean (resampleW resample r.2) fun w' => Φ (.ended (T₀ r.1 w'), w')) :=
            postLaw_mean (hprepLaw pk message signature) world (fun r => Φ (.ended (T₀ r.1 r.2), r.2))
        _ ≤ mean (resampleW resample world) (fun w => mean (scheme.prepareVerification pk message signature w) fun r =>
            Ψ (r.1, pruneW K r.2)) := by
            refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
            simp only [hΨ]
            refine le_min (mean_le_const _ _ 1 fun w' _ => hc.le_one _) ?_
            have hcr : Consistent r.2 :=
              hprepK pk message signature w r (consistent_of_mem_resampleW world w hw hposs) hr
            have h := hc.forward (.ended (T₀ r.1 r.2)) r.2 hcr
            simp only [hT₀w] at h
            exact h
        _ ≤ mean (resampleW resample (pruneW K world)) (fun w =>
            mean (scheme.prepareVerification pk message signature w) fun r => if touchesG K r.2 then 1 else Ψ r) :=
            hprepP pk message signature world hposs Ψ hΨfree hΨle
        _ ≤ mean (resampleW resample (pruneW K world)) (fun w =>
            mean (scheme.prepareVerification pk message signature w) fun r =>
              mean (resampleW resample r.2) fun w' => Φ (.ended (T₀ r.1 w'), w') + T (.ended (T₀ r.1 w'), w')) := by
            refine mean_le_mean _ _ _ fun w _ => mean_le_mean _ _ _ fun r _ => ?_
            by_cases ht : touchesG K r.2 = true
            · rw [if_pos ht]
              calc (1 : ℝ≥0∞) = mean (resampleW resample r.2) (fun _ => 1) := (mean_const _ _).symm
                _ ≤ _ := mean_le_mean _ _ _ fun w' hw' => by
                    have ht' := touchesG_of_mem_resampleW K r.2 w' hw' ht
                    calc (1 : ℝ≥0∞) = indicator (touchesG K w') := by rw [ht']; rfl
                      _ ≤ T (.ended (T₀ r.1 w'), w') := hc.touch_le _
                      _ ≤ _ := le_add_self
            · rw [if_neg ht]
              exact min_le_right _ _
        _ = mean (resampleW resample (pruneW K world)) (fun w =>
            mean (scheme.prepareVerification pk message signature w) fun r => Φ (.ended (T₀ r.1 r.2), r.2) + T (.ended (T₀ r.1 r.2), r.2)) :=
            (postLaw_mean (hprepLaw pk message signature) (pruneW K world)
              (fun r => Φ (.ended (T₀ r.1 r.2), r.2) + T (.ended (T₀ r.1 r.2), r.2))).symm
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
          mean (cutW scheme adversary index fuel pk sk (next r.1) w'
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
            exact ih index pk sk (next r.1) r.2 _ (hsignK sk message w r (consistent_of_mem_resampleW world w hw hposs) hr)
        _ ≤ mean (resampleW resample (pruneW K world)) (fun w => mean (scheme.sign sk message w) fun r =>
            if touchesG K r.2 then 1 else Ψ r) := hsignP sk message world hposs Ψ hΨfree hΨle
        _ ≤ _ := by
            refine mean_le_mean _ _ _ fun w _ => mean_le_mean _ _ _ fun r _ => ?_
            by_cases ht : touchesG K r.2 = true
            · rw [if_pos ht]
              exact htouched index fuel pk sk (next r.1) r.2 _ ht
            · rw [if_neg ht]
              exact min_le_right _ _
    | hash input next =>
      dsimp only
      cases index with
      | zero =>
        dsimp only
        simp only [mean_pure]
        exact hc.forward (.saved ⟨fuel, pk, sk, input, next, world, trace⟩) world hcons
      | succ index =>
        dsimp only
        simp only [mean_bind]
        rw [mean_hash_step world input (fun d w' => mean (cutW scheme adversary index fuel pk sk (next d) w'
          { trace with hashRequests := input :: trace.hashRequests }) Φ)]
        conv_rhs => rw [mean_hash_step (pruneW K world) input (fun d w' =>
          mean (cutW scheme adversary index fuel pk sk (next d) w'
            { trace with hashRequests := input :: trace.hashRequests }) fun r => Φ r + T r)]
        refine mean_le_mean _ _ _ fun r _ => ?_
        exact ih index pk sk (next r.1) { world with hashTable := r.2 } _ hcons
    | query input next =>
      dsimp only
      simp only [mean_bind]
      rw [postLaw_mean (hpubLaw input) world]
      conv_rhs => rw [postLaw_mean (hpubLaw input) (pruneW K world)]
      set Ψ : Answer × GW HashInput Digest lambda s wit rnd → ℝ≥0∞ := fun r =>
        min 1 (mean (resampleW resample r.2) fun w' =>
          mean (cutW scheme adversary index fuel pk sk (next r.1) w'
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
            exact ih index pk sk (next r.1) r.2 _ (hpubK input w r (consistent_of_mem_resampleW world w hw hposs) hr)
        _ ≤ mean (resampleW resample (pruneW K world)) (fun w => mean (scheme.publicOracle input w) fun r =>
            if touchesG K r.2 then 1 else Ψ r) := hpubP input world hposs Ψ hΨfree hΨle
        _ ≤ _ := by
            refine mean_le_mean _ _ _ fun w _ => mean_le_mean _ _ _ fun r _ => ?_
            by_cases ht : touchesG K r.2 = true
            · rw [if_pos ht]
              exact htouched index fuel pk sk (next r.1) r.2 _ ht
            · rw [if_neg ht]
              exact min_le_right _ _

include hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK hprepK hc in
/-- The reverse agreement: the cut from the resampled pruned world is below
the run from the resampled world plus the touching functional under the
pruned run. -/
theorem prune_le_cutW_gen (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State)
    (world : GW HashInput Digest lambda s wit rnd) (trace : Trace Message HashInput Query) (hcons : Consistent world) :
    mean (resampleW resample (pruneW K world)) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) Φ) ≤
      mean (resampleW resample world) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) Φ) +
      mean (resampleW resample (pruneW K world)) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) T) := by
  have h := cutW_le_prune_gen K scheme adversary hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK
    hprepK (fun r => 1 - Φ r) T (pruneCompatC_compl K Φ T hc) index fuel pk sk state world trace hcons
  have ha : mean (resampleW resample world) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) Φ) ≤ 1 :=
    mean_le_const _ _ 1 fun w _ => mean_le_const _ _ 1 fun r _ => hc.le_one _
  have hb : mean (resampleW resample (pruneW K world)) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) Φ) ≤ 1 :=
    mean_le_const _ _ 1 fun w _ => mean_le_const _ _ 1 fun r _ => hc.le_one _
  have hL : mean (resampleW resample world) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) fun r => 1 - Φ r) =
      1 - mean (resampleW resample world) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) Φ) := by
    rw [← mean_one_sub _ _ (fun w => mean_le_const _ _ 1 fun r _ => hc.le_one _)]
    refine congrArg _ (funext fun w => ?_)
    exact mean_one_sub _ _ fun r => hc.le_one _
  have hR : mean (resampleW resample (pruneW K world)) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) fun r =>
      (fun r => 1 - Φ r) r + T r) =
      (1 - mean (resampleW resample (pruneW K world)) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) Φ)) +
        mean (resampleW resample (pruneW K world)) (fun w => mean (cutW scheme adversary index fuel pk sk state w trace) T) := by
    rw [← mean_one_sub _ _ (fun w => mean_le_const _ _ 1 fun r _ => hc.le_one _), ← mean_add]
    refine congrArg _ (funext fun w => ?_)
    rw [mean_add, mean_one_sub _ _ fun r => hc.le_one _]
  rw [hL, hR] at h
  exact (one_sub_le_iff _ _ _ ha hb).mp h

end
end SDitH.Proofs.CutWorld
