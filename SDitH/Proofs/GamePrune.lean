import SDitH.Proofs.SharedPrune
import SDitH.Proofs.RunWorld

/-! The game run agrees with its run from the pruned world until a query
hits the pruned keys. The game world pruned at a list of keys prunes its
shared world; an oracle's prune law says its call from the resampled world
and from the resampled pruned world agree up to the touching of its result;
an oracle grows when its result's cipher history extends its input's, so
touching persists along the run. Under the oracles' resampling laws, prune
laws and growth, the mean of a family-free function of the pruned terminal
and world under the run from the resampled world is at most its mean plus
the final touching indicator under the run from the resampled pruned
world. -/

namespace SDitH.Proofs.GamePrune

open Spec.SignatureSecurity
open Spec.IdealCipher (Family)
open Spec.RandomOracleTrap (indicator)
open Spec.DomainSeparation (Bits)
open GameResample ChargeExpect ChargeCutExpect CipherResample SharedPrune HiddenEntries RunWorld
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}

/-- The game world over the shared world. -/
abbrev GW (HashInput Digest : Type*) (lambda s wit rnd : Nat) :=
  World HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)

/-- The game world with its family replaced. -/
def setFamily (w : GW HashInput Digest lambda s wit rnd) (f : Family (Bits lambda) (Bits lambda)) :
    GW HashInput Digest lambda s wit rnd :=
  { w with other := { w.other with family := f } }

/-- The game world pruned at a list of keys. -/
def pruneW (K : List (Bits lambda)) (w : GW HashInput Digest lambda s wit rnd) : GW HashInput Digest lambda s wit rnd :=
  { w with other := pruneShared K w.other }

/-- The game world's cipher history has an entry at the keys. -/
def touchesG (K : List (Bits lambda)) (w : GW HashInput Digest lambda s wit rnd) : Bool :=
  touchesW K w.other

/-- The game world's cipher history is possible. -/
def Possible (w : GW HashInput Digest lambda s wit rnd) : Prop :=
  ∃ f : Family (Bits lambda) (Bits lambda), Spec.IdealCipher.Matches f w.other.cipherHistory

/-- The game world's family matches its cipher history. -/
def Consistent (w : GW HashInput Digest lambda s wit rnd) : Prop :=
  Spec.IdealCipher.Matches w.other.family w.other.cipherHistory

omit [Fintype Digest] [Nonempty Digest] in
theorem possible_of_consistent (w : GW HashInput Digest lambda s wit rnd) (h : Consistent w) : Possible w :=
  ⟨w.other.family, h⟩

/-- A function of an oracle result that does not read the family. -/
def FamilyFreeG {A : Type*} (Ψ : A × GW HashInput Digest lambda s wit rnd → ℝ≥0∞) : Prop :=
  ∀ (a : A) (w : GW HashInput Digest lambda s wit rnd) (f : Family (Bits lambda) (Bits lambda)),
    Ψ (a, setFamily w f) = Ψ (a, w)

/-- A function of a terminal with its world that does not read the family,
with an attempt's embedded world replaced alike. -/
def FamilyFreeT
    (Φ : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞) : Prop :=
  ∀ (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (w : GW HashInput Digest lambda s wit rnd) (f : Family (Bits lambda) (Bits lambda)),
    Φ (withWorld t (setFamily w f), setFamily w f) = Φ (withWorld t w, w)

/-- An oracle's prune law: its call from the resampled world and from the
resampled pruned world agree, for family-free functions bounded by one, up
to the touching of its result. -/
def PruneLaw {A : Type*} (K : List (Bits lambda))
    (O : GW HashInput Digest lambda s wit rnd → PMF (A × GW HashInput Digest lambda s wit rnd)) : Prop :=
  ∀ (world : GW HashInput Digest lambda s wit rnd), Possible world →
    ∀ (Ψ : A × GW HashInput Digest lambda s wit rnd → ℝ≥0∞), FamilyFreeG Ψ → (∀ r, Ψ r ≤ 1) →
    mean (resampleW resample world) (fun w => mean (O w) fun r => Ψ (r.1, pruneW K r.2)) ≤
      mean (resampleW resample (pruneW K world)) (fun w => mean (O w) fun r => if touchesG K r.2 then 1 else Ψ r)

/-- An oracle grows: its result's cipher history extends its input's. -/
def Grows {A : Type*}
    (O : GW HashInput Digest lambda s wit rnd → PMF (A × GW HashInput Digest lambda s wit rnd)) : Prop :=
  ∀ (w : GW HashInput Digest lambda s wit rnd) (r : A × GW HashInput Digest lambda s wit rnd), r ∈ (O w).support →
    ∃ new, r.2.other.cipherHistory = new ++ w.other.cipherHistory

/-- An oracle keeps consistency: its result from a consistent world is
consistent. -/
def Keeps {A : Type*}
    (O : GW HashInput Digest lambda s wit rnd → PMF (A × GW HashInput Digest lambda s wit rnd)) : Prop :=
  ∀ (w : GW HashInput Digest lambda s wit rnd) (r : A × GW HashInput Digest lambda s wit rnd), Consistent w →
    r ∈ (O w).support → Consistent r.2

omit [Fintype Digest] [Nonempty Digest] in
/-- A resampled world of a possible world is consistent. -/
theorem consistent_of_mem_resampleW (w w' : GW HashInput Digest lambda s wit rnd)
    (hw' : w' ∈ (resampleW resample w).support) (hw : Possible w) : Consistent w' := by
  simp only [resampleW, resample, PMF.map_comp, PMF.support_map] at hw'
  obtain ⟨f, hf, rfl⟩ := hw'
  exact PrunedRun.matches_of_mem_posterior _ hw f hf

omit [Fintype Digest] [Nonempty Digest] in
theorem resampleW_setFamily (w : GW HashInput Digest lambda s wit rnd) (f : Family (Bits lambda) (Bits lambda)) :
    resampleW resample (setFamily w f) = resampleW resample w := by
  simp only [resampleW, resample, setFamily]

omit [Fintype Digest] [Nonempty Digest] in
/-- The mean over the resampled world of a family-free function is its value. -/
theorem mean_resampleW_const (F : GW HashInput Digest lambda s wit rnd → ℝ≥0∞)
    (hF : ∀ w f, F (setFamily w f) = F w) (w : GW HashInput Digest lambda s wit rnd) :
    mean (resampleW resample w) F = F w := by
  simp only [resampleW, resample, PMF.map_comp, mean_map, Function.comp_def]
  change mean _ (fun f => F (setFamily w f)) = _
  simp only [hF, mean_const]

omit [Fintype Digest] [Nonempty Digest] in
theorem touchesG_of_append (K : List (Bits lambda)) (w r : GW HashInput Digest lambda s wit rnd) (new : _)
    (h : r.other.cipherHistory = new ++ w.other.cipherHistory) (hw : touchesG K w = true) : touchesG K r = true := by
  simp only [touchesG, touchesW, decide_eq_true_eq] at hw ⊢
  obtain ⟨e, he, hk⟩ := hw
  exact ⟨e, by rw [h]; exact List.mem_append_right _ he, hk⟩

omit [Fintype Digest] [Nonempty Digest] in
theorem touchesG_of_mem_resampleW (K : List (Bits lambda)) (w w' : GW HashInput Digest lambda s wit rnd)
    (hw' : w' ∈ (resampleW resample w).support) (hw : touchesG K w = true) : touchesG K w' = true := by
  simp only [resampleW, resample, PMF.map_comp, PMF.support_map] at hw'
  obtain ⟨f, -, rfl⟩ := hw'
  exact hw

/-- Touching persists along the run of growing oracles. -/
theorem touchesG_runW (K : List (Bits lambda))
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsignG : ∀ sk m, Grows (scheme.sign sk m)) (hpubG : ∀ q, Grows (scheme.publicOracle q))
    (hprepG : ∀ pk m sig, Grows (scheme.prepareVerification pk m sig)) :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (w : GW HashInput Digest lambda s wit rnd)
      (trace : Trace Message HashInput Query), touchesG K w = true →
      ∀ r ∈ (runW scheme adversary fuel pk sk state w trace).support, touchesG K r.2 = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state w trace hw r hr
    simp only [runW, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact hw
  | succ fuel ih =>
    intro pk sk state w trace hw r hr
    simp only [runW, PMF.mem_support_bind_iff] at hr
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
      exact ih pk sk _ _ _ (touchesG_of_append K w result.2 new hnew hw) r hr
    | hash input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, -, hr⟩ := hr
      exact ih pk sk _ { w with hashTable := result.2 } _ hw r hr
    | query input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres, hr⟩ := hr
      obtain ⟨new, hnew⟩ := hpubG input w result hres
      exact ih pk sk _ _ _ (touchesG_of_append K w result.2 new hnew hw) r hr

omit [Fintype Digest] [Nonempty Digest] in
/-- A terminal's embedded world is replaced regardless of its former one. -/
theorem withWorld_withWorld (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (w w' : GW HashInput Digest lambda s wit rnd) : withWorld (withWorld t w) w' = withWorld t w' := by
  cases t <;> rfl

/-- The hash step from a resampled world. -/
theorem mean_hash_step (X : GW HashInput Digest lambda s wit rnd) (input : HashInput)
    (G : Digest → GW HashInput Digest lambda s wit rnd → ℝ≥0∞) :
    mean (resampleW resample X) (fun w => mean (Spec.RandomOracle.query w.hashTable input) fun r =>
      G r.1 { w with hashTable := r.2 }) =
    mean (Spec.RandomOracle.query X.hashTable input) fun r =>
      mean (resampleW resample { X with hashTable := r.2 }) fun w' => G r.1 w' := by
  calc _ = mean (resampleW resample X) (fun w => mean (Spec.RandomOracle.query X.hashTable input) fun r =>
        G r.1 { w with hashTable := r.2 }) := by
        unfold mean
        refine tsum_congr fun w => ?_
        by_cases hw : w ∈ (resampleW resample X).support
        · simp only [hashTable_of_mem resample X w hw]
        · rw [PMF.mem_support_iff, not_not] at hw
          simp [hw]
    _ = mean (Spec.RandomOracle.query X.hashTable input) fun r =>
        mean (resampleW resample X) fun w => G r.1 { w with hashTable := r.2 } := mean_comm _ _ _
    _ = _ := by
        refine congrArg _ (funext fun r => ?_)
        exact (mean_resampleW_update resample X r.2 (fun w' => G r.1 w')).symm

/-- The game run from the resampled world is below the run from the resampled
pruned world plus the final touching indicator. -/
theorem runW_le_prune (K : List (Bits lambda))
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
    (hΦ : FamilyFreeT Φ) (hle : ∀ r, Φ r ≤ 1) :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : GW HashInput Digest lambda s wit rnd)
      (trace : Trace Message HashInput Query), Consistent world →
      mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
        Φ (withWorld r.1 (pruneW K r.2), pruneW K r.2)) ≤
      mean (resampleW resample (pruneW K world)) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
        Φ r + indicator (touchesG K r.2)) := by
  -- the constant cases
  have hconst : ∀ (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
      (world : GW HashInput Digest lambda s wit rnd),
      mean (resampleW resample world) (fun w => Φ (withWorld t (pruneW K w), pruneW K w)) ≤
        mean (resampleW resample (pruneW K world)) (fun w => Φ (withWorld t w, w) + indicator (touchesG K w)) := by
    intro t world
    rw [mean_resampleW_const (fun w => Φ (withWorld t (pruneW K w), pruneW K w)) (fun w f => hΦ t (pruneW K w) f),
      mean_resampleW_const (fun w => Φ (withWorld t w, w) + indicator (touchesG K w))
        (fun w f => congrArg (· + indicator (touchesG K w)) (hΦ t w f))]
    exact le_self_add
  -- the touched continuation is at least one
  have htouched : ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State)
      (o : GW HashInput Digest lambda s wit rnd) (trace : Trace Message HashInput Query), touchesG K o = true →
      1 ≤ mean (resampleW resample o) (fun w' => mean (runW scheme adversary fuel pk sk state w' trace) fun r =>
        Φ r + indicator (touchesG K r.2)) := by
    intro fuel pk sk state o trace ho
    calc (1 : ℝ≥0∞) = mean (resampleW resample o) (fun w' =>
          mean (runW scheme adversary fuel pk sk state w' trace) fun _ => 1) := by simp only [mean_const]
      _ ≤ _ := mean_le_mean _ _ _ fun w' hw' => mean_le_mean _ _ _ fun r hr => by
          rw [touchesG_runW K scheme adversary hsignG hpubG hprepG fuel pk sk state w' trace
            (touchesG_of_mem_resampleW K o w' hw' ho) r hr]
          exact le_add_self
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state world trace _
    simp only [runW, mean_pure]
    exact hconst (.exhausted trace) world
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
      exact hconst (.aborted trace) world
    | finish message signature =>
      dsimp only
      simp only [mean_map]
      set Ψ : Option HashInput × GW HashInput Digest lambda s wit rnd → ℝ≥0∞ := fun r =>
        Φ (withWorld (match r.1 with
          | none => Terminal.rejected trace
          | some input => Terminal.attempt ⟨message, signature, input, scheme.signatureDigest signature, r.2, trace⟩)
          r.2, r.2) with hΨ
      have hΨfree : FamilyFreeG Ψ := by
        intro a w f
        simp only [hΨ]
        cases a <;> exact hΦ _ w f
      have hΨle : ∀ r, Ψ r ≤ 1 := fun r => hle _
      refine le_of_eq_of_le ?_ ((hprepP pk message signature world hposs Ψ hΨfree hΨle).trans
        (mean_le_mean _ _ _ fun w _ => mean_le_mean _ _ _ fun r _ => ?_))
      · refine congrArg _ (funext fun w => congrArg _ (funext fun r => ?_))
        rcases r with ⟨a, o⟩
        cases a with
        | none => simp only [hΨ]
        | some input =>
          simp only [hΨ]
          rfl
      · rcases r with ⟨a, o⟩
        by_cases ht : touchesG K o = true
        · rw [if_pos ht, ht, RandomOracleTrap.indicator_true]
          exact le_add_self
        · rw [if_neg ht]
          cases a <;> simp only [hΨ] <;> exact le_self_add
    | sign message next =>
      dsimp only
      simp only [mean_bind]
      rw [postLaw_mean (hsignLaw sk message) world]
      conv_rhs => rw [postLaw_mean (hsignLaw sk message) (pruneW K world)]
      set Ψ : Signature × GW HashInput Digest lambda s wit rnd → ℝ≥0∞ := fun r =>
        min 1 (mean (resampleW resample r.2) fun w' =>
          mean (runW scheme adversary fuel pk sk (next r.1) w'
            { trace with signingRequests := message :: trace.signingRequests }) fun r' =>
              Φ r' + indicator (touchesG K r'.2)) with hΨ
      have hΨfree : FamilyFreeG Ψ := by
        intro a w f
        simp only [hΨ, resampleW_setFamily]
      have hΨle : ∀ r, Ψ r ≤ 1 := fun r => min_le_left _ _
      calc _ ≤ mean (resampleW resample world) (fun w => mean (scheme.sign sk message w) fun r =>
            Ψ (r.1, pruneW K r.2)) := by
            refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
            simp only [hΨ]
            refine le_min (mean_le_const _ _ 1 fun w' _ => mean_le_const _ _ 1 fun r' _ => hle _) ?_
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
        { trace with hashRequests := input :: trace.hashRequests }) fun r =>
          Φ (withWorld r.1 (pruneW K r.2), pruneW K r.2))]
      conv_rhs => rw [mean_hash_step (pruneW K world) input (fun d w' =>
        mean (runW scheme adversary fuel pk sk (next d) w'
          { trace with hashRequests := input :: trace.hashRequests }) fun r => Φ r + indicator (touchesG K r.2))]
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
            { trace with publicRequests := input :: trace.publicRequests }) fun r' =>
              Φ r' + indicator (touchesG K r'.2)) with hΨ
      have hΨfree : FamilyFreeG Ψ := by
        intro a w f
        simp only [hΨ, resampleW_setFamily]
      have hΨle : ∀ r, Ψ r ≤ 1 := fun r => min_le_left _ _
      calc _ ≤ mean (resampleW resample world) (fun w => mean (scheme.publicOracle input w) fun r =>
            Ψ (r.1, pruneW K r.2)) := by
            refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
            simp only [hΨ]
            refine le_min (mean_le_const _ _ 1 fun w' _ => mean_le_const _ _ 1 fun r' _ => hle _) ?_
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

end
end SDitH.Proofs.GamePrune
