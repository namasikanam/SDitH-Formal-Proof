import SDitH.Proofs.ChargeRun
import SDitH.Proofs.GameResample

/-! The expected charge from a resampled world. An oracle's resampling law
is the joint-law form: the oracle's output from a resampled world has the
law of the output with its world resampled afresh. Under the laws for the
signing and public oracles, the mean over the resampled world of the
cumulative charge is at most the fuel times the per-call average bound,
the bound on the mean of the charge over a resampled world at every
invariant world within the budget. -/

namespace SDitH.Proofs.ChargeExpect

open Spec.SignatureSecurity
open GameResample ChargeRun
open scoped Classical ENNReal

noncomputable section

section Mean

variable {A B : Type*}

/-- The mean of a function under a distribution. -/
def mean (p : PMF A) (φ : A → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * φ a

theorem mean_bind (p : PMF A) (f : A → PMF B) (φ : B → ℝ≥0∞) :
    mean (p.bind f) φ = mean p fun a => mean (f a) φ := by
  unfold mean
  simp only [PMF.bind_apply]
  calc ∑' b, (∑' a, p a * f a b) * φ b = ∑' b, ∑' a, p a * f a b * φ b := by
        congr 1
        funext b
        rw [ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' b, p a * f a b * φ b := ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, f a b * φ b := by
        congr 1
        funext a
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext b
        rw [mul_assoc]

theorem mean_pure (b : A) (φ : A → ℝ≥0∞) : mean (PMF.pure b) φ = φ b := by
  unfold mean
  rw [tsum_eq_single b (fun a ha => by simp [PMF.pure_apply, ha])]
  simp [PMF.pure_apply]

theorem mean_map (p : PMF A) (g : A → B) (φ : B → ℝ≥0∞) : mean (p.map g) φ = mean p fun a => φ (g a) := by
  show mean (p.bind (PMF.pure ∘ g)) φ = _
  rw [mean_bind]
  congr 1
  funext a
  exact mean_pure _ _

theorem mean_const (p : PMF A) (c : ℝ≥0∞) : mean p (fun _ => c) = c := by
  unfold mean
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem mean_add (p : PMF A) (φ ψ : A → ℝ≥0∞) : mean p (fun a => φ a + ψ a) = mean p φ + mean p ψ := by
  unfold mean
  simp_rw [mul_add]
  exact ENNReal.tsum_add

theorem mean_le_mean (p : PMF A) (φ ψ : A → ℝ≥0∞) (h : ∀ a ∈ p.support, φ a ≤ ψ a) : mean p φ ≤ mean p ψ := by
  unfold mean
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · exact mul_le_mul' le_rfl (h a ha)
  · rw [PMF.mem_support_iff, not_not] at ha
    rw [ha]
    simp

theorem mean_le_const (p : PMF A) (φ : A → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ a ∈ p.support, φ a ≤ c) : mean p φ ≤ c :=
  (mean_le_mean p φ (fun _ => c) h).trans (le_of_eq (mean_const p c))

theorem mean_comm (p : PMF A) (q : PMF B) (F : A → B → ℝ≥0∞) :
    mean p (fun a => mean q (fun b => F a b)) = mean q (fun b => mean p (fun a => F a b)) := by
  unfold mean
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  congr 1
  funext b
  congr 1
  funext a
  ring

end Mean

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- An oracle's resampling law: the output from a resampled world has the
law of the output with its world resampled afresh. -/
def PostLaw {A : Type*} (res : Other → PMF Other)
    (O : World HashInput Digest Other → PMF (A × World HashInput Digest Other)) : Prop :=
  ∀ world, (resampleW res world).bind O =
    (resampleW res world).bind fun w => (O w).bind fun r => (resampleW res r.2).map fun w' => (r.1, w')

omit [Fintype Digest] [Nonempty Digest] in
/-- The law under any continuation. -/
theorem postLaw_bind {A R : Type*} {res : Other → PMF Other}
    {O : World HashInput Digest Other → PMF (A × World HashInput Digest Other)} (h : PostLaw res O)
    (world : World HashInput Digest Other) (K : A × World HashInput Digest Other → PMF R) :
    (resampleW res world).bind (fun w => (O w).bind K) =
      (resampleW res world).bind (fun w => (O w).bind fun r => (resampleW res r.2).bind fun w' => K (r.1, w')) := by
  rw [← PMF.bind_bind, h world, PMF.bind_bind]
  congr 1
  funext w
  rw [PMF.bind_bind]
  congr 1
  funext r
  rw [PMF.bind_map]
  rfl

omit [Fintype Digest] [Nonempty Digest] in
/-- The law in mean form. -/
theorem postLaw_mean {A : Type*} {res : Other → PMF Other}
    {O : World HashInput Digest Other → PMF (A × World HashInput Digest Other)} (h : PostLaw res O)
    (world : World HashInput Digest Other) (φ : A × World HashInput Digest Other → ℝ≥0∞) :
    mean (resampleW res world) (fun w => mean (O w) φ) =
      mean (resampleW res world) (fun w => mean (O w) fun r => mean (resampleW res r.2) fun w' => φ (r.1, w')) := by
  have := congrArg (fun p => mean p φ) (h world)
  simp only [mean_bind, mean_map] at this
  exact this

omit [Fintype Digest] [Nonempty Digest] in
theorem hashTable_of_mem (res : Other → PMF Other) (world w : World HashInput Digest Other)
    (hw : w ∈ (resampleW res world).support) : w.hashTable = world.hashTable := by
  unfold resampleW at hw
  rw [PMF.support_map] at hw
  obtain ⟨o, -, rfl⟩ := hw
  rfl

omit [Fintype Digest] [Nonempty Digest] in
theorem resampleW_update (res : Other → PMF Other) (world : World HashInput Digest Other)
    (table : HashInput → Option Digest) :
    resampleW res { world with hashTable := table } = (resampleW res world).map fun w => { w with hashTable := table } := by
  unfold resampleW
  rw [PMF.map_comp]
  rfl

/-- The charge's recursion in mean form. -/
theorem charge_succ (eps : World HashInput Digest Other → ℝ≥0∞)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) (fuel : Nat)
    (pk : PublicKey) (sk : SecretKey) (state : State) (world : World HashInput Digest Other)
    (trace : Trace Message HashInput Query) :
    charge eps sch adversary (fuel + 1) pk sk state world trace = mean (adversary.step pk state) fun action =>
      match action with
      | .abort => 0
      | .finish _ _ => 0
      | .sign message next => eps world + mean (sch.sign sk message world) fun r =>
          charge eps sch adversary fuel pk sk (next r.1) r.2
            { trace with signingRequests := message :: trace.signingRequests }
      | .hash input next => mean (Spec.RandomOracle.query world.hashTable input) fun r =>
          charge eps sch adversary fuel pk sk (next r.1) { world with hashTable := r.2 }
            { trace with hashRequests := input :: trace.hashRequests }
      | .query input next => mean (sch.publicOracle input world) fun r =>
          charge eps sch adversary fuel pk sk (next r.1) r.2
            { trace with publicRequests := input :: trace.publicRequests } := rfl

/-- The expected charge from a resampled world is at most the fuel times
the per-call average bound. -/
theorem charge_mean_le (res : Other → PMF Other)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsignLaw : ∀ (sk : SecretKey) (message : Message), PostLaw res (sch.sign sk message))
    (hpubLaw : ∀ query : Query, PostLaw res (sch.publicOracle query))
    (eps : World HashInput Digest Other → ℝ≥0∞) (ε : ℝ≥0∞) (B : Nat) (Inv : Nat → World HashInput Digest Other → Prop)
    (hmono : ∀ (n m : Nat) (world : World HashInput Digest Other), n ≤ m → Inv n world → Inv m world)
    (hres : ∀ (n : Nat) (world : World HashInput Digest Other), Inv n world →
      ∀ w ∈ (resampleW res world).support, Inv n w)
    (hquery : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat)
      (r : Digest × (HashInput → Option Digest)), Inv n world →
      r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
    (hpres : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
      (r : Signature × World HashInput Digest Other), Inv n world →
      r ∈ (sch.sign sk message world).support → Inv (n + 1) r.2)
    (hpub : ∀ (query : Query) (world : World HashInput Digest Other) (n : Nat) (r : Answer × World HashInput Digest Other),
      Inv n world → r ∈ (sch.publicOracle query world).support → Inv (n + 1) r.2)
    (heps : ∀ world : World HashInput Digest Other, Inv B world → mean (resampleW res world) eps ≤ ε)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : World HashInput Digest Other)
    (trace : Trace Message HashInput Query) (m : Nat) (hm : Inv m world) (hB : m + fuel ≤ B) :
    mean (resampleW res world) (fun w => charge eps sch adversary fuel pk sk state w trace) ≤ fuel * ε := by
  induction fuel generalizing state world trace m with
  | zero =>
    simp only [charge, mean_const, Nat.cast_zero, zero_mul]
    exact le_rfl
  | succ fuel ih =>
    have hstep : (fuel : ℝ≥0∞) * ε ≤ ((fuel + 1 : Nat) : ℝ≥0∞) * ε :=
      mul_le_mul' (Nat.cast_le.mpr (Nat.le_succ fuel)) le_rfl
    simp only [charge_succ]
    rw [mean_comm]
    refine mean_le_const _ _ _ (fun action _ => ?_)
    cases action with
    | abort =>
      dsimp only
      rw [mean_const]
      exact zero_le _
    | finish message signature =>
      dsimp only
      rw [mean_const]
      exact zero_le _
    | sign message next =>
      dsimp only
      rw [mean_add, postLaw_mean (hsignLaw sk message)]
      calc _ ≤ ε + mean (resampleW res world) (fun w => mean (sch.sign sk message w) fun _ => (fuel : ℝ≥0∞) * ε) :=
            add_le_add (heps world (hmono m B world (by omega) hm))
              (mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr =>
                ih (next r.1) r.2 _ (m + 1) (hpres sk message w m r (hres m world hm w hw) hr) (by omega))
        _ = ((fuel + 1 : Nat) : ℝ≥0∞) * ε := by
            simp only [mean_const]
            push_cast
            ring
    | hash input next =>
      dsimp only
      calc _ ≤ mean (resampleW res world) (fun w => mean (Spec.RandomOracle.query world.hashTable input) fun r =>
            charge eps sch adversary fuel pk sk (next r.1) { w with hashTable := r.2 }
              { trace with hashRequests := input :: trace.hashRequests }) :=
            mean_le_mean _ _ _ fun w hw => le_of_eq (by rw [hashTable_of_mem res world w hw])
        _ = mean (Spec.RandomOracle.query world.hashTable input) fun r =>
            mean (resampleW res { world with hashTable := r.2 }) fun w =>
              charge eps sch adversary fuel pk sk (next r.1) w
                { trace with hashRequests := input :: trace.hashRequests } := by
            rw [mean_comm]
            congr 1
            funext r
            rw [resampleW_update res world r.2, mean_map]
        _ ≤ (fuel : ℝ≥0∞) * ε :=
            mean_le_const _ _ _ fun r hr =>
              ih (next r.1) _ _ (m + 1) (hquery world input m r hm hr) (by omega)
        _ ≤ _ := hstep
    | query input next =>
      dsimp only
      rw [postLaw_mean (hpubLaw input)]
      calc _ ≤ mean (resampleW res world) (fun w => mean (sch.publicOracle input w) fun _ => (fuel : ℝ≥0∞) * ε) :=
            mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr =>
              ih (next r.1) r.2 _ (m + 1) (hpub input w m r (hres m world hm w hw) hr) (by omega)
        _ = (fuel : ℝ≥0∞) * ε := by simp only [mean_const]
        _ ≤ _ := hstep

end
end SDitH.Proofs.ChargeExpect
