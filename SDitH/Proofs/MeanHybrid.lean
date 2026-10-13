import SDitH.Proofs.ChargeCutExpect
import SDitH.Proofs.RowStoredPosterior

/-! The run hybrid in mean form. The per-call signing bound is stated for
a fixed continuation with the world resampled before the call: the mean
over the resampled world of the first scheme's signing bound to the
continuation is within a constant of the mean of the second scheme's. Along
a run the resampling is moved past each call by the oracles' resampling
laws and past each hash query by the hash-table update, so the means of
the two schemes' runs from a resampled world are within the fuel times the
constant. This is the form in which the witness-swap term is bounded. -/

namespace SDitH.Proofs.MeanHybrid

open Spec.SignatureSecurity
open RunHybrid GameResample ChargeExpect ChargeCutExpect RowStoredPosterior
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State C : Type*}
variable [Fintype Digest] [Nonempty Digest]

omit [Fintype Digest] [Nonempty Digest] in
theorem mean_bind_apply {A B : Type*} (p : PMF A) (f : A → PMF B) (b : B) :
    (p.bind f) b = mean p fun a => (f a) b :=
  (mean_eq_bind p f b).symm

omit [Fintype Digest] [Nonempty Digest] in
/-- A mean of a sum with a constant. -/
theorem mean_add_const {A : Type*} (p : PMF A) (φ : A → ℝ≥0∞) (K : ℝ≥0∞) :
    mean p (fun a => φ a + K) = mean p φ + K := by
  rw [mean_add, mean_const]

/-- The run hybrid in mean form. -/
theorem run_le_run_mean (res : Other → PMF Other)
    (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (ε : ℝ≥0∞) (B : Nat)
    (Inv : Nat → World HashInput Digest Other → Prop)
    (hmono : ∀ (n m : Nat) (world : World HashInput Digest Other), n ≤ m → Inv n world → Inv m world)
    (hres : ∀ (n : Nat) (world : World HashInput Digest Other), Inv n world →
      ∀ w ∈ (resampleW res world).support, Inv n w)
    (hquery : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat)
      (r : Digest × (HashInput → Option Digest)), Inv n world →
      r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
    (hpres : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
      (r : Signature × World HashInput Digest Other), Inv n world →
      r ∈ (sch₁.sign sk message world).support → Inv (n + 1) r.2)
    (hpub : ∀ (query : Query) (world : World HashInput Digest Other) (n : Nat) (r : Answer × World HashInput Digest Other),
      Inv n world → r ∈ (sch₂.publicOracle query world).support → Inv (n + 1) r.2)
    (hsignLaw : ∀ (sk : SecretKey) (message : Message), PostLaw res (sch₁.sign sk message))
    (hpubLaw : ∀ query : Query, PostLaw res (sch₂.publicOracle query))
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
      Inv B world → ∀ (h : Signature × World HashInput Digest Other → PMF C) (c : C),
      mean (resampleW res world) (fun w => ((sch₁.sign sk message w).bind h) c) ≤
        mean (resampleW res world) (fun w => ((sch₂.sign sk message w).bind h) c) + ε)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (hsk : Good sk) (state : State) (world : World HashInput Digest Other)
    (trace : Trace Message HashInput Query) (m : Nat) (hm : Inv m world) (hB : m + fuel ≤ B)
    (h : Terminal Message Signature HashInput Digest Other Query → PMF C) (c : C) :
    mean (resampleW res world) (fun w => ((run sch₁ adversary fuel pk sk state w trace).bind h) c) ≤
      mean (resampleW res world) (fun w => ((run sch₂ adversary fuel pk sk state w trace).bind h) c) + fuel * ε := by
  induction fuel generalizing state world trace m with
  | zero =>
    simp only [run, Nat.cast_zero, zero_mul, add_zero]
    exact le_rfl
  | succ fuel ih =>
    have hstep : (fuel : ℝ≥0∞) * ε ≤ ((fuel + 1 : Nat) : ℝ≥0∞) * ε :=
      mul_le_mul' (Nat.cast_le.mpr (Nat.le_succ fuel)) le_rfl
    simp only [run, PMF.bind_bind, mean_bind_apply (adversary.step pk state)]
    rw [mean_comm]
    conv_rhs => rw [mean_comm, ← mean_add_const]
    refine mean_le_mean _ _ _ fun action _ => ?_
    cases action with
    | abort =>
      dsimp only
      exact le_self_add
    | finish message signature =>
      dsimp only
      rw [hagree.prepareVerification, hagree.signatureDigest]
      exact le_self_add
    | sign message next =>
      dsimp only
      simp only [PMF.bind_bind]
      calc mean (resampleW res world) (fun w => ((sch₁.sign sk message w).bind fun r =>
              (run sch₁ adversary fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c)
          = mean (resampleW res world) (fun w => mean (sch₁.sign sk message w) fun r =>
              mean (resampleW res r.2) fun w' => ((run sch₁ adversary fuel pk sk (next r.1) w'
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) := by
            simp only [mean_bind_apply]
            exact postLaw_mean (hsignLaw sk message) world _
        _ ≤ mean (resampleW res world) (fun w => mean (sch₁.sign sk message w) fun r =>
              mean (resampleW res r.2) (fun w' => ((run sch₂ adversary fuel pk sk (next r.1) w'
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + fuel * ε) :=
            mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr =>
              ih (next r.1) r.2 _ (m + 1) (hpres sk message w m r (hres m world hm w hw) hr) (by omega)
        _ = mean (resampleW res world) (fun w => ((sch₁.sign sk message w).bind fun r =>
              (run sch₂ adversary fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + fuel * ε := by
            simp only [mean_add_const, mean_bind_apply]
            congr 1
            exact (postLaw_mean (hsignLaw sk message) world (fun r => mean (run sch₂ adversary fuel pk sk (next r.1) r.2
              { trace with signingRequests := message :: trace.signingRequests }) fun a => (h a) c)).symm
        _ ≤ (mean (resampleW res world) (fun w => ((sch₂.sign sk message w).bind fun r =>
              (run sch₂ adversary fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + ε) + fuel * ε :=
            add_le_add_left (hsign sk hsk message world (hmono m B world (by omega) hm) _ c) _
        _ = _ := by push_cast; ring
    | hash input next =>
      dsimp only
      simp only [PMF.bind_bind]
      have hform : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer),
          mean (resampleW res world) (fun w => ((Spec.RandomOracle.query w.hashTable input).bind fun r =>
            (run sch adversary fuel pk sk (next r.1) { w with hashTable := r.2 }
              { trace with hashRequests := input :: trace.hashRequests }).bind h) c) =
          mean (Spec.RandomOracle.query world.hashTable input) fun r =>
            mean (resampleW res { world with hashTable := r.2 }) fun w' =>
              ((run sch adversary fuel pk sk (next r.1) w'
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c := by
        intro sch
        calc _ = mean (resampleW res world) (fun w => ((Spec.RandomOracle.query world.hashTable input).bind fun r =>
              (run sch adversary fuel pk sk (next r.1) { w with hashTable := r.2 }
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c) := by
              unfold mean
              refine tsum_congr fun w => ?_
              by_cases hw : w ∈ (resampleW res world).support
              · simp only [hashTable_of_mem res world w hw]
              · rw [PMF.mem_support_iff, not_not] at hw
                simp [hw]
          _ = mean (Spec.RandomOracle.query world.hashTable input) fun r =>
              mean (resampleW res world) fun w => ((run sch adversary fuel pk sk (next r.1) { w with hashTable := r.2 }
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c := by
              simp only [mean_bind_apply]
              exact mean_comm _ _ _
          _ = _ := by
              refine congrArg _ (funext fun r => ?_)
              exact (mean_resampleW_update res world r.2 (fun w' => ((run sch adversary fuel pk sk (next r.1) w'
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c)).symm
      rw [hform sch₁, hform sch₂]
      refine (mean_le_mean _ _ _ fun r hr =>
        ih (next r.1) _ _ (m + 1) (hquery world input m r hm hr) (by omega)).trans ?_
      rw [mean_add_const]
      exact add_le_add_right hstep _
    | query input next =>
      dsimp only
      simp only [PMF.bind_bind, hagree.publicOracle]
      calc mean (resampleW res world) (fun w => ((sch₂.publicOracle input w).bind fun r =>
              (run sch₁ adversary fuel pk sk (next r.1) r.2
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c)
          = mean (resampleW res world) (fun w => mean (sch₂.publicOracle input w) fun r =>
              mean (resampleW res r.2) fun w' => ((run sch₁ adversary fuel pk sk (next r.1) w'
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) := by
            simp only [mean_bind_apply]
            exact postLaw_mean (hpubLaw input) world _
        _ ≤ mean (resampleW res world) (fun w => mean (sch₂.publicOracle input w) fun r =>
              mean (resampleW res r.2) (fun w' => ((run sch₂ adversary fuel pk sk (next r.1) w'
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) + fuel * ε) :=
            mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr =>
              ih (next r.1) r.2 _ (m + 1) (hpub input w m r (hres m world hm w hw) hr) (by omega)
        _ = mean (resampleW res world) (fun w => ((sch₂.publicOracle input w).bind fun r =>
              (run sch₂ adversary fuel pk sk (next r.1) r.2
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) + fuel * ε := by
            simp only [mean_add_const, mean_bind_apply]
            congr 1
            exact (postLaw_mean (hpubLaw input) world (fun r => mean (run sch₂ adversary fuel pk sk (next r.1) r.2
              { trace with publicRequests := input :: trace.publicRequests }) fun a => (h a) c)).symm
        _ ≤ _ := add_le_add_right hstep _

end
end SDitH.Proofs.MeanHybrid
