import SDitH.Proofs.MeanHybridCont
import SDitH.Proofs.RunWorld

/-! The mean-form hybrid over signing calls of the run with its final
world, with the per-call bound stated for its continuations: the second
scheme's run with its final world from the signing output, then the final
evaluation of the terminal with the world. The restored fork's first branch
needs this form, since its second branch starts from the first's final
world. -/

namespace SDitH.Proofs.MeanHybridContW

open Spec.SignatureSecurity Spec.SignatureReplay
open RunHybrid GameResample ChargeExpect ChargeCutExpect RowStoredPosterior MeanHybrid MeanHybridCont RunWorld
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State C : Type*}
variable [Fintype Digest] [Nonempty Digest]

variable (res : Other → PMF Other)
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

/-- The per-call bound in mean form for the continuations of the run with
its final world. -/
def SignRunWMean : Prop :=
  ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other), Inv B world →
    ∀ (fuel : Nat) (pk : PublicKey) (next : Signature → State) (trace : Trace Message HashInput Query)
      (h : Terminal Message Signature HashInput Digest Other Query × World HashInput Digest Other → PMF C) (c : C),
    mean (resampleW res world) (fun w => ((sch₁.sign sk message w).bind fun r =>
        (runW sch₂ adversary fuel pk sk (next r.1) r.2 trace).bind h) c) ≤
      mean (resampleW res world) (fun w => ((sch₂.sign sk message w).bind fun r =>
        (runW sch₂ adversary fuel pk sk (next r.1) r.2 trace).bind h) c) + ε

include hagree hmono hres hquery hpres hpub hsignLaw hpubLaw in
/-- The hybrid in mean form of the run with its final world. -/
theorem runW_le_runW_mean_cont (hsign : SignRunWMean (C := C) res sch₁ sch₂ adversary Good ε B Inv)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (hsk : Good sk) (state : State) (world : World HashInput Digest Other)
    (trace : Trace Message HashInput Query) (m : Nat) (hm : Inv m world) (hB : m + fuel ≤ B)
    (h : Terminal Message Signature HashInput Digest Other Query × World HashInput Digest Other → PMF C) (c : C) :
    mean (resampleW res world) (fun w => ((runW sch₁ adversary fuel pk sk state w trace).bind h) c) ≤
      mean (resampleW res world) (fun w => ((runW sch₂ adversary fuel pk sk state w trace).bind h) c) + fuel * ε := by
  induction fuel generalizing state world trace m with
  | zero =>
    simp only [runW, Nat.cast_zero, zero_mul, add_zero]
    exact le_rfl
  | succ fuel ih =>
    have hstep : (fuel : ℝ≥0∞) * ε ≤ ((fuel + 1 : Nat) : ℝ≥0∞) * ε :=
      mul_le_mul' (Nat.cast_le.mpr (Nat.le_succ fuel)) le_rfl
    simp only [runW, PMF.bind_bind, mean_bind_apply (adversary.step pk state)]
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
              (runW sch₁ adversary fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c)
          = mean (resampleW res world) (fun w => mean (sch₁.sign sk message w) fun r =>
              mean (resampleW res r.2) fun w' => ((runW sch₁ adversary fuel pk sk (next r.1) w'
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) := by
            simp only [mean_bind_apply]
            exact postLaw_mean (hsignLaw sk message) world _
        _ ≤ mean (resampleW res world) (fun w => mean (sch₁.sign sk message w) fun r =>
              mean (resampleW res r.2) (fun w' => ((runW sch₂ adversary fuel pk sk (next r.1) w'
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + fuel * ε) :=
            mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr =>
              ih (next r.1) r.2 _ (m + 1) (hpres sk message w m r (hres m world hm w hw) hr) (by omega)
        _ = mean (resampleW res world) (fun w => ((sch₁.sign sk message w).bind fun r =>
              (runW sch₂ adversary fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + fuel * ε := by
            simp only [mean_add_const, mean_bind_apply]
            congr 1
            exact (postLaw_mean (hsignLaw sk message) world (fun r => mean (runW sch₂ adversary fuel pk sk (next r.1) r.2
              { trace with signingRequests := message :: trace.signingRequests }) fun a => (h a) c)).symm
        _ ≤ (mean (resampleW res world) (fun w => ((sch₂.sign sk message w).bind fun r =>
              (runW sch₂ adversary fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + ε) + fuel * ε :=
            add_le_add (hsign sk hsk message world (hmono m B world (by omega) hm) fuel pk next _ h c) le_rfl
        _ = _ := by push_cast; ring
    | hash input next =>
      dsimp only
      simp only [PMF.bind_bind]
      have hform : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer),
          mean (resampleW res world) (fun w => ((Spec.RandomOracle.query w.hashTable input).bind fun r =>
            (runW sch adversary fuel pk sk (next r.1) { w with hashTable := r.2 }
              { trace with hashRequests := input :: trace.hashRequests }).bind h) c) =
          mean (Spec.RandomOracle.query world.hashTable input) fun r =>
            mean (resampleW res { world with hashTable := r.2 }) fun w' =>
              ((runW sch adversary fuel pk sk (next r.1) w'
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c := by
        intro sch
        calc _ = mean (resampleW res world) (fun w => ((Spec.RandomOracle.query world.hashTable input).bind fun r =>
              (runW sch adversary fuel pk sk (next r.1) { w with hashTable := r.2 }
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c) := by
              unfold mean
              refine tsum_congr fun w => ?_
              by_cases hw : w ∈ (resampleW res world).support
              · simp only [hashTable_of_mem res world w hw]
              · rw [PMF.mem_support_iff, not_not] at hw
                simp [hw]
          _ = mean (Spec.RandomOracle.query world.hashTable input) fun r =>
              mean (resampleW res world) fun w => ((runW sch adversary fuel pk sk (next r.1) { w with hashTable := r.2 }
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c := by
              simp only [mean_bind_apply]
              exact mean_comm _ _ _
          _ = _ := by
              refine congrArg _ (funext fun r => ?_)
              exact (mean_resampleW_update res world r.2 (fun w' => ((runW sch adversary fuel pk sk (next r.1) w'
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c)).symm
      rw [hform sch₁, hform sch₂]
      refine (mean_le_mean _ _ _ fun r hr =>
        ih (next r.1) _ _ (m + 1) (hquery world input m r hm hr) (by omega)).trans ?_
      rw [mean_add_const]
      exact add_le_add le_rfl hstep
    | query input next =>
      dsimp only
      simp only [PMF.bind_bind, hagree.publicOracle]
      calc mean (resampleW res world) (fun w => ((sch₂.publicOracle input w).bind fun r =>
              (runW sch₁ adversary fuel pk sk (next r.1) r.2
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c)
          = mean (resampleW res world) (fun w => mean (sch₂.publicOracle input w) fun r =>
              mean (resampleW res r.2) fun w' => ((runW sch₁ adversary fuel pk sk (next r.1) w'
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) := by
            simp only [mean_bind_apply]
            exact postLaw_mean (hpubLaw input) world _
        _ ≤ mean (resampleW res world) (fun w => mean (sch₂.publicOracle input w) fun r =>
              mean (resampleW res r.2) (fun w' => ((runW sch₂ adversary fuel pk sk (next r.1) w'
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) + fuel * ε) :=
            mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr =>
              ih (next r.1) r.2 _ (m + 1) (hpub input w m r (hres m world hm w hw) hr) (by omega)
        _ = mean (resampleW res world) (fun w => ((sch₂.publicOracle input w).bind fun r =>
              (runW sch₂ adversary fuel pk sk (next r.1) r.2
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) + fuel * ε := by
            simp only [mean_add_const, mean_bind_apply]
            congr 1
            exact (postLaw_mean (hpubLaw input) world (fun r => mean (runW sch₂ adversary fuel pk sk (next r.1) r.2
              { trace with publicRequests := input :: trace.publicRequests }) fun a => (h a) c)).symm
        _ ≤ _ := add_le_add le_rfl hstep


end
end SDitH.Proofs.MeanHybridContW
