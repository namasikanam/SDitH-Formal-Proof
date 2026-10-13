import SDitH.Proofs.ChargeCut

/-! The expected replay charges from a resampled key. The cut run obeys
the resampling law with the saved snapshot's world resampled; so from
key generation yielding a resampled world, the cut experiment's charge
is at most the fuel times the per-call average bound, the fork charge at
most twice that, and the event-experiment hybrid holds with these
constants in place of the per-world bound. -/

namespace SDitH.Proofs.ChargeCutExpect

open Spec.SignatureSecurity Spec.SignatureReplay
open GameResample ChargeRun ChargeExpect ChargeCut CutHybridGen EventHybrid
open scoped Classical ENNReal

noncomputable section

section Mean

variable {A : Type*}

theorem mean_mul_left (p : PMF A) (c : ℝ≥0∞) (φ : A → ℝ≥0∞) : mean p (fun a => c * φ a) = c * mean p φ := by
  unfold mean
  simp_rw [mul_left_comm _ c]
  exact ENNReal.tsum_mul_left

end Mean

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

omit [Fintype Digest] [Nonempty Digest] in
theorem mean_resampleW_update (res : Other → PMF Other) (world : World HashInput Digest Other)
    (table : HashInput → Option Digest) (φ : World HashInput Digest Other → ℝ≥0∞) :
    mean (resampleW res { world with hashTable := table }) φ =
      mean (resampleW res world) fun w => φ { w with hashTable := table } := by
  rw [resampleW_update res world table, mean_map]

/-- Resampling a cut result's world at a saved snapshot. -/
def resampleCut (res : Other → PMF Other) :
    Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State →
      PMF (Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State)
  | .ended terminal => PMF.pure (.ended terminal)
  | .saved snapshot => (resampleW res snapshot.world).map fun w => .saved { snapshot with world := w }

/-- The cut's resampling law: the cut from a resampled world has the law
of the cut with its saved world resampled afresh. -/
theorem cut_postLaw (res : Other → PMF Other) (hidem : ∀ other, (res other).bind res = res other)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsignLaw : ∀ (sk : SecretKey) (message : Message), PostLaw res (sch.sign sk message))
    (hpubLaw : ∀ query : Query, PostLaw res (sch.publicOracle query))
    (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : World HashInput Digest Other)
    (trace : Trace Message HashInput Query) :
    (resampleW res world).bind (fun w => cut sch adversary index fuel pk sk state w trace) =
      (resampleW res world).bind (fun w =>
        (cut sch adversary index fuel pk sk state w trace).bind (resampleCut res)) := by
  induction fuel generalizing index state world trace with
  | zero => simp only [cut, resampleCut, PMF.pure_bind]
  | succ fuel ih =>
    simp only [cut, PMF.bind_bind]
    rw [PMF.bind_comm]
    conv_rhs => rw [PMF.bind_comm]
    congr 1
    funext action
    cases action with
    | abort => simp only [resampleCut, PMF.pure_bind]
    | finish message signature =>
      dsimp only
      simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind, resampleCut]
    | sign message next =>
      dsimp only
      simp only [PMF.bind_bind]
      conv_lhs => rw [postLaw_bind (hsignLaw sk message)]
      conv_rhs => rw [postLaw_bind (hsignLaw sk message)]
      congr 1
      funext w
      congr 1
      funext r
      exact ih index (next r.1) r.2 _
    | hash input next =>
      dsimp only
      cases index with
      | zero =>
        dsimp only
        simp only [resampleCut, PMF.pure_bind, PMF.map, Function.comp_def]
        rw [resampleW_bind res hidem]
      | succ index =>
        dsimp only
        simp only [PMF.bind_bind, resampleW, PMF.bind_map, Function.comp_def]
        rw [PMF.bind_comm]
        conv_rhs => rw [PMF.bind_comm]
        congr 1
        funext result
        have h := ih index (next result.1) { world with hashTable := result.2 }
          { trace with hashRequests := input :: trace.hashRequests }
        simp only [resampleW, PMF.bind_map, Function.comp_def] at h
        exact h
    | query input next =>
      dsimp only
      simp only [PMF.bind_bind]
      conv_lhs => rw [postLaw_bind (hpubLaw input)]
      conv_rhs => rw [postLaw_bind (hpubLaw input)]
      congr 1
      funext w
      congr 1
      funext r
      exact ih index (next r.1) r.2 _

/-- The expected cut charge from a resampled world. -/
theorem chargeCut_mean_le (res : Other → PMF Other)
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
    (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : World HashInput Digest Other)
    (trace : Trace Message HashInput Query) (m : Nat) (hm : Inv m world) (hB : m + fuel ≤ B) :
    mean (resampleW res world) (fun w => chargeCut eps sch adversary index fuel pk sk state w trace) ≤ fuel * ε := by
  induction fuel generalizing index state world trace m with
  | zero =>
    simp only [chargeCut, mean_const, Nat.cast_zero, zero_mul]
    exact le_rfl
  | succ fuel ih =>
    have hstep : (fuel : ℝ≥0∞) * ε ≤ ((fuel + 1 : Nat) : ℝ≥0∞) * ε :=
      mul_le_mul' (Nat.cast_le.mpr (Nat.le_succ fuel)) le_rfl
    simp only [chargeCut]
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
                ih index (next r.1) r.2 _ (m + 1) (hpres sk message w m r (hres m world hm w hw) hr) (by omega))
        _ = ((fuel + 1 : Nat) : ℝ≥0∞) * ε := by
            simp only [mean_const]
            push_cast
            ring
    | hash input next =>
      cases index with
      | zero =>
        dsimp only
        rw [mean_const]
        exact zero_le _
      | succ index =>
        dsimp only
        calc _ ≤ mean (resampleW res world) (fun w => mean (Spec.RandomOracle.query world.hashTable input) fun r =>
              chargeCut eps sch adversary index fuel pk sk (next r.1) { w with hashTable := r.2 }
                { trace with hashRequests := input :: trace.hashRequests }) :=
              mean_le_mean _ _ _ fun w hw => le_of_eq (by rw [hashTable_of_mem res world w hw])
          _ = mean (Spec.RandomOracle.query world.hashTable input) fun r =>
              mean (resampleW res { world with hashTable := r.2 }) fun w =>
                chargeCut eps sch adversary index fuel pk sk (next r.1) w
                  { trace with hashRequests := input :: trace.hashRequests } := by
              rw [mean_comm]
              congr 1
              funext r
              rw [resampleW_update res world r.2, mean_map]
          _ ≤ (fuel : ℝ≥0∞) * ε :=
              mean_le_const _ _ _ fun r hr =>
                ih index (next r.1) _ _ (m + 1) (hquery world input m r hm hr) (by omega)
          _ ≤ _ := hstep
    | query input next =>
      dsimp only
      rw [postLaw_mean (hpubLaw input)]
      calc _ ≤ mean (resampleW res world) (fun w => mean (sch.publicOracle input w) fun _ => (fuel : ℝ≥0∞) * ε) :=
            mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr =>
              ih index (next r.1) r.2 _ (m + 1) (hpub input w m r (hres m world hm w hw) hr) (by omega)
        _ = (fuel : ℝ≥0∞) * ε := by simp only [mean_const]
        _ ≤ _ := hstep

/-- The cut experiment's charge from a resampled key. -/
theorem chargeExperiment_le (res : Other → PMF Other)
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
    (hkeygen : sch.keygen = sch.keygen.bind fun g => (resampleW res g.2.2).map fun w => (g.1, g.2.1, w))
    (hinit : ∀ generated ∈ sch.keygen.support, Inv 0 generated.2.2) (index fuel : Nat) (hB : fuel ≤ B) :
    chargeExperiment eps sch adversary index fuel ≤ fuel * ε := by
  unfold chargeExperiment
  rw [hkeygen, mean_bind]
  refine mean_le_const _ _ _ (fun g hg => ?_)
  rw [mean_map]
  dsimp only
  rw [mean_comm]
  refine mean_le_const _ _ _ (fun state _ => ?_)
  exact chargeCut_mean_le res sch adversary hsignLaw hpubLaw eps ε B Inv hmono hres hquery hpres hpub heps index fuel
    g.1 g.2.1 state g.2.2 _ 0 (hinit g hg) (by omega)

/-- The fork charge from a resampled key: twice the fuel times the per-call
average bound. The cut is the second scheme's, the branches the first's. -/
theorem chargeFork_le (res : Other → PMF Other) (hidem : ∀ other, (res other).bind res = res other)
    (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsignLaw₁ : ∀ (sk : SecretKey) (message : Message), PostLaw res (sch₁.sign sk message))
    (hpubLaw₁ : ∀ query : Query, PostLaw res (sch₁.publicOracle query))
    (hsignLaw₂ : ∀ (sk : SecretKey) (message : Message), PostLaw res (sch₂.sign sk message))
    (hpubLaw₂ : ∀ query : Query, PostLaw res (sch₂.publicOracle query))
    (eps : World HashInput Digest Other → ℝ≥0∞) (ε : ℝ≥0∞) (B : Nat) (Inv : Nat → World HashInput Digest Other → Prop)
    (hmono : ∀ (n m : Nat) (world : World HashInput Digest Other), n ≤ m → Inv n world → Inv m world)
    (hres : ∀ (n : Nat) (world : World HashInput Digest Other), Inv n world →
      ∀ w ∈ (resampleW res world).support, Inv n w)
    (hquery : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat)
      (r : Digest × (HashInput → Option Digest)), Inv n world →
      r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
    (hpres₁ : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
      (r : Signature × World HashInput Digest Other), Inv n world →
      r ∈ (sch₁.sign sk message world).support → Inv (n + 1) r.2)
    (hpub₁ : ∀ (query : Query) (world : World HashInput Digest Other) (n : Nat) (r : Answer × World HashInput Digest Other),
      Inv n world → r ∈ (sch₁.publicOracle query world).support → Inv (n + 1) r.2)
    (hpres₂ : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
      (r : Signature × World HashInput Digest Other), Inv n world →
      r ∈ (sch₂.sign sk message world).support → Inv (n + 1) r.2)
    (hpub₂ : ∀ (query : Query) (world : World HashInput Digest Other) (n : Nat) (r : Answer × World HashInput Digest Other),
      Inv n world → r ∈ (sch₂.publicOracle query world).support → Inv (n + 1) r.2)
    (hupdate : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat) (d : Digest), Inv n world →
      Inv (n + 1) { world with hashTable := Function.update world.hashTable input (some d) })
    (heps : ∀ world : World HashInput Digest Other, Inv B world → mean (resampleW res world) eps ≤ ε)
    (hkeygen : sch₂.keygen = sch₂.keygen.bind fun g => (resampleW res g.2.2).map fun w => (g.1, g.2.1, w))
    (hinit : ∀ generated ∈ sch₂.keygen.support, Inv 0 generated.2.2) (index fuel : Nat) (hB : 2 * fuel + 1 ≤ B) :
    chargeFork eps sch₁ sch₂ adversary index fuel ≤ 2 * fuel * ε := by
  unfold chargeFork cutExperiment
  rw [hkeygen, mean_bind, mean_bind]
  refine mean_le_const _ _ _ (fun g hg => ?_)
  rw [mean_map]
  dsimp only
  simp only [mean_bind]
  rw [mean_comm]
  refine mean_le_const _ _ _ (fun state _ => ?_)
  rw [← mean_bind, cut_postLaw res hidem sch₂ adversary hsignLaw₂ hpubLaw₂, mean_bind]
  refine mean_le_const _ _ _ (fun w hw => ?_)
  rw [mean_bind]
  refine mean_le_const _ _ _ (fun c hc => ?_)
  cases c with
  | ended t =>
    simp only [resampleCut, mean_pure]
    exact zero_le _
  | saved snapshot =>
    simp only [resampleCut, mean_map]
    have hrem : snapshot.remaining ≤ fuel :=
      ForkEventUnion.cut_remaining_le sch₂ adversary index fuel _ _ state _ _ _ hc snapshot rfl
    have hsup : Inv (0 + fuel) snapshot.world :=
      cut_saved_gen Inv hmono hquery sch₂ adversary hpres₂ hpub₂ index fuel _ _ state _ _ 0 (hres 0 g.2.2 (hinit g hg) w hw)
        _ hc snapshot rfl
    unfold chargeBranch
    dsimp only
    rw [mean_mul_left, mean_comm]
    calc 2 * mean (PMF.uniformOfFintype Digest) (fun answer => mean (resampleW res snapshot.world) fun w' =>
          charge eps sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer)
            { w' with hashTable := Function.update w'.hashTable snapshot.input (some answer) }
            { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) ≤
        2 * mean (PMF.uniformOfFintype Digest) (fun _ => (snapshot.remaining : ℝ≥0∞) * ε) := by
          refine mul_le_mul' le_rfl (mean_le_mean _ _ _ fun answer _ => ?_)
          calc _ ≤ mean (resampleW res snapshot.world) (fun w' =>
                charge eps sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer)
                  { w' with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) }
                  { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) :=
                mean_le_mean _ _ _ fun w' hw' => le_of_eq (by rw [hashTable_of_mem res snapshot.world w' hw'])
            _ = mean (resampleW res
                { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) })
                (fun w' => charge eps sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey
                  (snapshot.next answer) w'
                  { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) :=
                (mean_resampleW_update res snapshot.world
                  (Function.update snapshot.world.hashTable snapshot.input (some answer))
                  (fun w' => charge eps sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey
                    (snapshot.next answer) w'
                    { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests })).symm
            _ ≤ _ :=
                charge_mean_le res sch₁ adversary hsignLaw₁ hpubLaw₁ eps ε B Inv hmono hres hquery hpres₁ hpub₁ heps
                  snapshot.remaining _ _ _ _ _ (0 + fuel + 1) (hupdate snapshot.world snapshot.input _ answer hsup)
                  (by omega)
      _ = 2 * snapshot.remaining * ε := by rw [mean_const, mul_assoc]
      _ ≤ 2 * fuel * ε := mul_le_mul' (mul_le_mul' le_rfl (Nat.cast_le.mpr hrem)) le_rfl

end
end SDitH.Proofs.ChargeCutExpect
