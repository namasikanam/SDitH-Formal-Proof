import SDitH.Spec.SignatureReplay

/-! The signature game under resampling of the hidden state. With a
resampling operator on the other-state that is idempotent and commutes
with the signing and public oracles (a run then a continuation equals the
run, a fresh resampling of the result, then the continuation), the game
run from a resampled world equals the run of the scheme whose signing
oracle resamples the world before signing. When key generation already
yields a resampled world, the terminal laws, the experiments and the
advantages of the two schemes coincide. -/

namespace SDitH.Proofs.GameResample

open Spec.SignatureSecurity
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- Resampling the other-state of a game world. -/
def resampleW (res : Other → PMF Other) (world : World HashInput Digest Other) : PMF (World HashInput Digest Other) :=
  (res world.other).map fun other => { world with other := other }

/-- The scheme whose signing oracle resamples the world before signing. -/
def resampled (res : Other → PMF Other)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer) :
    Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer :=
  { sch with sign := fun sk message world => (resampleW res world).bind (sch.sign sk message) }

omit [Fintype Digest] [Nonempty Digest] in
theorem resampled_sign (res : Other → PMF Other)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer) (sk : SecretKey)
    (message : Message) (world : World HashInput Digest Other) :
    (resampled res sch).sign sk message world = (resampleW res world).bind (sch.sign sk message) := rfl

omit [Fintype Digest] [Nonempty Digest] in
theorem resampled_publicOracle (res : Other → PMF Other)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer) (query : Query)
    (world : World HashInput Digest Other) :
    (resampled res sch).publicOracle query world = sch.publicOracle query world := rfl

omit [Fintype Digest] [Nonempty Digest] in
/-- Idempotent resampling lifts to worlds. -/
theorem resampleW_bind {R : Type*} (res : Other → PMF Other) (hidem : ∀ other, (res other).bind res = res other)
    (world : World HashInput Digest Other) (g : World HashInput Digest Other → PMF R) :
    (resampleW res world).bind (fun w => (resampleW res w).bind g) = (resampleW res world).bind g := by
  unfold resampleW
  simp only [PMF.bind_map, Function.comp_def]
  rw [← PMF.bind_bind, hidem]

/-- The game run from a resampled world equals the run of the resampling
scheme. -/
theorem run_resample (res : Other → PMF Other) (hidem : ∀ other, (res other).bind res = res other)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsign : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other)
      (K : Signature × World HashInput Digest Other → PMF (Terminal Message Signature HashInput Digest Other Query)),
      (resampleW res world).bind (fun w => (sch.sign sk message w).bind K) =
        (resampleW res world).bind (fun w => (sch.sign sk message w).bind fun r =>
          (resampleW res r.2).bind fun w' => K (r.1, w')))
    (hpub : ∀ (query : Query) (world : World HashInput Digest Other)
      (K : Answer × World HashInput Digest Other → PMF (Terminal Message Signature HashInput Digest Other Query)),
      (resampleW res world).bind (fun w => (sch.publicOracle query w).bind K) =
        (resampleW res world).bind (fun w => (sch.publicOracle query w).bind fun r =>
          (resampleW res r.2).bind fun w' => K (r.1, w')))
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : World HashInput Digest Other)
    (trace : Trace Message HashInput Query) :
    (resampleW res world).bind (fun w => run sch adversary fuel pk sk state w trace) =
      (resampleW res world).bind (fun w => run (resampled res sch) adversary fuel pk sk state w trace) := by
  induction fuel generalizing state world trace with
  | zero => simp only [run]
  | succ fuel ih =>
    simp only [run]
    rw [PMF.bind_comm]
    conv_rhs => rw [PMF.bind_comm]
    congr 1
    funext action
    cases action with
    | abort => rfl
    | finish message signature => rfl
    | sign message next =>
      dsimp only
      simp only [resampled_sign, PMF.bind_bind]
      rw [resampleW_bind res hidem]
      conv_lhs => rw [hsign]
      conv_rhs => rw [hsign]
      congr 1
      funext w
      congr 1
      funext r
      exact ih (next r.1) r.2 _
    | hash input next =>
      simp only [resampleW, PMF.bind_map, Function.comp_def]
      rw [PMF.bind_comm]
      conv_rhs => rw [PMF.bind_comm]
      congr 1
      funext result
      have h := ih (next result.1) { world with hashTable := result.2 }
        { trace with hashRequests := input :: trace.hashRequests }
      simp only [resampleW, PMF.bind_map, Function.comp_def] at h
      exact h
    | query input next =>
      dsimp only
      simp only [resampled_publicOracle]
      conv_lhs => rw [hpub]
      conv_rhs => rw [hpub]
      congr 1
      funext w
      congr 1
      funext r
      exact ih (next r.1) r.2 _

/-- With key generation yielding a resampled world, the terminal laws of the
scheme and of its resampling scheme coincide. -/
theorem terminalLaw_resample (res : Other → PMF Other) (hidem : ∀ other, (res other).bind res = res other)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsign : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other)
      (K : Signature × World HashInput Digest Other → PMF (Terminal Message Signature HashInput Digest Other Query)),
      (resampleW res world).bind (fun w => (sch.sign sk message w).bind K) =
        (resampleW res world).bind (fun w => (sch.sign sk message w).bind fun r =>
          (resampleW res r.2).bind fun w' => K (r.1, w')))
    (hpub : ∀ (query : Query) (world : World HashInput Digest Other)
      (K : Answer × World HashInput Digest Other → PMF (Terminal Message Signature HashInput Digest Other Query)),
      (resampleW res world).bind (fun w => (sch.publicOracle query w).bind K) =
        (resampleW res world).bind (fun w => (sch.publicOracle query w).bind fun r =>
          (resampleW res r.2).bind fun w' => K (r.1, w')))
    (hkeygen : sch.keygen = sch.keygen.bind fun g => (resampleW res g.2.2).map fun w => (g.1, g.2.1, w))
    (fuel : Nat) :
    terminalLaw sch adversary fuel = terminalLaw (resampled res sch) adversary fuel := by
  unfold terminalLaw
  rw [show (resampled res sch).keygen = sch.keygen from rfl, hkeygen]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  congr 1
  funext g
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext state
  exact run_resample res hidem sch adversary hsign hpub fuel g.1 g.2.1 state g.2.2 ⟨[], [], []⟩

/-- The advantages coincide. -/
theorem advantage_resample (res : Other → PMF Other) (hidem : ∀ other, (res other).bind res = res other)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsign : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other)
      (K : Signature × World HashInput Digest Other → PMF (Terminal Message Signature HashInput Digest Other Query)),
      (resampleW res world).bind (fun w => (sch.sign sk message w).bind K) =
        (resampleW res world).bind (fun w => (sch.sign sk message w).bind fun r =>
          (resampleW res r.2).bind fun w' => K (r.1, w')))
    (hpub : ∀ (query : Query) (world : World HashInput Digest Other)
      (K : Answer × World HashInput Digest Other → PMF (Terminal Message Signature HashInput Digest Other Query)),
      (resampleW res world).bind (fun w => (sch.publicOracle query w).bind K) =
        (resampleW res world).bind (fun w => (sch.publicOracle query w).bind fun r =>
          (resampleW res r.2).bind fun w' => K (r.1, w')))
    (hkeygen : sch.keygen = sch.keygen.bind fun g => (resampleW res g.2.2).map fun w => (g.1, g.2.1, w))
    (fuel : Nat) :
    advantage sch adversary fuel = advantage (resampled res sch) adversary fuel := by
  unfold advantage experiment
  rw [terminalLaw_resample res hidem sch adversary hsign hpub hkeygen fuel]

end
end SDitH.Proofs.GameResample
