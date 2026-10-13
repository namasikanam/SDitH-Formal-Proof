import SDitH.Proofs.ForkRestoreEq

/-! The end-resampled event fork. The restored event fork evaluates the
event at the snapshot with the family resampled after the first branch;
the second branch keeps that family, so by its resampling law the event
may as well be evaluated at the family resampled after the second branch,
when the event is insensitive to the attempts' embedded families. This is
the form whose continuations are family-free, as the pruned-run agreement
requires. -/

namespace SDitH.Proofs.ForkRestoreEnd

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher
open Spec.DomainSeparation (Bits)
open Spec.RandomOracleTrap (indicator)
open GameResample ChargeExpect RunWorld GamePrune PruneLawRun HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open ForkRestoreShift ForkRestoreEq SharedResample SignBridge HiddenSlice MeanHybrid ChargeCutExpect
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}

/-- A terminal with its attempt's embedded family replaced. -/
def setFamilyT (f : Family (Bits lambda) (Bits lambda))
    (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) :
    Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query :=
  match t with
  | .attempt a => .attempt { a with world := setFamily a.world f }
  | t => t

/-- A branch with its attempt's embedded family replaced. -/
def setFamilyBranch (f : Family (Bits lambda) (Bits lambda))
    (b : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) :
    Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query :=
  ⟨b.answer, { b.checked with terminal := setFamilyT f b.checked.terminal }⟩

omit [Fintype Digest] [Nonempty Digest] in
theorem withWorld_setFamily (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (w : GW HashInput Digest lambda s wit rnd) (f : Family (Bits lambda) (Bits lambda)) :
    withWorld t (setFamily w f) = setFamilyT f (withWorld t w) := by
  cases t <;> rfl

/-- Finalizing a terminal with its family replaced. -/
theorem finalize_setFamilyT (f : Family (Bits lambda) (Bits lambda))
    (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) :
    finalize (setFamilyT f t) = (finalize t).map fun c => { c with terminal := setFamilyT f c.terminal } := by
  cases t with
  | attempt a =>
    simp only [setFamilyT, finalize, PMF.map_comp]
    rfl
  | exhausted trace => simp only [setFamilyT, finalize, PMF.pure_map]
  | aborted trace => simp only [setFamilyT, finalize, PMF.pure_map]
  | rejected trace => simp only [setFamilyT, finalize, PMF.pure_map]

variable (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)

/-- In the run with its final world, an attempt's embedded world is the
final world. -/
theorem runW_attempt : ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (w : GW HashInput Digest lambda s wit rnd)
    (trace : Trace Message HashInput Query), ∀ r ∈ (runW scheme adversary fuel pk sk state w trace).support,
    withWorld r.1 r.2 = r.1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state w trace r hr
    simp only [runW, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rfl
  | succ fuel ih =>
    intro pk sk state w trace r hr
    simp only [runW, PMF.mem_support_bind_iff] at hr
    obtain ⟨action, -, hr⟩ := hr
    cases action with
    | abort =>
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      rfl
    | finish message signature =>
      simp only [PMF.support_map, Set.mem_image] at hr
      obtain ⟨result, -, rfl⟩ := hr
      cases result.1 <;> rfl
    | sign message next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, -, hr⟩ := hr
      exact ih pk sk _ _ _ r hr
    | hash input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, -, hr⟩ := hr
      exact ih pk sk _ _ _ r hr
    | query input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, -, hr⟩ := hr
      exact ih pk sk _ _ _ r hr

/-- The fresh branch with its final world keeps the family. -/
theorem freshBranchW_family (hsignF : ∀ sk m, KeepsFamily (scheme.sign sk m)) (hpubF : ∀ q, KeepsFamily (scheme.publicOracle q))
    (hprepF : ∀ pk m sig, KeepsFamily (scheme.prepareVerification pk m sig))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (rw : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd) (h : rw ∈ (freshBranchW scheme adversary snapshot).support) :
    rw.2.other.family = snapshot.world.other.family := by
  unfold freshBranchW at h
  obtain ⟨answer, -, h⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
  obtain ⟨r, hr, h⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
  obtain ⟨c, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  exact runW_family scheme adversary hsignF hpubF hprepF _ _ _ _
    { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) } _ r hr

/-- The mean over the fresh branch through the branch with its final world. -/
theorem mean_freshBranch_eq_W
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (φ : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query → ℝ≥0∞) :
    mean (freshBranch scheme adversary snapshot) φ = mean (freshBranchW scheme adversary snapshot) fun rw => φ rw.1 := by
  rw [← freshBranchW_fst, mean_map]

omit [Fintype Digest] [Nonempty Digest] in
/-- Resampling then updating the table from the world's own table is
resampling the updated world. -/
theorem mean_resampleW_update' (X : GW HashInput Digest lambda s wit rnd)
    (T : (HashInput → Option Digest) → (HashInput → Option Digest)) (φ : GW HashInput Digest lambda s wit rnd → ℝ≥0∞) :
    mean (resampleW resample X) (fun y => φ { y with hashTable := T y.hashTable }) =
      mean (resampleW resample { X with hashTable := T X.hashTable }) φ := by
  conv_rhs => rw [mean_resampleW_update]
  refine mean_congr_support _ (fun y : GW HashInput Digest lambda s wit rnd => φ { y with hashTable := T y.hashTable })
    (fun y : GW HashInput Digest lambda s wit rnd => φ { y with hashTable := T X.hashTable }) fun y hy => ?_
  dsimp only
  rw [hashTable_of_mem resample X y hy]

omit [Fintype Digest] [Nonempty Digest] in
/-- Resampling then restoring is resampling the restored world. -/
theorem mean_resampleW_restore (B X : GW HashInput Digest lambda s wit rnd) (G : GW HashInput Digest lambda s wit rnd → ℝ≥0∞) :
    mean (resampleW resample X) (fun w' => G (restore B w')) = mean (resampleW resample (restore B X)) G := by
  simp only [resampleW, resample, PMF.map_comp, mean_map, Function.comp_def, restore]

/-- The resampling law of the second branch: a function of the branch and
its final family, insensitive to the attempt's embedded family, averages
the same with the family resampled at the end. -/
theorem right_end_resample (hsignLaw : ∀ sk m, PostLaw resample (scheme.sign sk m))
    (hpubLaw : ∀ q, PostLaw resample (scheme.publicOracle q))
    (hprepLaw : ∀ pk m sig, PostLaw resample (scheme.prepareVerification pk m sig))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (Ψ : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query →
      Family (Bits lambda) (Bits lambda) → ℝ≥0∞)
    (hΨ : ∀ b f g, Ψ (setFamilyBranch g b) f = Ψ b f) :
    mean (resampleW resample snapshot.world) (fun y =>
        mean (freshBranchW scheme adversary { snapshot with world := y }) fun rw => Ψ rw.1 rw.2.other.family) =
      mean (resampleW resample snapshot.world) (fun y =>
        mean (freshBranchW scheme adversary { snapshot with world := y }) fun rw =>
          mean (resampleW resample rw.2) fun w'' => Ψ rw.1 w''.other.family) := by
  simp only [freshBranchW, mean_bind, mean_map]
  rw [mean_comm]
  conv_rhs => rw [mean_comm]
  refine congrArg _ (funext fun answer => ?_)
  rw [mean_resampleW_update' snapshot.world (fun t => Function.update t snapshot.input (some answer))
    (fun y => mean (runW scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) y
      { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
        mean (finalize r.1) fun c => Ψ ⟨answer, c⟩ r.2.other.family)]
  conv_rhs => rw [mean_resampleW_update' snapshot.world (fun t => Function.update t snapshot.input (some answer))
    (fun y => mean (runW scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) y
      { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
        mean (finalize r.1) fun c => mean (resampleW resample r.2) fun w'' => Ψ ⟨answer, c⟩ w''.other.family)]
  rw [runW_postLaw_mean scheme adversary hsignLaw hpubLaw hprepLaw]
  refine mean_congr_support _ _ _ fun y hy => mean_congr_support _ _ _ fun r hr => ?_
  conv_rhs => rw [mean_comm]
  refine mean_congr_support _ _ _ fun w' hw' => ?_
  obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW r.2 w' hw'
  rw [withWorld_setFamily, runW_attempt scheme adversary _ _ _ _ _ _ r hr, finalize_setFamilyT, mean_map]
  refine congrArg _ (funext fun c => ?_)
  exact hΨ ⟨answer, c⟩ _ f

variable (E : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State →
    Option (Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) → Bool)

/-- The end-resampled event fork. -/
def forkEventE (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query State) : PMF Bool :=
  match snapshot.world.hashTable snapshot.input with
  | some _ => PMF.pure (E snapshot none)
  | none => (PMF.uniformOfFintype Digest).bind fun answer =>
      (runW scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer)
        { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) }
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }).bind fun r =>
      (resampleW resample r.2).bind fun w' =>
        (finalize (withWorld r.1 w')).bind fun checked =>
          (freshBranchW scheme adversary { snapshot with world := restore snapshot.world w' }).bind fun rw =>
            (resampleW resample rw.2).map fun w'' =>
              E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨answer, checked⟩, rw.1))

/-- The restored and the end-resampled event forks agree, for an event
insensitive to the attempts' embedded families. -/
theorem forkEventR_eq_E (hsignLaw : ∀ sk m, PostLaw resample (scheme.sign sk m))
    (hpubLaw : ∀ q, PostLaw resample (scheme.publicOracle q))
    (hprepLaw : ∀ pk m sig, PostLaw resample (scheme.prepareVerification pk m sig))
    (hsignF : ∀ sk m, KeepsFamily (scheme.sign sk m)) (hpubF : ∀ q, KeepsFamily (scheme.publicOracle q))
    (hprepF : ∀ pk m sig, KeepsFamily (scheme.prepareVerification pk m sig))
    (hEleft : ∀ snapshot' left right g, E snapshot' (some (setFamilyBranch g left, right)) = E snapshot' (some (left, right)))
    (hEright : ∀ snapshot' left right g, E snapshot' (some (left, setFamilyBranch g right)) = E snapshot' (some (left, right)))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State) :
    (forkEventR scheme adversary E snapshot) true = (forkEventE scheme adversary E snapshot) true := by
  cases hlook : snapshot.world.hashTable snapshot.input with
  | some d => simp only [forkEventR, forkEventE, hlook]
  | none =>
    simp only [forkEventR, forkEventE, hlook, mean_bind_apply, map_true]
    refine congrArg _ (funext fun answer => ?_)
    refine mean_congr_support _ _ _ fun r hr => ?_
    -- the first branch's checked terminal carries the resampled family, which the event ignores
    have hleft : ∀ (w' : GW HashInput Digest lambda s wit rnd), w' ∈ (resampleW resample r.2).support →
        ∀ (φ : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query → ℝ≥0∞),
        (∀ c g, φ { c with terminal := setFamilyT g c.terminal } = φ c) →
        mean (finalize (withWorld r.1 w')) φ = mean (finalize r.1) φ := by
      intro w' hw' φ hφ
      obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW r.2 w' hw'
      rw [withWorld_setFamily, runW_attempt scheme adversary _ _ _ _ _ _ r hr, finalize_setFamilyT, mean_map]
      exact congrArg _ (funext fun c => hφ c f)
    have hL : mean (resampleW resample r.2) (fun w' => mean (finalize (withWorld r.1 w')) fun c =>
        mean (freshBranch scheme adversary { snapshot with world := restore snapshot.world w' }) fun right =>
          indicator (E { snapshot with world := setFamily snapshot.world w'.other.family } (some (⟨answer, c⟩, right)))) =
        mean (finalize r.1) fun c => mean (resampleW resample r.2) fun w' =>
          mean (freshBranch scheme adversary { snapshot with world := restore snapshot.world w' }) fun right =>
            indicator (E { snapshot with world := setFamily snapshot.world w'.other.family } (some (⟨answer, c⟩, right))) := by
      rw [← mean_comm]
      refine mean_congr_support _ _ _ fun w' hw' => hleft w' hw' _ fun c g => ?_
      refine congrArg _ (funext fun right => ?_)
      exact congrArg _ (hEleft _ ⟨answer, c⟩ right g)
    have hR : mean (resampleW resample r.2) (fun w' => mean (finalize (withWorld r.1 w')) fun c =>
        mean (freshBranchW scheme adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
          mean (resampleW resample rw.2) fun w'' =>
            indicator (E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨answer, c⟩, rw.1)))) =
        mean (finalize r.1) fun c => mean (resampleW resample r.2) fun w' =>
          mean (freshBranchW scheme adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
            mean (resampleW resample rw.2) fun w'' =>
              indicator (E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨answer, c⟩, rw.1))) := by
      rw [← mean_comm]
      refine mean_congr_support _ _ _ fun w' hw' => hleft w' hw' _ fun c g => ?_
      refine congrArg _ (funext fun rw => congrArg _ (funext fun w'' => ?_))
      exact congrArg _ (hEleft _ ⟨answer, c⟩ rw.1 g)
    rw [hL, hR]
    refine congrArg _ (funext fun c => ?_)
    -- the second branch: the family at the end
    have hfam : ∀ w', mean (freshBranch scheme adversary { snapshot with world := restore snapshot.world w' }) (fun right =>
        indicator (E { snapshot with world := setFamily snapshot.world w'.other.family } (some (⟨answer, c⟩, right)))) =
        mean (freshBranchW scheme adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
          indicator (E { snapshot with world := setFamily snapshot.world rw.2.other.family } (some (⟨answer, c⟩, rw.1))) := by
      intro w'
      rw [mean_freshBranch_eq_W]
      refine mean_congr_support _ _ _ fun rw hrw => ?_
      rw [freshBranchW_family scheme adversary hsignF hpubF hprepF _ rw hrw]
      rfl
    simp only [hfam]
    rw [mean_resampleW_restore snapshot.world r.2 (fun y => mean (freshBranchW scheme adversary { snapshot with world := y }) fun rw =>
        indicator (E { snapshot with world := setFamily snapshot.world rw.2.other.family } (some (⟨answer, c⟩, rw.1)))),
      mean_resampleW_restore snapshot.world r.2 (fun y => mean (freshBranchW scheme adversary { snapshot with world := y }) fun rw =>
        mean (resampleW resample rw.2) fun w'' =>
          indicator (E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨answer, c⟩, rw.1))))]
    have h := right_end_resample scheme adversary hsignLaw hpubLaw hprepLaw { snapshot with world := restore snapshot.world r.2 }
      (fun b f => indicator (E { snapshot with world := setFamily snapshot.world f } (some (⟨answer, c⟩, b))))
      (fun b f g => by simp only [hEright])
    simpa using h

end
end SDitH.Proofs.ForkRestoreEnd
