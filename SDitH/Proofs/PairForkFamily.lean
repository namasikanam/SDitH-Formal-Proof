import SDitH.Proofs.PairFork

/-! The fork bound for family-dependent events: an event that, at the
snapshot with a family, implies a predicate of that family on the union of
the two attempt histories (a predicate reading the branches' bodies, the
union as a set and the family) has probability at most the mean, along the
restored fork, of the predicate under the family resampled at the end of
the second branch. The plain fork is read in its common form, the second
branch is shifted from the empty-history base, the union of the attempt
histories is the same set for the plain and the restored second branch,
and the family of the restored branch is resampled at its end. -/

namespace SDitH.Proofs.PairForkFamily

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher Spec.IdealCipherPairCollision
open Spec.DomainSeparation (Bits)
open Spec.RandomOracleTrap (indicator)
open GameResample ChargeExpect RunWorld GamePrune HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open ForkRestoreShift ForkRestoreEq ForkRestoreEnd SharedResample HiddenSlice MeanHybrid PairMass PairOracles PairRun
open PairFork SignBridge PruneCompatClosure
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}
  (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (Φ : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query →
    Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query →
    Family (Bits lambda) (Bits lambda) → List (Entry (Bits lambda) (Bits lambda)) → Bool)
  (hΦset : ∀ left right g U U', (∀ x, x ∈ U ↔ x ∈ U') → Φ left right g U = Φ left right g U')
  (hΦshift : ∀ left right g U H, Φ left (shiftBranch H right) g U = Φ left right g U)
  (hΦfamL : ∀ left right g U f, Φ (setFamilyBranch f left) right g U = Φ left right g U)
  (hΦfamR : ∀ left right g U f, Φ left (setFamilyBranch f right) g U = Φ left right g U)
  (E : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State →
    Option (Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) → Bool)
  (hnone : ∀ snapshot', E snapshot' none = false)
  (hEleft : ∀ snapshot' left right, E snapshot' (some (left, right)) = true →
    ∃ att, left.checked.terminal = Terminal.attempt att)
  (hEfamL : ∀ snapshot' left right g, E snapshot' (some (setFamilyBranch g left, right)) = E snapshot' (some (left, right)))
  (hE : ∀ (snapshot' : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query
      State) left right (g : Family (Bits lambda) (Bits lambda)),
    E { snapshot' with world := setFamily snapshot'.world g } (some (left, right)) = true →
      Φ left right g (attemptHistory right ++ attemptHistory left) = true)
  (hsignLaw : ∀ (sk : SecretKey) (message : Message), PostLaw resample (sch.sign sk message))
  (hpubLaw : ∀ query : Query, PostLaw resample (sch.publicOracle query))
  (hprepLaw : ∀ pk m sig, PostLaw resample (sch.prepareVerification pk m sig))
  (hsignF : ∀ sk m, KeepsFamily (sch.sign sk m)) (hpubF : ∀ q, KeepsFamily (sch.publicOracle q))
  (hprepF : ∀ pk m sig, KeepsFamily (sch.prepareVerification pk m sig))
  (hsignG : ∀ sk m, Grows (sch.sign sk m)) (hpubG : ∀ q, Grows (sch.publicOracle q))
  (hprepG : ∀ pk m sig, Grows (sch.prepareVerification pk m sig))
  (hsignS : ∀ sk m, ShiftLaw (sch.sign sk m)) (hpubS : ∀ q, ShiftLaw (sch.publicOracle q))
  (hprepS : ∀ pk m sig, ShiftLaw (sch.prepareVerification pk m sig))

omit [Fintype Digest] [Nonempty Digest] in
/-- The union of the attempt histories of the second branch shifted by the
snapshot's history and of the first branch, and of the second branch
shifted by the first branch's final history and of the first branch, are
the same set when the first branch's final history extends the
snapshot's. -/
theorem union_shift_iff (H₁ H₂ : List (Entry (Bits lambda) (Bits lambda))) (hsub : H₁ ⊆ H₂)
    (left : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (hleft : ∀ x ∈ H₂, x ∈ attemptHistory left)
    (right : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) (x) :
    x ∈ attemptHistory (shiftBranch H₁ right) ++ attemptHistory left ↔
      x ∈ attemptHistory (shiftBranch H₂ right) ++ attemptHistory left := by
  unfold attemptHistory shiftBranch shiftT
  cases right.checked.terminal with
  | attempt a =>
    simp only [shiftG, List.mem_append]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (hleft x (hsub h))
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (hleft x h)
      · exact Or.inr h
  | exhausted t => simp
  | aborted t => simp
  | rejected t => simp

include hΦset hΦshift hΦfamR hnone hEleft hEfamL hE hsignLaw hpubLaw hprepLaw hsignF hpubF hprepF hsignG hpubG hprepG hsignS hpubS
  hprepS in
/-- The fork bound for a family-dependent event: the plain fork's event is
at most the restored chain's mean of the predicate under the family
resampled at the end of the second branch. -/
theorem fork_family_bound
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State) :
    mean (resampleW resample snapshot.world) (fun w =>
        ((forkAt sch adversary { snapshot with world := w }).map (E { snapshot with world := w })) true) ≤
      mean (PMF.uniformOfFintype Digest) fun a =>
        mean (resampleW resample { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) })
          fun w =>
          mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) w
              { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
            mean (finalize r.1) fun c =>
              mean (resampleW resample (restore snapshot.world r.2)) fun y =>
                mean (freshBranchW sch adversary { snapshot with world := y }) fun rw =>
                  mean (resampleW resample rw.2) fun w'' =>
                    indicator (Φ ⟨a, c⟩ rw.1 w''.other.family (attemptHistory rw.1 ++ attemptHistory ⟨a, c⟩)) := by
  cases hlook : snapshot.world.hashTable snapshot.input with
  | some d =>
    refine (mean_le_const _ _ 0 fun w hw => ?_).trans (zero_le _)
    have hl : w.hashTable snapshot.input = some d := by
      rw [hashTable_of_mem resample snapshot.world w hw]
      exact hlook
    simp only [forkAt, hl, PMF.pure_map, hnone, PMF.pure_apply]
    simp
  | none =>
    rw [shared_eq_common sch adversary E hsignLaw hpubLaw hprepLaw hsignF hpubF hprepF snapshot hlook]
    unfold common
    refine mean_le_mean _ _ _ fun a _ => ?_
    set Wa : GW HashInput Digest lambda s wit rnd :=
      { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) } with hWa
    refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
    obtain ⟨new, hnew⟩ := runW_history sch adversary hsignG hpubG hprepG _ _ _ _ _ _ r hr
    have hwhist : w.other.cipherHistory = snapshot.world.other.cipherHistory := history_of_mem_resampleW Wa w hw
    have hr2hist : r.2.other.cipherHistory = new ++ snapshot.world.other.cipherHistory := by rw [hnew, hwhist]
    -- the pointwise step at a resampled family and a checked first branch
    have hpt : ∀ w' ∈ (resampleW resample r.2).support, ∀ c, c.terminal = r.1 →
        mean (freshBranch sch adversary { snapshot with world := setFamily snapshot.world w'.other.family }) (fun right =>
          indicator (E { snapshot with world := setFamily snapshot.world w'.other.family } (some (⟨a, c⟩, right)))) ≤
        mean (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
          indicator (Φ ⟨a, c⟩ rw.1 w'.other.family (attemptHistory rw.1 ++ attemptHistory ⟨a, c⟩)) := by
      intro w' hw' c hcterm
      have hw'hist : w'.other.cipherHistory = new ++ snapshot.world.other.cipherHistory := by
        rw [history_of_mem_resampleW _ _ hw', hr2hist]
      have hsub : snapshot.world.other.cipherHistory ⊆ w'.other.cipherHistory := by
        rw [hw'hist]
        exact List.subset_append_right _ _
      have hL : freshBranch sch adversary { snapshot with world := setFamily snapshot.world w'.other.family } =
          (freshBranch sch adversary { snapshot with world := { snapshot.world with other :=
            { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }).map
            (shiftBranch snapshot.world.other.cipherHistory) := by
        rw [setFamily_eq_shiftG]
        have := freshBranch_shift sch adversary hsignS hpubS hprepS { snapshot with world :=
          { snapshot.world with other := { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }
          snapshot.world.other.cipherHistory
        simp only at this
        exact this
      have hR : freshBranchW sch adversary { snapshot with world := restore snapshot.world w' } =
          (freshBranchW sch adversary { snapshot with world := { snapshot.world with other :=
            { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }).map
            (fun rw => (shiftBranch w'.other.cipherHistory rw.1, shiftG w'.other.cipherHistory rw.2)) := by
        rw [restore_eq_shiftG]
        have := freshBranchW_shift sch adversary hsignS hpubS hprepS { snapshot with world :=
          { snapshot.world with other := { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }
          w'.other.cipherHistory
        simp only at this
        exact this
      rw [hL, mean_map, ← freshBranchW_fst, mean_map, hR, mean_map]
      refine mean_le_mean _ _ _ fun rw _ => ?_
      dsimp only
      cases hEv : E { snapshot with world := setFamily snapshot.world w'.other.family }
          (some (⟨a, c⟩, shiftBranch snapshot.world.other.cipherHistory rw.1)) with
      | false => simp [indicator]
      | true =>
        rw [RandomOracleTrap.indicator_true]
        have hΦ := hE _ ⟨a, c⟩ _ _ hEv
        -- the first branch is an attempt embedding the run's final world
        obtain ⟨att, hatt⟩ := hEleft _ _ _ hEv
        have hatt' : c.terminal = Terminal.attempt att := hatt
        have hr1 : r.1 = Terminal.attempt att := by rw [← hcterm, hatt']
        have hwa := runW_attempt sch adversary _ _ _ _ _ _ r hr
        rw [hr1] at hwa
        simp only [withWorld, Terminal.attempt.injEq] at hwa
        have hworld : r.2 = att.world := by simpa using congrArg Attempt.world hwa
        have hAH : attemptHistory (⟨a, c⟩ : Branch Message Signature HashInput Digest
            (Spec.SharedScheme.World lambda s wit rnd) Query) = att.world.other.cipherHistory := by
          unfold attemptHistory
          dsimp only
          rw [hatt']
        have hleft : ∀ x ∈ w'.other.cipherHistory, x ∈ attemptHistory (⟨a, c⟩ : Branch Message Signature HashInput Digest
            (Spec.SharedScheme.World lambda s wit rnd) Query) := by
          intro x hx
          rw [hAH, ← hworld, ← history_of_mem_resampleW _ _ hw']
          exact hx
        rw [hΦshift] at hΦ
        rw [hΦshift, ← hΦset ⟨a, c⟩ rw.1 _ _ _ (fun x => union_shift_iff _ _ hsub ⟨a, c⟩ hleft rw.1 x), hΦ]
        exact le_rfl
    -- swap the checked first branch out of the resampling
    have hswap : mean (resampleW resample r.2) (fun w' => mean (finalize (withWorld r.1 w')) fun c =>
        mean (freshBranch sch adversary { snapshot with world := setFamily snapshot.world w'.other.family }) fun right =>
          indicator (E { snapshot with world := setFamily snapshot.world w'.other.family } (some (⟨a, c⟩, right)))) =
        mean (finalize r.1) fun c => mean (resampleW resample r.2) fun w' =>
          mean (freshBranch sch adversary { snapshot with world := setFamily snapshot.world w'.other.family }) fun right =>
            indicator (E { snapshot with world := setFamily snapshot.world w'.other.family } (some (⟨a, c⟩, right))) := by
      rw [← mean_comm]
      refine mean_congr_support _ _ _ fun w' hw' => ?_
      obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW r.2 w' hw'
      rw [withWorld_setFamily, runW_attempt sch adversary _ _ _ _ _ _ r hr, finalize_setFamilyT, mean_map]
      refine congrArg _ (funext fun c => ?_)
      refine congrArg _ (funext fun right => ?_)
      exact congrArg _ (hEfamL _ ⟨a, c⟩ right f)
    rw [hswap]
    refine mean_le_mean _ _ _ fun c hc => ?_
    have hcterm : c.terminal = r.1 := finalize_terminal r.1 c hc
    calc mean (resampleW resample r.2) (fun w' =>
            mean (freshBranch sch adversary { snapshot with world := setFamily snapshot.world w'.other.family }) fun right =>
              indicator (E { snapshot with world := setFamily snapshot.world w'.other.family } (some (⟨a, c⟩, right))))
        ≤ mean (resampleW resample r.2) (fun w' =>
            mean (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
              indicator (Φ ⟨a, c⟩ rw.1 w'.other.family (attemptHistory rw.1 ++ attemptHistory ⟨a, c⟩))) :=
          mean_le_mean _ _ _ fun w' hw' => hpt w' hw' c hcterm
      _ = mean (resampleW resample r.2) (fun w' =>
            mean (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
              indicator (Φ ⟨a, c⟩ rw.1 rw.2.other.family (attemptHistory rw.1 ++ attemptHistory ⟨a, c⟩))) := by
          refine mean_congr_support _ _ _ fun w' _ => mean_congr_support _ _ _ fun rw hrw => ?_
          rw [freshBranchW_family sch adversary hsignF hpubF hprepF _ rw hrw]
          rfl
      _ = mean (resampleW resample (restore snapshot.world r.2)) (fun y =>
            mean (freshBranchW sch adversary { snapshot with world := y }) fun rw =>
              indicator (Φ ⟨a, c⟩ rw.1 rw.2.other.family (attemptHistory rw.1 ++ attemptHistory ⟨a, c⟩))) :=
          mean_resampleW_restore snapshot.world r.2 (fun y =>
            mean (freshBranchW sch adversary { snapshot with world := y }) fun rw =>
              indicator (Φ ⟨a, c⟩ rw.1 rw.2.other.family (attemptHistory rw.1 ++ attemptHistory ⟨a, c⟩)))
      _ = _ :=
          right_end_resample sch adversary hsignLaw hpubLaw hprepLaw { snapshot with world := restore snapshot.world r.2 }
            (fun b f => indicator (Φ ⟨a, c⟩ b f (attemptHistory b ++ attemptHistory ⟨a, c⟩)))
            (fun b f g => by dsimp only; rw [attemptHistory_setFamily, hΦfamR])

end
end SDitH.Proofs.PairForkFamily
