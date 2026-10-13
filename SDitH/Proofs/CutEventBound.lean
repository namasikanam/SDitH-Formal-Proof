import SDitH.Proofs.GameEventBoundLen

/-! The size-dependent event bound along the cut, the prefix of the game
up to a selected adversarial hash action. The event at a saved snapshot's
world or at an ended attempt's world is bounded as along the run, and the
snapshot's size plus its remaining growth stays below the level, which is
the premise the branch bounds need. Starting from key generation this
charges the prefix. -/

namespace SDitH.Proofs.CutEventBound

open Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrap
open GameEventBound (terminalBad)
open GameEventBoundLen (ServiceBoundLen)
open scoped Classical ENNReal
noncomputable section

variable {PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- The event at a saved snapshot's world or an ended attempt's world. -/
def cutBad (bad : Other → Bool) :
    Spec.SignatureReplay.Cut PublicKey (PublicKey × SecretKey) Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Other Query State → Bool
  | .saved snapshot => bad snapshot.world.other
  | .ended terminal => terminalBad bad terminal

variable (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
  (bad : Other → Bool) (size : Other → Nat) (growth : Nat) (epsilon : Nat → ℝ≥0∞)

/-- Along the cut, the event at the snapshot or attempt is bounded as along the run. -/
theorem cut_event_bound_len (hb : ServiceBoundLen components bad size growth epsilon) (hmono : Monotone epsilon)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State) (L : Nat) :
    ∀ (index fuel : Nat) (pk : PublicKey) (sk : PublicKey × SecretKey) (state : State)
      (world : World (HashInput PublicKey Message Payload) Digest Other)
      (trace : Trace Message (HashInput PublicKey Message Payload) Query),
      size world.other + fuel * (growth + growth) ≤ L →
      ((Spec.SignatureReplay.cut (scheme components) adversary index fuel pk sk state world trace).map (cutBad bad)) true ≤
        indicator (bad world.other) + fuel * (epsilon L + epsilon L) := by
  intro index fuel
  induction fuel generalizing index with
  | zero =>
    intro pk sk state world trace _
    simp [Spec.SignatureReplay.cut, PMF.pure_map, PMF.pure_apply, cutBad, terminalBad]
  | succ fuel ih =>
    intro pk sk state world trace hsize
    have hsucc : (fuel + 1) * (growth + growth) = fuel * (growth + growth) + (growth + growth) := Nat.succ_mul _ _
    rw [hsucc] at hsize
    simp only [Spec.SignatureReplay.cut, PMF.map_bind]
    refine ChallengeMixtures.bind_true_le _ _ _ fun action _ => ?_
    cases action with
    | abort =>
      simp [PMF.pure_map, PMF.pure_apply, cutBad, terminalBad]
    | finish message signature =>
      rw [PMF.map_comp]
      refine (ForkCutRun.map_true_mono _ _
        (fun r : Option (HashInput PublicKey Message Payload) × World (HashInput PublicKey Message Payload) Digest Other =>
          bad r.2.other) ?_).trans ?_
      · intro result h
        simp only [Function.comp] at h
        cases hr : result.1 with
        | none => rw [hr] at h; simp [cutBad, terminalBad] at h
        | some input => rw [hr] at h; exact h
      · exact (GameEventBoundLen.verify_bound_len components bad size growth epsilon hb hmono L pk message signature world
          (by omega)).trans
          (add_le_add_right ((le_self_add).trans (GameEventBound.le_succ_mul fuel (epsilon L + epsilon L))) _)
    | sign message next =>
      refine (RandomOracleTrap.bind_map_indicator_le _ _ _
        (fun r : Signature Digest Body × World (HashInput PublicKey Message Payload) Digest Other => bad r.2.other)
        (fuel * (epsilon L + epsilon L)) fun result hresult => ih index pk sk (next result.1) result.2 _ ?_).trans ?_
      · have := GameEventBoundLen.sign_size components bad size growth epsilon hb sk message world result hresult
        omega
      · refine (add_le_add_left (GameEventBoundLen.sign_bound_len components bad size growth epsilon hb hmono L sk message
          world (by omega)) _).trans (le_of_eq ?_)
        rw [GameEventBound.succ_mul_eq]
        ring
    | hash input next =>
      cases index with
      | zero =>
        simp only [PMF.pure_map, PMF.pure_apply, cutBad]
        exact (RandomOracleTrap.ite_le_indicator _).trans le_self_add
      | succ index =>
        rw [PMF.map_bind]
        refine ChallengeMixtures.bind_true_le _ _ _ fun result _ => ?_
        refine (ih index pk sk (next result.1) _ _ (by show size world.other + _ ≤ L; omega)).trans ?_
        show indicator (bad world.other) + _ ≤ _
        exact add_le_add_right (mul_le_mul_left (Nat.cast_le.mpr (Nat.le_succ fuel)) _) _
    | query input next =>
      refine (RandomOracleTrap.bind_map_indicator_le _ _ _
        (fun r : Answer × World (HashInput PublicKey Message Payload) Digest Other => bad r.2.other)
        (fuel * (epsilon L + epsilon L)) fun result hresult => ih index pk sk (next result.1) result.2 _ ?_).trans ?_
      · have := GameEventBoundLen.oracle_size components bad size growth epsilon hb input world result hresult
        omega
      · refine (add_le_add_left (GameEventBoundLen.oracle_bound_len components bad size growth epsilon hb hmono L input
          world (by omega)) _).trans ?_
        calc indicator (bad world.other) + epsilon L + fuel * (epsilon L + epsilon L)
            ≤ indicator (bad world.other) + (epsilon L + epsilon L) + fuel * (epsilon L + epsilon L) := by
              gcongr
              exact le_self_add
          _ = indicator (bad world.other) + (fuel + 1 : ℕ) * (epsilon L + epsilon L) := by
              rw [GameEventBound.succ_mul_eq]
              ring

/-- Along the cut, a saved snapshot's size plus its remaining growth stays
below the level. -/
theorem cut_size (hb : ServiceBoundLen components bad size growth epsilon)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State) (L : Nat) :
    ∀ (index fuel : Nat) (pk : PublicKey) (sk : PublicKey × SecretKey) (state : State)
      (world : World (HashInput PublicKey Message Payload) Digest Other)
      (trace : Trace Message (HashInput PublicKey Message Payload) Query)
      (c : Spec.SignatureReplay.Cut PublicKey (PublicKey × SecretKey) Message (Signature Digest Body)
        (HashInput PublicKey Message Payload) Digest Other Query State),
      c ∈ (Spec.SignatureReplay.cut (scheme components) adversary index fuel pk sk state world trace).support →
      size world.other + fuel * (growth + growth) ≤ L →
      ∀ snapshot, c = .saved snapshot → size snapshot.world.other + snapshot.remaining * (growth + growth) ≤ L := by
  intro index fuel
  induction fuel generalizing index with
  | zero =>
    intro pk sk state world trace c hc _ snapshot hs
    simp only [Spec.SignatureReplay.cut, PMF.mem_support_pure_iff] at hc
    subst hc
    cases hs
  | succ fuel ih =>
    intro pk sk state world trace c hc hsize snapshot hs
    have hsucc : (fuel + 1) * (growth + growth) = fuel * (growth + growth) + (growth + growth) := Nat.succ_mul _ _
    rw [hsucc] at hsize
    simp only [Spec.SignatureReplay.cut] at hc
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
    cases action with
    | abort =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst hrest
      cases hs
    | finish message signature =>
      obtain ⟨result, _, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst hres
      cases hr : result.1 with
      | none => rw [hr] at hs; cases hs
      | some input => rw [hr] at hs; cases hs
    | sign message next =>
      obtain ⟨result, hresult, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      have := GameEventBoundLen.sign_size components bad size growth epsilon hb sk message world result hresult
      exact ih index pk sk _ _ _ c hrun (by omega) snapshot hs
    | hash input next =>
      cases index with
      | zero =>
        simp only [PMF.mem_support_pure_iff] at hrest
        subst hrest
        cases hs
        show size world.other + fuel * (growth + growth) ≤ L
        omega
      | succ index =>
        obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
        exact ih index pk sk _ _ _ c hrun (by show size world.other + _ ≤ L; omega) snapshot hs
    | query input next =>
      obtain ⟨result, hresult, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      have := GameEventBoundLen.oracle_size components bad size growth epsilon hb input world result hresult
      exact ih index pk sk _ _ _ c hrun (by omega) snapshot hs

end
end SDitH.Proofs.CutEventBound
