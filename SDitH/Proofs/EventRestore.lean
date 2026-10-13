import SDitH.Proofs.ForkRestoreEnd
import SDitH.Proofs.EventHybrid

/-! The event experiment with the end-resampled restored fork. From a
resampled key, the cut's saved world is resampled by the cut's resampling
law, the shared fork agrees with the restored one from a resampled
snapshot, and the restored fork agrees with the end-resampled one; so the
event experiment equals the experiment whose fork is end-resampled and
restored, for events insensitive to the second branch's history suffix
and to the attempts' embedded families. -/

namespace SDitH.Proofs.EventRestore

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher
open Spec.DomainSeparation (Bits)
open Spec.RandomOracleTrap (indicator)
open GameResample ChargeExpect RunWorld GamePrune PruneLawRun HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open ForkRestoreShift ForkRestoreEq ForkRestoreEnd SharedResample SignBridge HiddenSlice MeanHybrid ChargeCutExpect EventHybrid
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}
  (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (E : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State →
    Option (Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) → Bool)

/-- The event experiment with the end-resampled restored fork. -/
def eventExpE (index fuel : Nat) : PMF Bool :=
  (cutExperiment scheme adversary index fuel).bind fun c => match c with
    | .ended _ => PMF.pure false
    | .saved snapshot => forkEventE scheme adversary E snapshot

omit [Fintype Digest] [Nonempty Digest] in
/-- A distribution on booleans is determined by its probability of true. -/
theorem pmf_bool_ext (p q : PMF Bool) (h : p true = q true) : p = q := by
  ext b
  cases b
  · have hp := PMF.tsum_coe p
    have hq := PMF.tsum_coe q
    rw [tsum_bool] at hp hq
    rw [h] at hp
    exact (ENNReal.add_left_inj (PMF.apply_ne_top q true)).mp (hp.trans hq.symm)
  · exact h

/-- The event experiment equals its end-resampled restored form. -/
theorem eventExp_eq_E
    (hkeygen : scheme.keygen = scheme.keygen.bind fun g => (resampleW resample g.2.2).map fun w => (g.1, g.2.1, w))
    (hsignLaw : ∀ sk m, PostLaw resample (scheme.sign sk m))
    (hpubLaw : ∀ q, PostLaw resample (scheme.publicOracle q))
    (hprepLaw : ∀ pk m sig, PostLaw resample (scheme.prepareVerification pk m sig))
    (hsignF : ∀ sk m, KeepsFamily (scheme.sign sk m)) (hpubF : ∀ q, KeepsFamily (scheme.publicOracle q))
    (hprepF : ∀ pk m sig, KeepsFamily (scheme.prepareVerification pk m sig))
    (hsignG : ∀ sk m, Grows (scheme.sign sk m)) (hpubG : ∀ q, Grows (scheme.publicOracle q))
    (hprepG : ∀ pk m sig, Grows (scheme.prepareVerification pk m sig))
    (hsignS : ∀ sk m, ShiftLaw (scheme.sign sk m)) (hpubS : ∀ q, ShiftLaw (scheme.publicOracle q))
    (hprepS : ∀ pk m sig, ShiftLaw (scheme.prepareVerification pk m sig))
    (hE : ∀ snapshot' left right H, E snapshot' (some (left, shiftBranch H right)) = E snapshot' (some (left, right)))
    (hEleft : ∀ snapshot' left right g, E snapshot' (some (setFamilyBranch g left, right)) = E snapshot' (some (left, right)))
    (hEright : ∀ snapshot' left right g, E snapshot' (some (left, setFamilyBranch g right)) = E snapshot' (some (left, right)))
    (index fuel : Nat) :
    (eventExp scheme adversary E index fuel) true = (eventExpE scheme adversary E index fuel) true := by
  unfold eventExp eventExpE cutExperiment
  rw [hkeygen]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine congrArg (fun p : PMF Bool => p true) ?_
  refine congrArg _ (funext fun g => ?_)
  dsimp only
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  refine congrArg _ (funext fun state => ?_)
  rw [← PMF.bind_bind, cut_postLaw resample resample_idem scheme adversary hsignLaw hpubLaw, PMF.bind_bind]
  conv_rhs => rw [← PMF.bind_bind, cut_postLaw resample resample_idem scheme adversary hsignLaw hpubLaw, PMF.bind_bind]
  refine congrArg _ (funext fun w => ?_)
  simp only [PMF.bind_bind]
  refine congrArg _ (funext fun c => ?_)
  cases c with
  | ended t => simp only [resampleCut, PMF.pure_bind]
  | saved snapshot =>
    apply pmf_bool_ext
    simp only [resampleCut, mean_bind_apply, mean_map]
    rw [fork_restore_eq scheme adversary E hsignLaw hpubLaw hprepLaw hsignF hpubF hprepF hsignG hpubG hprepG hsignS hpubS hprepS
      hE snapshot]
    refine congrArg _ (funext fun w' => ?_)
    exact forkEventR_eq_E scheme adversary E hsignLaw hpubLaw hprepLaw hsignF hpubF hprepF hEleft hEright _

end
end SDitH.Proofs.EventRestore
