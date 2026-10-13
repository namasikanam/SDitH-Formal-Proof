import SDitH.Proofs.HistoryShiftGame
import SDitH.Proofs.GamePrune
import SDitH.Proofs.ForkOutcome
import SDitH.Spec.SignatureReplay

/-! The restored fork. The fork's two branches start from the same saved
world and so share its cipher family; a signing call's continuation in the
first branch is then not a fixed function of the call's output. The
restored fork runs the first branch with its final world, resamples the
family given the first branch's final history, and runs the second branch
from the snapshot's tables with that family and history; every
continuation is then a game run. This module names the restored fork and
proves that the game's oracles keep the family along a run. -/

namespace SDitH.Proofs.ForkRestore

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher
open Spec.DomainSeparation (Bits)
open GameResample ChargeExpect RunWorld GamePrune PruneLawRun HistoryShiftGame CipherResample ForkOutcome
open scoped Classical

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}

/-- An oracle keeps the family. -/
def KeepsFamily {A : Type*} (O : GW HashInput Digest lambda s wit rnd → PMF (A × GW HashInput Digest lambda s wit rnd)) : Prop :=
  ∀ (w : GW HashInput Digest lambda s wit rnd) (r : A × GW HashInput Digest lambda s wit rnd), r ∈ (O w).support →
    r.2.other.family = w.other.family

omit [Fintype Digest] [Nonempty Digest] in
/-- A program-shaped oracle keeps the family. -/
theorem keepsFamily_run {A S : Type*} (budget : Nat)
    (program : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A)
    (post : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A → (HashInput → Option Digest) → PMF (S × (HashInput → Option Digest))) :
    KeepsFamily (runOracle (HashInput := HashInput) (Digest := Digest) budget program post) := by
  intro w r hr
  simp only [runOracle, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hr
  obtain ⟨p, hp, q, -, rfl⟩ := hr
  exact runProgram_family _ _ _ p hp

omit [Fintype Digest] [Nonempty Digest] in
/-- Sampling before an oracle preserves family keeping. -/
theorem keepsFamily_sample {X S : Type*} (sample : PMF X)
    (body : X → GW HashInput Digest lambda s wit rnd → PMF (S × GW HashInput Digest lambda s wit rnd))
    (h : ∀ x, KeepsFamily (body x)) : KeepsFamily fun w => sample.bind fun x => body x w := by
  intro w r hr
  obtain ⟨x, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  exact h x w r hr

omit [Fintype Digest] [Nonempty Digest] in
/-- A pure answer keeps the family. -/
theorem keepsFamily_pure {S : Type*} (a : S) :
    KeepsFamily fun w : GW HashInput Digest lambda s wit rnd => PMF.pure (a, w) := by
  intro w r hr
  simp only [PMF.mem_support_pure_iff] at hr
  subst hr
  rfl

/-- The game run keeps the family. -/
theorem runW_family
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsign : ∀ sk m, KeepsFamily (scheme.sign sk m)) (hpub : ∀ q, KeepsFamily (scheme.publicOracle q))
    (hprep : ∀ pk m sig, KeepsFamily (scheme.prepareVerification pk m sig)) :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (w : GW HashInput Digest lambda s wit rnd)
      (trace : Trace Message HashInput Query), ∀ r ∈ (runW scheme adversary fuel pk sk state w trace).support,
      r.2.other.family = w.other.family := by
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
      obtain ⟨result, hres, rfl⟩ := hr
      exact hprep pk message signature w result hres
    | sign message next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres, hr⟩ := hr
      rw [ih pk sk _ _ _ r hr]
      exact hsign sk message w result hres
    | hash input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, -, hr⟩ := hr
      exact ih pk sk _ { w with hashTable := result.2 } _ r hr
    | query input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres, hr⟩ := hr
      rw [ih pk sk _ _ _ r hr]
      exact hpub input w result hres

variable (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)

/-- The fresh branch with its final world. -/
def freshBranchW (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query State) :
    PMF (Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd) :=
  (PMF.uniformOfFintype Digest).bind fun answer =>
    (runW scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer)
      { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) }
      { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }).bind fun r =>
      (finalize r.1).map fun checked => (⟨answer, checked⟩, r.2)

/-- The fresh branch is the first component of the fresh branch with its
final world. -/
theorem freshBranchW_fst (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest
    (Spec.SharedScheme.World lambda s wit rnd) Query State) :
    (freshBranchW scheme adversary snapshot).map Prod.fst = freshBranch scheme adversary snapshot := by
  unfold freshBranchW freshBranch continueWith
  rw [PMF.map_bind]
  refine congrArg _ (funext fun answer => ?_)
  rw [run_eq_runW, PMF.bind_map, PMF.map_bind, PMF.map_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [PMF.map_comp]
  rfl

/-- The snapshot's world with the family and history of a final world. -/
def restore (base final : GW HashInput Digest lambda s wit rnd) : GW HashInput Digest lambda s wit rnd :=
  { base with other := { base.other with family := final.other.family, cipherHistory := final.other.cipherHistory } }

/-- The restored fork: the first branch with its final world, the family
resampled given its final history, and the second branch from the
snapshot's tables with that family and history. -/
def forkAtR (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query State) :
    PMF (Option (Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)) :=
  match snapshot.world.hashTable snapshot.input with
  | some _ => PMF.pure none
  | none => (freshBranchW scheme adversary snapshot).bind fun left =>
      (resampleW resample (restore snapshot.world left.2)).bind fun w' =>
        (freshBranch scheme adversary { snapshot with world := w' }).map fun right => some (left.1, right)

end
end SDitH.Proofs.ForkRestore
