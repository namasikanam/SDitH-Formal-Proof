import SDitH.Proofs.PruneLawRun
import SDitH.Proofs.RunHistoryShift
import SDitH.Proofs.RunWorld

/-! The cipher history is only a log. Appending entries to a game world's
inner cipher history changes nothing in the oracles' answers: a
program-shaped oracle from the extended world is the oracle from the world
with the entries appended to its output's history, and so is the game run
with its final world, with an attempt's embedded world shifted alike. This
lets a branch of the fork start from another branch's final world with the
snapshot's tables: only its history's suffix differs. -/

namespace SDitH.Proofs.HistoryShiftGame

open Spec.SignatureSecurity Spec.IdealCipher Spec.HashCipherTrace
open Spec.DomainSeparation (Bits)
open GameResample ChargeExpect RunWorld GamePrune PruneLawRun RunHistoryShift
open scoped Classical

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}

/-- The game world with entries appended to its inner cipher history. -/
def shiftG (H : List (Entry (Bits lambda) (Bits lambda))) (w : GW HashInput Digest lambda s wit rnd) :
    GW HashInput Digest lambda s wit rnd :=
  { w with other := { w.other with cipherHistory := w.other.cipherHistory ++ H } }

/-- An oracle obeys the shift law: from the extended world it is the oracle
with the entries appended to its output's history. -/
def ShiftLaw {A : Type*} (O : GW HashInput Digest lambda s wit rnd → PMF (A × GW HashInput Digest lambda s wit rnd)) : Prop :=
  ∀ (H : List (Entry (Bits lambda) (Bits lambda))) (w : GW HashInput Digest lambda s wit rnd),
    O (shiftG H w) = (O w).map fun r => (r.1, shiftG H r.2)

omit [Fintype Digest] [Nonempty Digest] in
/-- A program-shaped oracle obeys the shift law. -/
theorem shiftLaw_run {A S : Type*} (budget : Nat)
    (program : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A)
    (post : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A → (HashInput → Option Digest) → PMF (S × (HashInput → Option Digest))) :
    ShiftLaw (runOracle (HashInput := HashInput) (Digest := Digest) budget program post) := by
  intro H w
  have h1 := runFixed_history_shift w.other.family budget program w.other.hashTable
    w.other.hashHistory (w.other.cipherHistory ++ H) w.other.trace
  have h2 := runFixed_history_shift w.other.family budget program w.other.hashTable
    w.other.hashHistory w.other.cipherHistory w.other.trace
  simp only [runOracle, Spec.SharedScheme.runProgram, shiftG]
  rw [h1, h2]
  simp only [PMF.map_comp, PMF.bind_map, PMF.map_bind, Function.comp_def]
  congr 1
  funext out
  simp only [appendHistory, List.append_assoc]

omit [Fintype Digest] [Nonempty Digest] in
/-- Sampling before an oracle preserves the shift law. -/
theorem shiftLaw_sample {X S : Type*} (sample : PMF X)
    (body : X → GW HashInput Digest lambda s wit rnd → PMF (S × GW HashInput Digest lambda s wit rnd))
    (h : ∀ x, ShiftLaw (body x)) : ShiftLaw fun w => sample.bind fun x => body x w := by
  intro H w
  simp only [PMF.map_bind]
  refine congrArg _ (funext fun x => ?_)
  exact h x H w

omit [Fintype Digest] [Nonempty Digest] in
/-- A pure answer obeys the shift law. -/
theorem shiftLaw_pure {S : Type*} (a : S) :
    ShiftLaw fun w : GW HashInput Digest lambda s wit rnd => PMF.pure (a, w) := by
  intro H w
  simp only [PMF.pure_map]

/-- A terminal with an attempt's embedded world shifted. -/
def shiftT (H : List (Entry (Bits lambda) (Bits lambda)))
    (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) :
    Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query :=
  match t with
  | .attempt a => .attempt { a with world := shiftG H a.world }
  | t => t

/-- The game run with its final world from the extended world is the run
with the entries appended to its final history and to an attempt's
embedded history. -/
theorem runW_shift
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsign : ∀ sk m, ShiftLaw (scheme.sign sk m)) (hpub : ∀ q, ShiftLaw (scheme.publicOracle q))
    (hprep : ∀ pk m sig, ShiftLaw (scheme.prepareVerification pk m sig)) :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (H : List (Entry (Bits lambda) (Bits lambda)))
      (w : GW HashInput Digest lambda s wit rnd) (trace : Trace Message HashInput Query),
      runW scheme adversary fuel pk sk state (shiftG H w) trace =
        (runW scheme adversary fuel pk sk state w trace).map fun r => (shiftT H r.1, shiftG H r.2) := by
  intro fuel
  induction fuel with
  | zero =>
    intros
    simp only [runW, PMF.pure_map]
    rfl
  | succ fuel ih =>
    intro pk sk state H w trace
    simp only [runW, PMF.map_bind]
    congr 1
    funext action
    cases action with
    | abort =>
      simp only [PMF.pure_map]
      rfl
    | finish message signature =>
      dsimp only
      rw [hprep pk message signature H w, PMF.map_comp, PMF.map_comp]
      congr 1
      funext result
      rcases result with ⟨a, o⟩
      cases a <;> rfl
    | sign message next =>
      dsimp only
      rw [hsign sk message H w, PMF.bind_map, PMF.map_bind]
      simp only [Function.comp_def]
      congr 1
      funext r
      exact ih pk sk (next r.1) H r.2 _
    | hash input next =>
      dsimp only
      rw [PMF.map_bind]
      congr 1
      funext r
      exact ih pk sk (next r.1) H { w with hashTable := r.2 } _
    | query input next =>
      dsimp only
      rw [hpub input H w, PMF.bind_map, PMF.map_bind]
      simp only [Function.comp_def]
      congr 1
      funext r
      exact ih pk sk (next r.1) H r.2 _

end
end SDitH.Proofs.HistoryShiftGame
