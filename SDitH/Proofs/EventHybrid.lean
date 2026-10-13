import SDitH.Proofs.CutHybrid
import SDitH.Proofs.ForkEventUnion

/-! The hybrid over the event experiment. The event experiment of a scheme
cuts the game at a hash request, forks at a saved snapshot and evaluates
an event on the fork's result. A saved snapshot carries the cut's secret
key and at most the cut's fuel. So for two schemes agreeing off signing,
with a per-call bound for good keys, the event experiments are within
three times the fuel times the bound (once for the cut, twice for the
fork's two branches). -/

namespace SDitH.Proofs.EventHybrid

open Spec.SignatureSecurity Spec.SignatureReplay
open RunHybrid CutHybrid
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- A saved snapshot of the cut carries the cut's secret key. -/
theorem cut_saved_secretKey (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    ∀ (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : World HashInput Digest Other)
      (trace : Trace Message HashInput Query) (c : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State),
      c ∈ (cut scheme adversary index fuel pk sk state world trace).support →
      ∀ snapshot, c = .saved snapshot → snapshot.secretKey = sk := by
  intro index fuel
  induction fuel generalizing index with
  | zero =>
    intro pk sk state world trace c hc snapshot hs
    simp only [cut, PMF.mem_support_pure_iff] at hc
    subst hc
    cases hs
  | succ fuel ih =>
    intro pk sk state world trace c hc snapshot hs
    simp only [cut] at hc
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
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact ih index pk sk _ _ _ c hrun snapshot hs
    | hash input next =>
      cases index with
      | zero =>
        simp only [PMF.mem_support_pure_iff] at hrest
        subst hrest
        cases hs
        rfl
      | succ index =>
        obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
        exact ih index pk sk _ _ _ c hrun snapshot hs
    | query input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact ih index pk sk _ _ _ c hrun snapshot hs

/-- The event experiment of a scheme: cut, then fork at a saved snapshot and
evaluate the event on the fork's result. -/
def eventExp (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (E : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State →
      Option (Branch Message Signature HashInput Digest Other Query × Branch Message Signature HashInput Digest Other Query) →
      Bool)
    (index fuel : Nat) : PMF Bool :=
  (cutExperiment scheme adversary index fuel).bind fun c => match c with
    | .ended _ => PMF.pure false
    | .saved snapshot => (forkAt scheme adversary snapshot).map (E snapshot)

variable (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (eps : ℝ≥0∞)
  (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other)
    (h : Signature × World HashInput Digest Other → PMF Bool) (c : Bool),
    ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps)

include hagree hsign in
/-- The event-experiment hybrid: within three times the fuel times the
bound, for good generated keys. -/
theorem eventExp_le (hgood : ∀ generated ∈ sch₁.keygen.support, Good generated.2.1)
    (E : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State →
      Option (Branch Message Signature HashInput Digest Other Query × Branch Message Signature HashInput Digest Other Query) →
      Bool)
    (index fuel : Nat) :
    (eventExp sch₁ adversary E index fuel) true ≤
      (eventExp sch₂ adversary E index fuel) true + (fuel * eps + 2 * fuel * eps) := by
  unfold eventExp
  refine (cutExperiment_le sch₁ sch₂ adversary hagree Good eps hsign hgood index fuel _ true).trans ?_
  rw [add_comm (fuel * eps) (2 * fuel * eps), ← add_assoc]
  refine add_le_add_left ?_ _
  refine bind_le_bind_add_const' _ _ _ _ true (fun c hc => ?_)
  cases c with
  | ended t =>
    dsimp only
    exact le_self_add
  | saved snapshot =>
    dsimp only
    obtain ⟨generated, hg, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
    obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
    have hrem : snapshot.remaining ≤ fuel :=
      ForkEventUnion.cut_remaining_le sch₂ adversary index fuel _ _ state _ _ _ hcut snapshot rfl
    have hkey : snapshot.secretKey = generated.2.1 :=
      cut_saved_secretKey sch₂ adversary index fuel _ _ state _ _ _ hcut snapshot rfl
    have hsk : Good snapshot.secretKey := by
      rw [hkey]
      exact hgood generated (by rw [hagree.keygen]; exact hg)
    rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
    refine (forkAt_le sch₁ sch₂ adversary hagree Good eps hsign snapshot hsk _ true).trans ?_
    exact add_le_add_right (mul_le_mul' (mul_le_mul' le_rfl (Nat.cast_le.mpr hrem)) le_rfl) _

end
end SDitH.Proofs.EventHybrid
