import SDitH.Proofs.TraceGrowth
import SDitH.Proofs.RowStoredPosterior
import SDitH.Proofs.SimulationGapMean

/-! The cipher-history invariant. A shared world is cipher-consistent when
its family matches its cipher history; a program run keeps the family
and extends the history by entries the family answers, so consistency is
kept and the history grows by at most the budget. The honest and
simulated signings add at most the commitment budget of cipher entries
and the public oracle at most one, all keeping consistency; key
generation starts with the empty history. The extended counted invariant
adds consistency and a cipher-history budget to the counted invariant,
and is kept by every step and by resampling. -/

namespace SDitH.Proofs.CipherInvariant

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.HashCipherTrace
open Spec.IdealCipher (Family Matches)
open Spec.PIOPArithmetic (selectorCount)
open SignStep TraceLength TraceGrowth SimulationGapInv SimulationGapGen SimulationGapTrace SimulationGapMean
open RowStoredPosterior GameResample CipherResample
open scoped Classical

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- A shared world is cipher-consistent when its family matches its history. -/
def Consistent (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) : Prop :=
  Matches world.family world.cipherHistory

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A program run keeps consistency and grows the history by at most the
budget. -/
theorem runProgram_cipher {A : Type*} (budget : Nat)
    (program : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w)
      (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda) A)
    (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (result)
    (hr : result ∈ (runProgram budget program world).support) (hc : Consistent world) :
    Consistent result.2 ∧ result.2.cipherHistory.length ≤ world.cipherHistory.length + budget := by
  obtain ⟨out, hout, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  exact ⟨runFixed_cipher_matches procedure world.family budget program world.hashTable world.hashHistory
      world.cipherHistory world.trace out hout hc,
    runFixed_cipher_length_le procedure world.family budget program world.hashTable world.hashHistory
      world.cipherHistory world.trace out hout⟩

/-- The honest signing keeps consistency and adds at most the commitment
budget of cipher entries. -/
theorem honest_sign_cipher (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (r)
    (hr : r ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message
      world).support) (hc : Consistent world.other) :
    Consistent r.2.other ∧ r.2.other.cipherHistory.length ≤ world.other.cipherHistory.length + commitBudget tau kappa := by
  rcases sk with ⟨pk', witness⟩
  rw [honest_sign_eq'] at hr
  obtain ⟨salt, _, h1⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨root, _, h2⟩ := (PMF.mem_support_bind_iff _ _ _).mp h1
  obtain ⟨res, hres, h3⟩ := (PMF.mem_support_bind_iff _ _ _).mp h2
  obtain ⟨hashResult, _, h4⟩ := (PMF.mem_support_bind_iff _ _ _).mp h3
  obtain ⟨opened, hop, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp h4
  subst heq
  simp only [Spec.CandidateScheme.openSigning, PMF.mem_support_pure_iff] at hop
  subst hop
  have hpre : (preparedOf S salt res).2.2 = res.2 := by
    unfold preparedOf
    cases res.1 <;> rfl
  dsimp only
  rw [hpre]
  exact runProgram_cipher _ _ world.other res hres hc

/-- The simulated signing keeps consistency and adds at most the commitment
budget of cipher entries. -/
theorem simulatedSign_cipher (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (r) (hr : r ∈ (simulatedSign S publicKey message world).support) (hc : Consistent world.other) :
    Consistent r.2.other ∧ r.2.other.cipherHistory.length ≤ world.other.cipherHistory.length + commitBudget tau kappa := by
  obtain ⟨salt, _, hsalt⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨root, _, hroot⟩ := (PMF.mem_support_bind_iff _ _ _).mp hsalt
  obtain ⟨fake, _, hfake⟩ := (PMF.mem_support_bind_iff _ _ _).mp hroot
  obtain ⟨digest, _, hdigest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfake
  obtain ⟨run, hrun, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hdigest
  have hlen := runProgram_cipher _ _ world.other run hrun hc
  rw [← hres]
  dsimp only
  split <;> (try split) <;> (try split) <;> exact hlen

/-- The public oracle keeps consistency and adds at most one cipher entry. -/
theorem publicOracle_cipher (query : Query lambda)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (r) (hr : r ∈ ((simulatedScheme S V verifyBudget publicKey sampleWitness).publicOracle query world).support)
    (hc : Consistent world.other) :
    Consistent r.2.other ∧ r.2.other.cipherHistory.length ≤ world.other.cipherHistory.length + 1 := by
  obtain ⟨result, hresult, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  dsimp only
  cases query with
  | hash input =>
    obtain ⟨run, hrun, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    exact runProgram_cipher 1 _ world.other run hrun hc
  | mask input =>
    obtain ⟨run, hrun, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    exact runProgram_cipher 1 _ world.other run hrun hc
  | cipher request =>
    obtain ⟨run, hrun, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    exact runProgram_cipher 1 _ world.other run hrun hc

/-- The extended counted invariant: the counted invariant, consistency, and
the cipher-history budget. -/
def InvC (n : Nat)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : Prop :=
  InvT tau kappa n world ∧ Consistent world.other ∧ world.other.cipherHistory.length ≤ commitBudget tau kappa * n

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem invC_mono (n m : Nat) (world) (hnm : n ≤ m)
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world) : InvC (tau := tau) (kappa := kappa) m world :=
  ⟨invT_mono n m world hnm h.1, h.2.1, h.2.2.trans (Nat.mul_le_mul_left _ hnm)⟩

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem invC_query (world) (input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (n : Nat)
    (r : Spec.BAVC.Digest lambda × (HashInput (List Bool) (List Bool) (Payload F lambda higherCount) →
      Option (Spec.BAVC.Digest lambda)))
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world)
    (hr : r ∈ (Spec.RandomOracle.query world.hashTable input).support) :
    InvC (tau := tau) (kappa := kappa) (n + 1) { world with hashTable := r.2 } :=
  ⟨invT_query world input n r h.1 hr, h.2.1, h.2.2.trans (Nat.mul_le_mul_left _ (Nat.le_succ n))⟩

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem invC_update (world) (input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (n : Nat)
    (d : Spec.BAVC.Digest lambda)
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world) :
    InvC (tau := tau) (kappa := kappa) (n + 1) { world with hashTable := Function.update world.hashTable input (some d) } :=
  ⟨invT_update world input n d h.1, h.2.1, h.2.2.trans (Nat.mul_le_mul_left _ (Nat.le_succ n))⟩

theorem invC_pub (query : Query lambda) (world) (n : Nat) (r)
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world)
    (hr : r ∈ ((simulatedScheme S V verifyBudget publicKey sampleWitness).publicOracle query world).support) :
    InvC (tau := tau) (kappa := kappa) (n + 1) r.2 := by
  obtain ⟨hc, hlen⟩ := publicOracle_cipher S V verifyBudget publicKey sampleWitness query world r hr h.2.1
  refine ⟨invT_pub S V verifyBudget publicKey sampleWitness query world n r h.1 hr, hc, ?_⟩
  have h2 := one_le_commitBudget (tau := tau) (kappa := kappa)
  have h3 := h.2.2
  calc r.2.other.cipherHistory.length ≤ world.other.cipherHistory.length + 1 := hlen
    _ ≤ commitBudget tau kappa * n + commitBudget tau kappa := by omega
    _ = commitBudget tau kappa * (n + 1) := by ring

theorem invC_honest (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) (world) (n : Nat) (r)
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world)
    (hr : r ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message
      world).support) : InvC (tau := tau) (kappa := kappa) (n + 1) r.2 := by
  obtain ⟨hc, hlen⟩ := honest_sign_cipher S V verifyBudget publicKey sampleWitness sk message world r hr h.2.1
  refine ⟨invT_honest S V verifyBudget publicKey sampleWitness sk message world n r h.1 hr, hc, ?_⟩
  have h3 := h.2.2
  calc r.2.other.cipherHistory.length ≤ world.other.cipherHistory.length + commitBudget tau kappa := hlen
    _ ≤ commitBudget tau kappa * n + commitBudget tau kappa := by omega
    _ = commitBudget tau kappa * (n + 1) := by ring

theorem invC_simulated (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) (world) (n : Nat) (r)
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world)
    (hr : r ∈ ((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message world).support) :
    InvC (tau := tau) (kappa := kappa) (n + 1) r.2 := by
  obtain ⟨hc, hlen⟩ := simulatedSign_cipher S sk.1 message world r hr h.2.1
  refine ⟨invT_simulated S V verifyBudget publicKey sampleWitness sk message world n r h.1 hr, hc, ?_⟩
  have h3 := h.2.2
  calc r.2.other.cipherHistory.length ≤ world.other.cipherHistory.length + commitBudget tau kappa := hlen
    _ ≤ commitBudget tau kappa * n + commitBudget tau kappa := by omega
    _ = commitBudget tau kappa * (n + 1) := by ring

/-- The generated keys satisfy the extended invariant at zero. -/
theorem invC_keygen :
    ∀ generated ∈ (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).keygen.support,
      InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
        (kappa := kappa) 0 generated.2.2 := by
  intro generated hg
  refine ⟨invT_keygen S V verifyBudget publicKey sampleWitness generated hg, ?_, ?_⟩
  · obtain ⟨g, hg', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hg
    obtain ⟨witness, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hg'
    obtain ⟨family, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
    intro e he
    exact absurd he (List.not_mem_nil)
  · obtain ⟨g, hg', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hg
    obtain ⟨witness, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hg'
    obtain ⟨family, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
    simp

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- Resampling keeps the extended invariant: the resampled family matches
the history, which is unchanged. -/
theorem invC_resample (n : Nat) (world)
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world) :
    ∀ w' ∈ (resampleW resample world).support, InvC (tau := tau) (kappa := kappa) n w' := by
  intro w' hw
  refine ⟨invT_resample n world h.1 w' hw, ?_, ?_⟩
  · unfold resampleW at hw
    rw [PMF.support_map] at hw
    obtain ⟨o, ho, rfl⟩ := hw
    unfold resample at ho
    rw [PMF.support_map] at ho
    obtain ⟨f, hf, rfl⟩ := ho
    exact posterior_support_matches _ ⟨world.other.family, h.2.1⟩ f hf
  · unfold resampleW at hw
    rw [PMF.support_map] at hw
    obtain ⟨o, ho, rfl⟩ := hw
    unfold resample at ho
    rw [PMF.support_map] at ho
    obtain ⟨f, -, rfl⟩ := ho
    exact h.2.2

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The extended invariant yields the named cipher-history hypothesis. -/
theorem invC_game (n : Nat) (world)
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world) :
    (∃ family : Family (Bits lambda) (Bits lambda), Matches family world.other.cipherHistory) ∧
      world.other.cipherHistory.length ≤ commitBudget tau kappa * n :=
  ⟨⟨world.other.family, h.2.1⟩, h.2.2⟩

end
end SDitH.Proofs.CipherInvariant
