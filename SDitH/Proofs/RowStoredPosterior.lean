import SDitH.Proofs.RowStoredAfter
import SDitH.Proofs.TraceLength
import SDitH.Proofs.ChargeExpect

/-! The row-stored term's mean over the resampled family. The mean over the
resampled world of the row-stored term is the head's run under a family
drawn from the posterior of the world's cipher history; the run splits at
the last commitment call, the family is resampled at the split point, and
unless the last call is stale there the row-stored event has probability
at most the fiber bound times the fixed set's size over the remaining
block count. So the mean is at most the staleness term (the probability,
over the salt, the root and the run before the last call, that the last
call is stale in the split point's history) plus an explicit bound. -/

namespace SDitH.Proofs.RowStoredPosterior

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.RandomOracleTrace Spec.RandomOracleTrap
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches Candidates)
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.AbstractSignature
open Spec.PIOPArithmetic (selectorCount)
open IdealCipherFresh HeadCommitSplit RowsSupport RowStoredReduce RowStoredCount RowStoredAfter CommitLinesEvents
open OuterFresh PrefixLinesFresh CipherResample PosteriorFresh RunBind PrefixOrMention HeadLastRun InputPresentBound
open SharedGameInvariant TraceLength GameResample ChargeExpect RunHybrid
open scoped Classical ENNReal

noncomputable section

section Cipher

variable {Input Digest Key Block State : Type*} [Fintype Digest] [Nonempty Digest]

/-- A run's cipher history is matched by the family when the starting
history is. -/
theorem runFixed_cipher_matches (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (family : Family Key Block) (fuel : Nat) (state : State) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family fuel state table hashes ciphers log).support)
    (hm : Matches family ciphers) : Matches family out.cipherHistory := by
  induction fuel generalizing state table hashes ciphers log out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst hout
    exact hm
  | succ fuel ih =>
    simp only [runFixed] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst hrest
      exact hm
    | hash input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      exact ih _ _ _ _ _ inner hinner hm
    | cipher request next =>
      refine ih _ _ _ _ _ out hrest ?_
      exact (IdealCipher.matches_cons family ciphers request _).mpr ⟨hm, rfl⟩

/-- A run's cipher history grows by at most the fuel. -/
theorem runFixed_cipher_length_le (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (family : Family Key Block) (fuel : Nat) (state : State) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family fuel state table hashes ciphers log).support) :
    out.cipherHistory.length ≤ ciphers.length + fuel := by
  induction fuel generalizing state table hashes ciphers log out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst hout
    exact le_rfl
  | succ fuel ih =>
    simp only [runFixed] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst hrest
      exact Nat.le_add_right _ _
    | hash input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      exact (ih _ _ _ _ _ inner hinner).trans (by omega)
    | cipher request next =>
      have := ih _ _ _ _ _ out hrest
      simp only [List.length_cons] at this
      omega

variable [Fintype Key] [Fintype Block]

/-- A family in the posterior's support matches the history when some
family does. -/
theorem posterior_support_matches (history : List (Spec.IdealCipher.Entry Key Block))
    (hpos : ∃ family : Family Key Block, Matches family history) (family : Family Key Block)
    (hf : family ∈ (posterior history).support) : Matches family history := by
  unfold posterior at hf
  rw [dif_pos hpos, PMF.support_map] at hf
  obtain ⟨c, -, rfl⟩ := hf
  exact c.property

end Cipher

variable {lambda tau kappa s wit rnd : Nat}

/-- The staleness of the last call at a split point's result. -/
def staleOf {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (BeforeData lambda tau kappa))) : Bool :=
  match out.state with
  | .done v => stale htau S salt v out.cipherHistory
  | _ => true

/-- The row-stored event's mean is at most the indicator of the last call's
staleness plus the fixed-set bound. -/
theorem after_le {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (c : Nat)
    (hfiber : ∀ b, Fintype.card {r : Bits lambda // S.layout.output r = b} ≤ c) (q : Nat)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (BeforeData lambda tau kappa)))
    (v : BeforeData lambda tau kappa) (hstate : out.state = .done v) (htraced : Traced out.hashTable out.trace)
    (hpos : ∃ family : Family (Bits lambda) (Bits lambda), Matches family out.cipherHistory)
    (hlen : out.cipherHistory.length ≤ q) :
    ((posterior out.cipherHistory).bind fun family =>
        (continueRun family tau (headAfter htau S salt) out).map (rowStored htau)) true ≤
      indicator (staleOf htau S salt out) +
        ((c * (fixedSet v out.trace).card : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞) := by
  have hstale : staleOf htau S salt out = stale htau S salt v out.cipherHistory := by
    unfold staleOf
    rw [hstate]
  rw [hstale]
  cases hs : stale htau S salt v out.cipherHistory with
  | true =>
    rw [RandomOracleTrap.indicator_true]
    exact (PMF.coe_le_one _ _).trans le_self_add
  | false =>
    rw [RandomOracleTrap.indicator_false, zero_add]
    have hfresh : FreshInput (⟨out.cipherHistory, hpos⟩ : Spec.IdealCipher.World (Bits lambda) (Bits lambda))
        (lastKey (kappa := kappa) S.layout htau v.1)
        (S.layout.input (cipherInput S.variant salt (lastAddress (kappa := kappa) htau) true)) := by
      intro e he hk hi
      simp only [stale, decide_eq_false_iff_not, not_exists, not_and] at hs
      exact hs e he hk hi
    have hcont : ∀ family, (continueRun family tau (headAfter htau S salt) out).map (rowStored htau) =
        (runFixed procedure family tau (headAfter htau S salt v) out.hashTable out.hashHistory out.cipherHistory
          out.trace).map (rowStored htau) := by
      intro family
      unfold continueRun
      rw [hstate]
      rw [PMF.map_comp]
      rfl
    simp only [hcont]
    calc _ ≤ ((posterior out.cipherHistory).bind fun family => PMF.pure
            (decide (lastRowQuery htau v (lastBlock htau S salt v family) ∈ fixedSet v out.trace))) true :=
          bind_true_le_bind_true _ _ _ fun family _ => by
            refine (map_true_le_indicator _ _ _ fun o ho hrow =>
              rowStored_mem htau S salt v family _ _ _ _ htraced o ho hrow).trans (le_of_eq ?_)
            rw [PMF.pure_apply]
            by_cases hP : lastRowQuery htau v (lastBlock htau S salt v family) ∈ fixedSet v out.trace <;>
              simp [hP, indicator]
      _ ≤ _ := by
          show ((posterior out.cipherHistory).map fun family =>
            decide (lastRowQuery htau v (lastBlock htau S salt v family) ∈ fixedSet v out.trace)) true ≤ _
          exact posterior_row_le ⟨out.cipherHistory, hpos⟩ _ _ hfresh q hlen htau v S.layout.output c hfiber
            (fixedSet v out.trace)

variable {higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The staleness term of a world: over the salt, the root and the run
before the last call under the posterior family, the probability that the
last call is stale in the split point's history. -/
def staleTerm (htau : tau ≠ 0)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : ℝ≥0∞ :=
  ((PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
    (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
      (posterior world.other.cipherHistory).bind fun family =>
        (runFixed procedure family (beforeBudget tau kappa) (headBefore htau S.signer salt root) world.other.hashTable
          world.other.hashHistory world.other.cipherHistory world.other.trace).map (staleOf htau S.signer salt)) true

theorem mean_eq_bind {A B : Type*} (p : PMF A) (q : A → PMF B) (b : B) :
    mean p (fun a => (q a) b) = (p.bind q) b := by
  unfold mean
  rw [PMF.bind_apply]

/-- The row-stored term's mean over the resampled family is at most the
staleness term plus the explicit bound. -/
theorem rowTerm_mean_le (htau : tau ≠ 0)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (hpos : ∃ family : Family (Bits lambda) (Bits lambda), Matches family world.other.cipherHistory)
    (hwf : WellFormed world.other) (L : Nat) (hT : world.other.trace.length ≤ L) (h₀ : Nat)
    (hH : world.other.cipherHistory.length ≤ h₀) (c : Nat)
    (hfiber : ∀ b, Fintype.card {r : Bits lambda // S.signer.layout.output r = b} ≤ c) (q : Nat)
    (hq : h₀ + beforeBudget tau kappa ≤ q) :
    mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤
      staleTerm S htau world +
        ((c * (L + beforeBudget tau kappa + tau) : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞) := by
  set K : ℝ≥0∞ :=
    ((c * (L + beforeBudget tau kappa + tau) : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞) with hK
  simp only [resampleW, resample, mean_map]
  unfold rowTerm staleTerm
  rw [mean_eq_bind, PMF.bind_comm]
  conv_lhs => enter [1, 2, salt]; rw [PMF.bind_comm]
  refine bind_le_bind_add_const' _ _ _ _ true fun salt _ => ?_
  refine bind_le_bind_add_const' _ _ _ _ true fun root _ => ?_
  simp only [runFixed_headInit_split htau, PMF.map_bind]
  have hres := runFixed_resample procedure (beforeBudget tau kappa) (headBefore htau S.signer salt root)
    world.other.hashTable world.other.hashHistory
    (⟨world.other.cipherHistory, hpos⟩ : Spec.IdealCipher.World (Bits lambda) (Bits lambda)) world.other.trace
    (fun out family => (continueRun family tau (headAfter htau S.signer salt) out).map (rowStored htau))
  dsimp only at hres
  rw [hres]
  refine bind_le_bind_add_const' _ _ _ _ true fun family hf => ?_
  have hmatch : Matches family world.other.cipherHistory := posterior_support_matches _ hpos family hf
  refine InputPresentTail.bind_true_le_event_add _ _ (staleOf htau S.signer salt) K fun out hout hstale => ?_
  obtain ⟨v, hv⟩ := runFixed_bounded_done family _ _ (headBefore_bounded htau S.signer salt root) _ _ _ _ out hout
  have hinv := HashCipherTrace.run_invariants procedure family _ _ _ _ _ _ out hout hwf.1 hwf.2.1 hwf.2.2.1 hwf.2.2.2.1 hwf.2.2.2.2
  have hpos' : ∃ family : Family (Bits lambda) (Bits lambda), Matches family out.cipherHistory :=
    ⟨family, runFixed_cipher_matches procedure family _ _ _ _ _ _ out hout hmatch⟩
  have hlen : out.cipherHistory.length ≤ q :=
    (runFixed_cipher_length_le procedure family _ _ _ _ _ _ out hout).trans (by omega)
  refine (after_le htau S.signer salt c hfiber q out v hv hinv.1 hpos' hlen).trans ?_
  rw [hstale, RandomOracleTrap.indicator_false, zero_add, hK]
  refine ENNReal.div_le_div_right ((Nat.cast_le (α := ℝ≥0∞)).mpr (Nat.mul_le_mul_left c ?_)) _
  refine (fixedSet_card_le v out.trace).trans ?_
  have := runFixed_trace_length_le procedure family _ _ _ _ _ _ out hout
  omega

end
end SDitH.Proofs.RowStoredPosterior
