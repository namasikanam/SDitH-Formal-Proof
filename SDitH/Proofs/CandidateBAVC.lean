import SDitH.Spec.CandidateBAVC
import SDitH.Proofs.SharedSigner

/-! Evaluation of the candidate reconstruction. A successful evaluation
returns the salted outer digest stored for the recomputed commitments and
the opening's revealed seeds; every revealed seed is present off the hidden
index, its commitment is CommitSeed through the family with both cipher
calls recorded, the hidden commitments are the transmitted ones, and every
row and the outer query is stored. On the candidate opening of an honest
key the recomputed commitments are the key's. The program is bounded. -/

namespace SDitH.Proofs.CandidateBAVC

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.HashCipherEvaluation Spec.SeedPrimitives
open Spec.SharedSigner Spec.CandidateBAVC
open Spec.SlopeConsistencyGame (Out)
open SharedSigner (digestAt expandEntries)
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}
variable (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
  (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))

/-- The value of one leaf's commitment program. -/
def leafValue (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Opening lambda tau (2 ^ kappa))
    (pair : Fin tau × Fin (2 ^ kappa)) : Option (Digest lambda) :=
  if pair.2 = hidden pair.1 then some (opening.hiddenCommitments pair.1)
  else (opening.revealed pair.1 pair.2).map fun seed =>
    commitSeed (tau * 2 ^ kappa) variant (Spec.BAVCCipherProgram.encStar layout family) salt seed
      (Spec.SeedTree.leafOffset pair.1 pair.2)

/-- The recorded cipher calls of one leaf's commitment program. -/
def leafEntries (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Opening lambda tau (2 ^ kappa))
    (pair : Fin tau × Fin (2 ^ kappa)) : Prop :=
  ∀ seed, pair.2 ≠ hidden pair.1 → opening.revealed pair.1 pair.2 = some seed →
    expandEntries family ciphers layout variant salt (tau * 2 ^ kappa + Spec.SeedTree.leafOffset pair.1 pair.2) seed

theorem leafCommit_evaluates (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Opening lambda tau (2 ^ kappa))
    (pair : Fin tau × Fin (2 ^ kappa)) (value : Option (Digest lambda))
    (h : Evaluates family table ciphers (leafCommit (s := s) (wit := wit) (rnd := rnd) layout variant salt hidden opening pair) value) :
    value = leafValue family layout variant salt hidden opening pair ∧
      leafEntries family ciphers layout variant salt hidden opening pair := by
  unfold leafCommit at h
  unfold leafValue leafEntries
  split at h
  · rename_i hh
    cases h
    simp only [hh, ↓reduceIte, true_and]
    intro seed hne
    exact absurd rfl hne
  · rename_i hh
    simp only [hh, ↓reduceIte]
    cases hrev : opening.revealed pair.1 pair.2 with
    | none =>
      rw [hrev] at h
      cases h
      simp only [Option.map_none, true_and]
      intro seed _ habs
      cases habs
    | some seed =>
      rw [hrev] at h
      obtain ⟨commitment, hc, hdone⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp h
      obtain ⟨rfl, hentries⟩ := SharedSigner.commitCall_evaluates family table ciphers layout _ variant salt seed _ commitment hc
      cases hdone
      refine ⟨rfl, ?_⟩
      intro seed' _ hseed'
      rw [Option.some.inj hseed'] at hentries
      exact hentries

/-- The primitives induced by the executed family and table. -/
def induced (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding) :
    Primitives lambda :=
  bavcPrimitives (tau * 2 ^ kappa) variant (Spec.BAVCCipherProgram.encStar layout family) (digestAt table)

/-- A successful candidate reconstruction. -/
theorem reconstruct_evaluates (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Opening lambda tau (2 ^ kappa))
    (value : Reconstructed lambda tau (2 ^ kappa))
    (h : Evaluates family table ciphers (Spec.CandidateBAVC.reconstruct (s := s) (wit := wit) (rnd := rnd) layout variant salt hidden opening)
      (Except.ok value)) :
    let C := commitsOf (leafValue family layout variant salt hidden opening)
    let P := induced (tau := tau) (kappa := kappa) family table layout variant
    value.seeds = opening.revealed ∧
      value.hcom = P.hash (Spec.BAVCBinding.outerQuery P salt C) ∧
      (∀ e, ∃ pair, table (Spec.BAVCBinding.rowQuery C e) = some pair ∧ pair.1 = P.hash (Spec.BAVCBinding.rowQuery C e)) ∧
      (∃ pair, table (Spec.BAVCBinding.outerQuery P salt C) = some pair ∧ pair.1 = value.hcom) ∧
      (∀ e, C e (hidden e) = opening.hiddenCommitments e) ∧
      ∀ e i, i ≠ hidden e → ∃ seed, opening.revealed e i = some seed ∧
        C e i = commitSeed (tau * 2 ^ kappa) variant (Spec.BAVCCipherProgram.encStar layout family) salt seed
          (Spec.SeedTree.leafOffset e i) ∧
        expandEntries family ciphers layout variant salt (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) seed := by
  intro C P
  unfold Spec.CandidateBAVC.reconstruct at h
  obtain ⟨commits, hcommits, h1⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp h
  obtain ⟨hcin, _⟩ := SharedSigner.collect_evaluates family table ciphers _ (leafValue family layout variant salt hidden opening)
    (leafEntries family ciphers layout variant salt hidden opening)
    (fun pair v hv => leafCommit_evaluates family table ciphers layout variant salt hidden opening pair v hv) _ _ commits hcommits
  have hfun : commits = leafValue family layout variant salt hidden opening := by
    funext pair
    exact (hcin pair (SharedSlopeExec.mem_allPairs pair.1 pair.2)).1
  subst hfun
  split at h1
  swap
  · cases h1
  rename_i hall
  obtain ⟨rowHashes, hrows, h2⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp h1
  obtain ⟨hrin, _⟩ := SharedSigner.collect_evaluates family table ciphers _
    (fun e => digestAt table (Spec.BAVCBinding.rowQuery C e))
    (fun e => ∃ pair, table (Spec.BAVCBinding.rowQuery C e) = some pair)
    (fun e v hv => SharedSigner.hashCall_evaluates family table ciphers _ v hv) _ _ rowHashes hrows
  have hrowfun : rowHashes = fun e => P.hash (Spec.BAVCBinding.rowQuery C e) := by
    funext e
    exact (hrin e (List.mem_finRange e)).1
  cases h2 with
  | hash _ _ outer _ houter hdone =>
    cases hdone
    have houterq : Spec.BAVCChainInputs.outerString salt rowHashes = Spec.BAVCBinding.outerQuery P salt C := by
      rw [hrowfun]
      rfl
    refine ⟨rfl, ?_, ?_, ⟨outer, by rw [← houterq]; exact houter, rfl⟩, ?_, ?_⟩
    · show outer.1 = _
      rw [← houterq]
      exact (SharedSigner.digestAt_of_stored table _ outer houter).symm
    · intro e
      obtain ⟨pair, hpair⟩ := (hrin e (List.mem_finRange e)).2
      exact ⟨pair, hpair, (SharedSigner.digestAt_of_stored table _ pair hpair).symm⟩
    · intro e
      simp [C, commitsOf, leafValue]
    · intro e i hne
      have hsome := hall (e, i)
      simp only [leafValue, hne, ↓reduceIte, Option.isSome_map] at hsome
      obtain ⟨seed, hseed⟩ := Option.isSome_iff_exists.mp hsome
      refine ⟨seed, hseed, ?_, (hcin (e, i) (SharedSlopeExec.mem_allPairs e i)).2 seed hne hseed⟩
      simp [C, commitsOf, leafValue, hne, hseed]

/-- On the candidate opening of an honestly committed key, the recomputed
commitments are the key's. -/
theorem commits_openKey (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (hash : List Bool → Digest lambda) (salt root : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) :
    commitsOf (leafValue family layout variant salt hidden
      (openKey (Spec.BAVC.commit (bavcPrimitives (tau * 2 ^ kappa) variant (Spec.BAVCCipherProgram.encStar layout family) hash)
        salt root).key hidden)) =
      (Spec.BAVC.commit (bavcPrimitives (tau * 2 ^ kappa) variant (Spec.BAVCCipherProgram.encStar layout family) hash)
        salt root).key.commitments := by
  funext e i
  by_cases hi : i = hidden e
  · subst hi
    simp [commitsOf, leafValue, openKey]
  · simp [commitsOf, leafValue, openKey, hi]
    rfl

theorem leafCommit_bounded (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Opening lambda tau (2 ^ kappa))
    (pair : Fin tau × Fin (2 ^ kappa)) :
    Bounded 2 (leafCommit (s := s) (wit := wit) (rnd := rnd) layout variant salt hidden opening pair) := by
  unfold leafCommit
  split
  · trivial
  · split
    · trivial
    · exact HashCipherProgram.bounded_bind _ (fun commitment => Program.done (some commitment)) 2 0
        (SharedSigner.commitCall_bounded layout _ variant salt _ _) fun _ => trivial

theorem reconstruct_bounded (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Opening lambda tau (2 ^ kappa)) :
    Bounded (budget tau kappa) (Spec.CandidateBAVC.reconstruct (s := s) (wit := wit) (rnd := rnd) layout variant salt hidden opening) := by
  unfold Spec.CandidateBAVC.reconstruct budget
  refine HashCipherProgram.bounded_mono _ _ _ (by rw [Nat.mul_comm]; omega)
    (HashCipherProgram.bounded_bind _ _ ((Spec.SharedSlopeExec.allPairs tau kappa).length * 2) (tau + 1)
      (SharedSigner.collect_bounded _ 2 (fun pair => leafCommit_bounded layout variant salt hidden opening pair) _ _)
      fun commits => ?_)
  split
  · refine HashCipherProgram.bounded_mono _ _ _ (by simp [List.length_finRange])
      (HashCipherProgram.bounded_bind _ _ ((List.finRange tau).length * 1) 1
        (SharedSigner.collect_bounded _ 1 (fun e => SharedSigner.hashCall_bounded _) _ _) fun rowHashes => ?_)
    intro _
    trivial
  · trivial

end
end SDitH.Proofs.CandidateBAVC
