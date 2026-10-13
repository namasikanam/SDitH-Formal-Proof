import SDitH.Spec.CandidateScheme
import SDitH.Proofs.CandidateBAVC
import SDitH.Proofs.VisitedInputs

/-! The candidate verifier's evaluation and visited inputs. A successful
verification over the candidate reconstruction decomposes into the
reconstruction's evaluation, the auxiliary lookup, the middle's evaluation
and the lines lookup; the candidate reconstruction visits only its row and
outer queries, so the verification visits only those, the auxiliary
query, the middle's inputs and the lines query. -/

namespace SDitH.Proofs.CandidateSchemeChain

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.HashCipherEvaluation Spec.SharedScheme
open Spec.CandidateScheme Spec.CandidateBAVC Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open ForkSlopePrefix (hashInputs)
open scoped Classical
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}
variable (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
  (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))

/-- A successful candidate verification decomposes into its four stages. -/
theorem verify_evaluates {F : Type*} (V : VerifierSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
    (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (piop : Digest lambda)
    (decomposition : Spec.BLCRetry.Counter × Spec.CandidateBAVC.Opening lambda tau (2 ^ kappa))
    (recovered : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (h : Evaluates family table ciphers (Spec.CandidateScheme.verifyProgram V salt aux piop decomposition) (Except.ok recovered)) :
    ∃ (reconstruction : Reconstructed lambda tau (2 ^ kappa)) (pa pl : Out lambda s wit rnd)
      (value : F × (Fin wit → F) × (Fin rnd → F) × (Fin s → Fin tau → Fin kappa → ZMod 2)),
      Evaluates family table ciphers
        (Spec.CandidateBAVC.reconstruct V.layout V.variant salt (V.expand piop decomposition.1) decomposition.2)
        (Except.ok reconstruction) ∧
      table (Spec.BLCHashChain.auxQuery reconstruction.hcom (Spec.BLCHashChain.sourceTail V.encoding aux.corrections)) = some pa ∧
      Evaluates family table ciphers (V.middle salt aux (V.expand piop decomposition.1) reconstruction pa.1) (Except.ok value) ∧
      table (Spec.BLCHashChain.linesQuery pa.1 (V.encoding.vector aux.plain ++ V.encoding.base value.2.2.2)) = some pl ∧
      recovered = ⟨value.1, value.2.1, value.2.2.1, pl.1⟩ := by
  unfold Spec.CandidateScheme.verifyProgram at h
  obtain ⟨result, hr, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp h
  cases result with
  | error cause => cases ht
  | ok reconstruction =>
    cases ht with
    | hash _ _ pa _ hpa tail =>
      obtain ⟨middle, hm, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp tail
      cases middle with
      | error cause => cases ht
      | ok value =>
        cases ht with
        | hash _ _ pl _ hpl done =>
          cases done
          exact ⟨reconstruction, pa, pl, value, hr, hpa, hm, hpl, rfl⟩

theorem hashInputs_leafCommit (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Spec.CandidateBAVC.Opening lambda tau (2 ^ kappa))
    (pair : Fin tau × Fin (2 ^ kappa)) :
    hashInputs family table (leafCommit (s := s) (wit := wit) (rnd := rnd) layout variant salt hidden opening pair) = [] := by
  unfold leafCommit
  split
  · rfl
  · split
    · rfl
    · simp only [commitCall, expandCall, Spec.HashCipherProgram.bind, hashInputs]

/-- Visited inputs of a collector: each comes from some listed call. -/
theorem hashInputs_collect {ι B : Type*} [DecidableEq ι] (call : ι → SignerProgram lambda s wit rnd B) :
    ∀ (l : List ι) (acc : ι → B) (value : ι → B),
      Evaluates family table ciphers (collect call l acc) value →
      ∀ x ∈ hashInputs family table (collect call l acc), ∃ k ∈ l, x ∈ hashInputs family table (call k) := by
  intro l
  induction l with
  | nil =>
    intro acc value _ x hx
    cases hx
  | cons k rest ih =>
    intro acc value h x hx
    obtain ⟨middle, hmid, hrest⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp h
    simp only [collect] at hx
    rw [VisitedInputs.hashInputs_bind family table ciphers _ _ _ hmid, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ⟨k, List.mem_cons_self, hx⟩
    · obtain ⟨k', hk', hx'⟩ := ih _ _ hrest x hx
      exact ⟨k', List.mem_cons_of_mem k hk', hx'⟩

/-- A successful candidate reconstruction visits only its row and outer queries. -/
theorem reconstruct_visited (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Spec.CandidateBAVC.Opening lambda tau (2 ^ kappa))
    (value : Reconstructed lambda tau (2 ^ kappa))
    (h : Evaluates family table ciphers (Spec.CandidateBAVC.reconstruct (s := s) (wit := wit) (rnd := rnd) layout variant salt hidden opening)
      (Except.ok value)) :
    let C := commitsOf (CandidateBAVC.leafValue family layout variant salt hidden opening)
    let P := CandidateBAVC.induced (tau := tau) (kappa := kappa) family table layout variant
    ∀ x ∈ hashInputs family table (Spec.CandidateBAVC.reconstruct (s := s) (wit := wit) (rnd := rnd) layout variant salt hidden opening),
      x ∈ Spec.BAVCBinding.hashQueries P salt C := by
  intro C P x hx
  unfold Spec.CandidateBAVC.reconstruct at h hx
  obtain ⟨commits, hcommits, h1⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp h
  rw [VisitedInputs.hashInputs_bind family table ciphers _ _ _ hcommits, List.mem_append] at hx
  rcases hx with hx | hx
  · obtain ⟨k, _, hk⟩ := hashInputs_collect family table ciphers _ _ _ _ hcommits x hx
    rw [hashInputs_leafCommit] at hk
    cases hk
  · have hfun : commits = CandidateBAVC.leafValue family layout variant salt hidden opening := by
      obtain ⟨hcin, _⟩ := SharedSigner.collect_evaluates family table ciphers _
        (CandidateBAVC.leafValue family layout variant salt hidden opening)
        (CandidateBAVC.leafEntries family ciphers layout variant salt hidden opening)
        (fun pair v hv => CandidateBAVC.leafCommit_evaluates family table ciphers layout variant salt hidden opening pair v hv)
        _ _ commits hcommits
      funext pair
      exact (hcin pair (SharedSlopeExec.mem_allPairs pair.1 pair.2)).1
    subst hfun
    split at h1
    swap
    · cases h1
    rename_i hall
    rw [if_pos hall] at hx
    obtain ⟨rowHashes, hrows, h2⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp h1
    rw [VisitedInputs.hashInputs_bind family table ciphers _ _ _ hrows, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨e, _, he⟩ := hashInputs_collect family table ciphers _ _ _ _ hrows x hx
      simp only [hashCall, hashInputs] at he
      have hmem : x = Spec.BAVCBinding.rowQuery C e := by
        split at he <;> exact List.mem_singleton.mp he
      rw [hmem]
      exact BAVCBinding.rowQuery_mem P salt C e
    · obtain ⟨hrin, _⟩ := SharedSigner.collect_evaluates family table ciphers _
        (fun e => SharedSigner.digestAt table (Spec.BAVCBinding.rowQuery C e))
        (fun e => ∃ pair, table (Spec.BAVCBinding.rowQuery C e) = some pair)
        (fun e v hv => SharedSigner.hashCall_evaluates family table ciphers _ v hv) _ _ rowHashes hrows
      have hrowfun : rowHashes = fun e => P.hash (Spec.BAVCBinding.rowQuery C e) := by
        funext e
        exact (hrin e (List.mem_finRange e)).1
      cases h2 with
      | hash _ _ outer _ houter _ =>
        simp only [hashInputs, houter, List.mem_singleton] at hx
        rw [hx, hrowfun]
        exact BAVCBinding.outerQuery_mem P salt C

/-- A successful candidate verification visits only the reconstruction's
queries, the auxiliary query, the middle's inputs and the lines query. -/
theorem verify_visited {F : Type*} (V : VerifierSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
    (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (piop : Digest lambda)
    (decomposition : Spec.BLCRetry.Counter × Spec.CandidateBAVC.Opening lambda tau (2 ^ kappa))
    (recovered : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (h : Evaluates family table ciphers (Spec.CandidateScheme.verifyProgram V salt aux piop decomposition) (Except.ok recovered)) :
    ∃ (reconstruction : Reconstructed lambda tau (2 ^ kappa)) (pa pl : Out lambda s wit rnd)
      (value : F × (Fin wit → F) × (Fin rnd → F) × (Fin s → Fin tau → Fin kappa → ZMod 2)),
      Evaluates family table ciphers
        (Spec.CandidateBAVC.reconstruct V.layout V.variant salt (V.expand piop decomposition.1) decomposition.2)
        (Except.ok reconstruction) ∧
      table (Spec.BLCHashChain.auxQuery reconstruction.hcom (Spec.BLCHashChain.sourceTail V.encoding aux.corrections)) = some pa ∧
      Evaluates family table ciphers (V.middle salt aux (V.expand piop decomposition.1) reconstruction pa.1) (Except.ok value) ∧
      table (Spec.BLCHashChain.linesQuery pa.1 (V.encoding.vector aux.plain ++ V.encoding.base value.2.2.2)) = some pl ∧
      recovered = ⟨value.1, value.2.1, value.2.2.1, pl.1⟩ ∧
      ∀ x ∈ hashInputs family table (Spec.CandidateScheme.verifyProgram V salt aux piop decomposition),
        x ∈ Spec.BAVCBinding.hashQueries (CandidateBAVC.induced (tau := tau) (kappa := kappa) family table V.layout V.variant) salt
            (commitsOf (CandidateBAVC.leafValue family V.layout V.variant salt (V.expand piop decomposition.1) decomposition.2)) ∨
        x = Spec.BLCHashChain.auxQuery reconstruction.hcom (Spec.BLCHashChain.sourceTail V.encoding aux.corrections) ∨
        x ∈ hashInputs family table (V.middle salt aux (V.expand piop decomposition.1) reconstruction pa.1) ∨
        x = Spec.BLCHashChain.linesQuery pa.1 (V.encoding.vector aux.plain ++ V.encoding.base value.2.2.2) := by
  unfold Spec.CandidateScheme.verifyProgram at h ⊢
  obtain ⟨result, hr, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp h
  cases result with
  | error cause => cases ht
  | ok reconstruction =>
    have hvisited := reconstruct_visited family table ciphers V.layout V.variant salt _ _ reconstruction hr
    cases ht with
    | hash _ _ pa _ hpa tail =>
      obtain ⟨middle, hm, tail'⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp tail
      cases middle with
      | error cause => cases tail'
      | ok value =>
        cases tail' with
        | hash _ _ pl _ hpl hdone =>
          cases hdone
          refine ⟨reconstruction, pa, pl, value, hr, hpa, hm, hpl, rfl, ?_⟩
          intro x hx
          rw [VisitedInputs.hashInputs_bind family table ciphers _ _ _ hr] at hx
          simp only [hashInputs, hpa, List.mem_append, List.mem_cons] at hx
          rcases hx with hx | hx | hx
          · exact Or.inl (hvisited x hx)
          · exact Or.inr (Or.inl hx)
          · rw [VisitedInputs.hashInputs_bind family table ciphers _ _ _ hm] at hx
            simp only [hashInputs, hpl, List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | hx
            · exact Or.inr (Or.inr (Or.inl hx))
            · exact Or.inr (Or.inr (Or.inr hx))

end
end SDitH.Proofs.CandidateSchemeChain
