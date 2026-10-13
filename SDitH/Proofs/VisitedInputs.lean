import SDitH.Proofs.ForkSlopePrefix
import SDitH.Proofs.SharedSchemeChain
import SDitH.Proofs.BAVCReconstructionProgram
import SDitH.Proofs.CandidateVerifier

/-! The hash inputs visited by the executed verification. Visited inputs
compose along binds, the cipher lifts visit none, the digest lift visits
the same inputs as its projection, a successful reconstruction visits only
its row and outer queries, and a successful verification visits only the
reconstruction's queries, the auxiliary query, the middle's inputs and the
lines query; the candidate middle visits exactly the mask input. These
are the inputs the fork accounting must find in the fork table. -/

namespace SDitH.Proofs.VisitedInputs

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.HashCipherEvaluation Spec.BAVCReconstructionProgram
open Spec.SharedScheme Spec.CandidateVerifier
open Spec.SlopeConsistencyGame (Out)
open ForkSlopePrefix (hashInputs)
open scoped Classical
noncomputable section

section Generic

variable {Input Dig Key Block A B : Type*}

theorem hashInputs_bind (family : Spec.IdealCipher.Family Key Block) (table : Input → Option Dig)
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (program : Program Input Dig Key Block A)
    (next : A → Program Input Dig Key Block B) (value : A) (h : Evaluates family table ciphers program value) :
    hashInputs family table (bind program next) = hashInputs family table program ++ hashInputs family table (next value) := by
  induction h with
  | done value => rfl
  | hash input tail answer value stored _ ih =>
    simp only [Spec.HashCipherProgram.bind, hashInputs, stored, ih, List.cons_append]
  | cipher request tail value _ _ ih =>
    simp only [Spec.HashCipherProgram.bind, hashInputs, ih]

theorem hashInputs_liftCipher (family : Spec.IdealCipher.Family Key Block) (table : Input → Option Dig)
    (program : Spec.OracleProgram.Program (Spec.IdealCipher.Query Key Block) Block A) :
    hashInputs family table (liftCipher (Input := Input) (Digest := Dig) program) = [] := by
  induction program with
  | done a => rfl
  | query request next ih => simp only [liftCipher, hashInputs, ih]

end Generic

variable {lambda tau kappa s wit rnd : Nat}

theorem hashInputs_liftFirst {A : Type*} (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Out lambda s wit rnd))
    (program : Program (List Bool) (Digest lambda) (Bits lambda) (Bits lambda) A) :
    hashInputs family table (liftFirst (s := s) (wit := wit) (rnd := rnd) program) =
      hashInputs family (fun x => (table x).map Prod.fst) program := by
  induction program with
  | done a => rfl
  | hash input next ih =>
    simp only [liftFirst, hashInputs]
    cases table input with
    | none => rfl
    | some pair => simp only [Option.map_some, ih]
  | cipher request next ih => simp only [liftFirst, hashInputs, ih]

section Reconstruction

variable {N : Nat} {Key Block : Type*}

theorem rows_visited (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Grinding)
    (family : Spec.IdealCipher.Family Key Block) (table : List Bool → Option (Digest lambda))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N) :
    ∀ (count : Nat) (hc : count ≤ tau) (rows : Rows lambda N count),
      Evaluates family table ciphers (rowsThrough layout variant salt hidden opening nodes count hc) (.ok rows) →
      ∀ x ∈ hashInputs family table (rowsThrough layout variant salt hidden opening nodes count hc),
        ∃ e : Fin count, x = rowInput rows.leaves[e] := by
  intro count
  induction count with
  | zero =>
    intro hc rows h x hx
    cases hx
  | succ count ih =>
    intro hc rows h x hx
    obtain ⟨earlier, he, ht⟩ := (BAVCReconstructionProgram.evaluates_bindExcept family table ciphers _ _ _).mp h
    cases earlier with
    | error cause => cases ht
    | ok prev =>
      obtain ⟨rowResult, hr, ht'⟩ := (BAVCReconstructionProgram.evaluates_bindExcept family table ciphers _ _ _).mp ht
      cases rowResult with
      | error cause => cases ht'
      | ok row =>
        cases ht' with
        | hash _ _ digest _ stored hd =>
          cases hd
          simp only [rowsThrough, bindExcept] at hx
          rw [hashInputs_bind family table ciphers _ _ _ he] at hx
          simp only at hx
          rw [hashInputs_bind family table ciphers _ _ _ hr, hashInputs_liftCipher] at hx
          simp only [List.nil_append, hashInputs, stored, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · obtain ⟨e, he'⟩ := ih (by omega) prev he x hx
            refine ⟨⟨e.val, by omega⟩, ?_⟩
            rw [he']
            change rowInput prev.leaves[e.val] = rowInput (prev.leaves.push row)[e.val]
            rw [Vector.getElem_push_lt e.isLt]
          · refine ⟨⟨count, by omega⟩, ?_⟩
            change rowInput row = rowInput (prev.leaves.push row)[count]
            rw [Vector.getElem_push_eq]

/-- A successful reconstruction visits only its row and outer queries. -/
theorem reconstruct_visited (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Grinding)
    (family : Spec.IdealCipher.Family Key Block) (table : List Bool → Option (Digest lambda))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat) (initial : NodesBinding lambda tau N)
    (recon : Reconstructed lambda tau N)
    (h : Evaluates family table ciphers (Spec.BAVCReconstructionProgram.reconstruct layout variant salt hidden opening Topen initial) (.ok recon)) :
    ∃ rows : Rows lambda N tau, RowsCovered table rows ∧
      recon = reconstructionHashes (primitives (tau := tau) (N := N) layout variant family table) salt rows.leaves ∧
      Spec.BAVCBindingROM.observed (primitives (tau := tau) (N := N) layout variant family table) table salt
        (Spec.BAVCBinding.rowCommitments rows.leaves) = true ∧
      ∀ x ∈ hashInputs family table (Spec.BAVCReconstructionProgram.reconstruct layout variant salt hidden opening Topen initial),
        x ∈ Spec.BAVCBinding.hashQueries (primitives (tau := tau) (N := N) layout variant family table) salt
          (Spec.BAVCBinding.rowCommitments rows.leaves) := by
  unfold Spec.BAVCReconstructionProgram.reconstruct at h ⊢
  cases hp : prefill hidden opening Topen with
  | error cause =>
    rw [hp] at h
    cases h
  | ok tree =>
    rw [hp] at h
    obtain ⟨nodesResult, hn, ht⟩ := (BAVCReconstructionProgram.evaluates_bindExcept family table ciphers _ _ _).mp h
    cases nodesResult with
    | error cause => cases ht
    | ok nodes =>
      obtain ⟨rowsResult, hr, ht'⟩ := (BAVCReconstructionProgram.evaluates_bindExcept family table ciphers _ _ _).mp ht
      cases rowsResult with
      | error cause => cases ht'
      | ok rows =>
        have hcov := (BAVCReconstructionProgram.rows_evaluates layout variant family table ciphers salt hidden opening
          nodes tau le_rfl _ hr).2
        obtain ⟨hresult, hobserved⟩ := BAVCReconstructionProgram.finish_evaluates layout variant family table ciphers salt
          rows hcov _ ht'
        refine ⟨rows, hcov, Except.ok.inj hresult, hobserved, ?_⟩
        intro x hx
        simp only [bindExcept] at hx
        rw [hashInputs_bind family table ciphers _ _ _ hn, hashInputs_liftCipher] at hx
        simp only [List.nil_append] at hx
        rw [hashInputs_bind family table ciphers _ _ _ hr] at hx
        simp only [List.mem_append] at hx
        have hhash := BAVCReconstructionProgram.covered_hashes layout variant family table rows hcov
        rcases hx with hx | hx
        · obtain ⟨e, rfl⟩ := rows_visited layout variant family table ciphers salt hidden opening nodes tau le_rfl rows hr x hx
          simp only [Spec.BAVCBinding.hashQueries, List.mem_append, List.mem_ofFn]
          exact Or.inl ⟨e, rfl⟩
        · cases ht' with
          | hash _ _ root _ stored hd =>
            simp only [finish, hashInputs, stored, List.mem_singleton] at hx
            subst hx
            simp only [Spec.BAVCBinding.hashQueries, List.mem_append, List.mem_singleton]
            right
            simp only [outerInput, hhash, Spec.BAVCBinding.outerQuery, Spec.BAVCBinding.rowQuery, hashBavc]
            rfl

end Reconstruction

/-- The candidate middle visits exactly the mask input. -/
theorem candidateMiddle_visited {F : Type*} [Field F] [Algebra (ZMod 2) F] (xi : F)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (nodes : NodesBinding lambda tau (2 ^ kappa))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (salt : Bits lambda) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa))
    (recon : Reconstructed lambda tau (2 ^ kappa)) (auxiliary : Digest lambda) :
    hashInputs family table (candidateMiddle xi p nodes encode randomCount enough salt aux hidden recon auxiliary) =
      [Spec.BAVCChainInputs.maskInput auxiliary] := by
  simp only [candidateMiddle, hashInputs]
  cases table (Spec.BAVCChainInputs.maskInput auxiliary) with
  | none => rfl
  | some answer =>
    cases hfold : Spec.BLCRecompute.foldExecutionsThrough p salt (reconstructionBindings nodes recon) aux hidden
        randomCount enough tau le_rfl with
    | error cause => rfl
    | ok folded =>
      dsimp only
      cases hshares : Spec.BLCRecompute.collectShares folded with
      | error cause => rfl
      | ok shares => rfl

/-- A successful verification visits only the reconstruction's row and
outer queries, the auxiliary query, the middle's inputs and the lines query. -/
theorem verify_visited {F : Type*} (V : VerifierSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
    (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (piop : Digest lambda)
    (decomposition : Spec.BLCRetry.Counter × Opening lambda tau)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (recovered : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (h : Evaluates family table ciphers (verifyProgram V salt aux piop decomposition) (Except.ok recovered)) :
    ∃ (reconstruction : Reconstructed lambda tau (2 ^ kappa)) (rows : Rows lambda (2 ^ kappa) tau) (pa pl : Out lambda s wit rnd)
      (value : F × (Fin wit → F) × (Fin rnd → F) × (Fin s → Fin tau → Fin kappa → ZMod 2)),
      Evaluates family (SharedSchemeChain.projected table) ciphers
        (Spec.BAVCReconstructionProgram.reconstruct V.layout V.variant salt (V.expand piop decomposition.1) decomposition.2 V.Topen V.nodes)
        (Except.ok reconstruction) ∧
      RowsCovered (SharedSchemeChain.projected table) rows ∧
      reconstruction = reconstructionHashes
        (primitives (tau := tau) (N := 2 ^ kappa) V.layout V.variant family (SharedSchemeChain.projected table)) salt rows.leaves ∧
      Spec.BAVCBindingROM.observed
        (primitives (tau := tau) (N := 2 ^ kappa) V.layout V.variant family (SharedSchemeChain.projected table))
        (SharedSchemeChain.projected table) salt (Spec.BAVCBinding.rowCommitments rows.leaves) = true ∧
      table (Spec.BLCHashChain.auxQuery reconstruction.hcom (Spec.BLCHashChain.sourceTail V.encoding aux.corrections)) = some pa ∧
      Evaluates family table ciphers (V.middle salt aux (V.expand piop decomposition.1) reconstruction pa.1) (Except.ok value) ∧
      table (Spec.BLCHashChain.linesQuery pa.1 (V.encoding.vector aux.plain ++ V.encoding.base value.2.2.2)) = some pl ∧
      recovered = ⟨value.1, value.2.1, value.2.2.1, pl.1⟩ ∧
      ∀ x ∈ hashInputs family table (verifyProgram V salt aux piop decomposition),
        x ∈ Spec.BAVCBinding.hashQueries
            (primitives (tau := tau) (N := 2 ^ kappa) V.layout V.variant family (SharedSchemeChain.projected table))
            salt (Spec.BAVCBinding.rowCommitments rows.leaves) ∨
        x = Spec.BLCHashChain.auxQuery reconstruction.hcom (Spec.BLCHashChain.sourceTail V.encoding aux.corrections) ∨
        x ∈ hashInputs family table (V.middle salt aux (V.expand piop decomposition.1) reconstruction pa.1) ∨
        x = Spec.BLCHashChain.linesQuery pa.1 (V.encoding.vector aux.plain ++ V.encoding.base value.2.2.2) := by
  unfold verifyProgram at h ⊢
  obtain ⟨result, hr, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp h
  cases result with
  | error cause => cases ht
  | ok reconstruction =>
    have hrecon := (SharedScheme.liftFirst_evaluates family table ciphers _ _).mp hr
    obtain ⟨rows, hcov, hhashes, hobserved, hvisited⟩ := reconstruct_visited V.layout V.variant family _ ciphers salt _ _
      V.Topen V.nodes reconstruction hrecon
    cases ht with
    | hash _ _ pa _ hpa tail =>
      obtain ⟨middle, hm, tail'⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp tail
      cases middle with
      | error cause => cases tail'
      | ok value =>
        cases tail' with
        | hash _ _ pl _ hpl hdone =>
          cases hdone
          refine ⟨reconstruction, rows, pa, pl, value, hrecon, hcov, hhashes, hobserved, hpa, hm, hpl, rfl, ?_⟩
          intro x hx
          rw [hashInputs_bind family table ciphers _ _ _ hr, hashInputs_liftFirst] at hx
          simp only [hashInputs, hpa, List.mem_append, List.mem_cons] at hx
          rcases hx with hx | hx | hx
          · exact Or.inl (hvisited x hx)
          · exact Or.inr (Or.inl hx)
          · rw [hashInputs_bind family table ciphers _ _ _ hm] at hx
            simp only [hashInputs, hpl, List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | hx
            · exact Or.inr (Or.inr (Or.inl hx))
            · exact Or.inr (Or.inr (Or.inr hx))

end
end SDitH.Proofs.VisitedInputs
