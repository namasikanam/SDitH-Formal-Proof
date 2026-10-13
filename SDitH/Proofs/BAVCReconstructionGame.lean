import SDitH.Spec.BAVCReconstructionGame
import SDitH.Proofs.BAVCReconstructionCoverage
import SDitH.Proofs.HashCipherPipelineSecurity
import SDitH.Proofs.BAVCBindingROM

namespace SDitH.Proofs.BAVCReconstructionGame

open Spec.BAVC Spec.BAVCReconstructionProgram Spec.BAVCReconstructionGame
open Spec.HashCipherProgram Spec.HashCipherEvaluation
open scoped Classical
noncomputable section

variable {lambda tau N : Nat} {Key Block State : Type*}

theorem verify_bounded (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (Topen : Nat) (claim : Claim lambda tau N) : Bounded (verificationBudget tau N) (verifyProgram layout variant Topen claim) := by
  rw [verificationBudget, two_mul]
  apply HashCipherProgram.bounded_bind _ _ (budget tau N) (budget tau N)
    (BAVCReconstructionProgram.reconstruction_bounded layout variant claim.left.salt claim.left.hidden claim.left.opening Topen claim.left.nodes)
  intro left
  exact HashCipherProgram.bounded_bind _ _ (budget tau N) 0
    (BAVCReconstructionProgram.reconstruction_bounded layout variant claim.right.salt claim.right.hidden claim.right.opening Topen claim.right.nodes)
    (fun _ => trivial)

theorem verify_evaluates (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (Topen : Nat) (claim : Claim lambda tau N) (family : Spec.IdealCipher.Family Key Block)
    (table : List Bool → Option (Digest lambda)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (checked : Checked lambda tau N) (h : Evaluates family table ciphers (verifyProgram layout variant Topen claim) checked) :
    checked.claim = claim ∧
      Evaluates family table ciphers (Spec.BAVCReconstructionProgram.reconstruct layout variant claim.left.salt claim.left.hidden claim.left.opening Topen claim.left.nodes) checked.left ∧
      Evaluates family table ciphers (Spec.BAVCReconstructionProgram.reconstruct layout variant claim.right.salt claim.right.hidden claim.right.opening Topen claim.right.nodes) checked.right := by
  obtain ⟨left, hl, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ checked).mp h
  obtain ⟨right, hr, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ checked).mp ht
  cases ht
  exact ⟨rfl, hl, hr⟩

/-- Two real successful computations with inconsistent revealed seeds yield
an actual stored hash collision, or a same-index seed collision whose required
cipher entries are in this very transcript. -/
theorem evaluated_collision (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (Topen : Nat) (claim : Claim lambda tau N) (family : Spec.IdealCipher.Family Key Block)
    (out : Spec.HashCipher.Result (List Bool) (Digest lambda) Key Block State)
    (left right : Reconstructed lambda tau N)
    (hl : Evaluates family out.hashTable out.cipherHistory
      (Spec.BAVCReconstructionProgram.reconstruct layout variant claim.left.salt claim.left.hidden claim.left.opening Topen claim.left.nodes) (.ok left))
    (hr : Evaluates family out.hashTable out.cipherHistory
      (Spec.BAVCReconstructionProgram.reconstruct layout variant claim.right.salt claim.right.hidden claim.right.opening Topen claim.right.nodes) (.ok right))
    (hroot : left.hcom = right.hcom) (e : Fin tau) (i : Fin N) (leftSeed rightSeed : Seed lambda)
    (hls : left.seeds e i = some leftSeed) (hrs : right.seeds e i = some rightSeed) (hne : leftSeed ≠ rightSeed) :
    (∃ pair, Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView out) = true) ∨
      (claim.left.salt = claim.right.salt ∧
        Spec.BAVCBinding.IsSeedCollision (primitives (tau := tau) (N := N) layout variant family out.hashTable)
          claim.left.salt (Spec.SeedTree.leafOffset e i) leftSeed rightSeed ∧
        ∀ side : Bool,
          Spec.IdealCipher.entry (.encrypt (layout.key leftSeed)
            (layout.input (Spec.SeedPrimitives.cipherInput variant claim.left.salt (tau * N + Spec.SeedTree.leafOffset e i) side)))
            (family (layout.key leftSeed) (layout.input (Spec.SeedPrimitives.cipherInput variant claim.left.salt (tau * N + Spec.SeedTree.leafOffset e i) side))) ∈ out.cipherHistory ∧
          Spec.IdealCipher.entry (.encrypt (layout.key rightSeed)
            (layout.input (Spec.SeedPrimitives.cipherInput variant claim.left.salt (tau * N + Spec.SeedTree.leafOffset e i) side)))
            (family (layout.key rightSeed) (layout.input (Spec.SeedPrimitives.cipherInput variant claim.left.salt (tau * N + Spec.SeedTree.leafOffset e i) side))) ∈ out.cipherHistory) := by
  let p := primitives (tau := tau) (N := N) layout variant family out.hashTable
  have hleft := BAVCReconstructionProgram.reconstruction_evaluates layout variant family out.hashTable out.cipherHistory
    claim.left.salt claim.left.hidden claim.left.opening Topen claim.left.nodes (.ok left) hl
  have hright := BAVCReconstructionProgram.reconstruction_evaluates layout variant family out.hashTable out.cipherHistory
    claim.right.salt claim.right.hidden claim.right.opening Topen claim.right.nodes (.ok right) hr
  obtain ⟨leftRows, hlrows, hlvalue, hlcoverage⟩ := hleft.2 left rfl
  obtain ⟨rightRows, hrrows, hrvalue, hrcoverage⟩ := hright.2 right rfl
  change Spec.BAVCBinding.reconstructionRows p claim.left.salt claim.left.hidden claim.left.opening Topen claim.left.nodes = .ok leftRows at hlrows
  change Spec.BAVCBinding.reconstructionRows p claim.right.salt claim.right.hidden claim.right.opening Topen claim.right.nodes = .ok rightRows at hrrows
  have hroots : Spec.BAVCBinding.rootHash p claim.left.salt (Spec.BAVCBinding.rowCommitments leftRows) =
      Spec.BAVCBinding.rootHash p claim.right.salt (Spec.BAVCBinding.rowCommitments rightRows) := by
    change (reconstructionHashes p claim.left.salt leftRows).hcom = (reconstructionHashes p claim.right.salt rightRows).hcom
    rw [← hlvalue, ← hrvalue]
    exact hroot
  cases hf : Spec.BAVCBinding.findHashCollision p claim.left.salt claim.right.salt
      (Spec.BAVCBinding.rowCommitments leftRows) (Spec.BAVCBinding.rowCommitments rightRows) with
  | some pair =>
    have hc := BAVCBinding.find_some_collision p _ _ _ _ hroots pair hf
    have htable : Spec.BAVCBindingROM.withTable p out.hashTable = p := rfl
    have hleftQuery := BAVCBindingROM.observed_lookup p out.hashTable claim.left.salt _ hlcoverage pair.1 (by simpa only [htable] using hc.2.1)
    have hrightQuery := BAVCBindingROM.observed_lookup p out.hashTable claim.right.salt _ hrcoverage pair.2 (by simpa only [htable] using hc.2.2)
    rw [htable] at hleftQuery hrightQuery
    refine Or.inl ⟨pair, ?_⟩
    simp only [Spec.RandomOracleCollision.storedCollision, Spec.HashCipher.hashView, decide_eq_true_eq]
    exact ⟨hc.1.1, p.hash pair.1, hleftQuery, by simpa only [hc.1.2] using hrightQuery⟩
  | none =>
    have hfind : Spec.BAVCBinding.findReconstructionCollision p claim.left.salt claim.right.salt claim.left.hidden claim.right.hidden
        claim.left.opening claim.right.opening Topen claim.left.nodes claim.right.nodes = .ok none := by
      simp only [Spec.BAVCBinding.findReconstructionCollision, hlrows, hrrows, hf, Bind.bind, Except.bind]
    rcases BAVCBindingReconstruction.reconstruction_disagreement_collision p claim.left.salt claim.right.salt
      claim.left.hidden claim.right.hidden claim.left.opening claim.right.opening Topen claim.left.nodes claim.right.nodes
      left right hleft.1 hright.1 hroot e i leftSeed rightSeed hls hrs hne with ⟨pair, hp, _⟩ | ⟨_, hsalt, hseed⟩
    · rw [hfind] at hp
      cases hp
    · refine Or.inr ⟨hsalt, hseed, ?_⟩
      intro side
      exact ⟨BAVCReconstructionCoverage.reconstruction_calls layout variant family out.hashTable out.cipherHistory
        claim.left.salt claim.left.hidden claim.left.opening Topen claim.left.nodes left hl e i leftSeed hls side,
        by simpa only [hsalt] using (BAVCReconstructionCoverage.reconstruction_calls layout variant family out.hashTable out.cipherHistory
          claim.right.salt claim.right.hidden claim.right.opening Topen claim.right.nodes right hr e i rightSeed hrs side)⟩

variable [Fintype Key] [Fintype Block]

/-- Both selected reconstructions finish, including error outcomes. The
evaluation certificates refer to the same final table and cipher graph. -/
theorem joint_complete (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (Topen : Nat) (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N)
    (joint : Spec.IdealCipher.Family Key Block × Spec.HashCipher.Result (List Bool) (Digest lambda) Key Block
      (ReconstructionProgram lambda Key Block (Checked lambda tau N)))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (verificationBudget tau N)
      (fun state => verifyProgram layout variant Topen (choose state))).support) :
    ∃ checked, joint.2.state = .done checked ∧
      Evaluates joint.1 joint.2.hashTable joint.2.cipherHistory (verifyProgram layout variant Topen checked.claim) checked := by
  obtain ⟨start, _, tail, ht, he⟩ := HashCipherPipeline.joint_decompose adversary q initial procedure (verificationBudget tau N)
    (fun state => verifyProgram layout variant Topen (choose state)) joint hout
  obtain ⟨checked, hs, hv⟩ := HashCipherEvaluation.run_evaluates joint.1 _ (verificationBudget tau N)
    (verify_bounded layout variant Topen (choose start.state)) start.hashTable start.hashHistory start.cipherHistory tail ht
  have hc := (verify_evaluates layout variant Topen (choose start.state) joint.1 tail.hashTable tail.cipherHistory checked hv).1
  rw [← hc] at hv
  exact ⟨checked, by simpa only [he, Spec.HashCipher.markHash] using hs, by simpa only [he, Spec.HashCipher.markHash] using hv⟩

theorem winning_evaluations (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (Topen : Nat) (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N)
    (joint : Spec.IdealCipher.Family Key Block × Spec.HashCipher.Result (List Bool) (Digest lambda) Key Block
      (ReconstructionProgram lambda Key Block (Checked lambda tau N)))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (verificationBudget tau N)
      (fun state => verifyProgram layout variant Topen (choose state))).support)
    (hwin : wins joint.2 = true) :
    ∃ (claim : Claim lambda tau N) (left right : Reconstructed lambda tau N) (e : Fin tau) (i : Fin N) (leftSeed rightSeed : Seed lambda),
      Evaluates joint.1 joint.2.hashTable joint.2.cipherHistory
        (Spec.BAVCReconstructionProgram.reconstruct layout variant claim.left.salt claim.left.hidden claim.left.opening Topen claim.left.nodes) (.ok left) ∧
      Evaluates joint.1 joint.2.hashTable joint.2.cipherHistory
        (Spec.BAVCReconstructionProgram.reconstruct layout variant claim.right.salt claim.right.hidden claim.right.opening Topen claim.right.nodes) (.ok right) ∧
      left.hcom = right.hcom ∧ left.seeds e i = some leftSeed ∧ right.seeds e i = some rightSeed ∧ leftSeed ≠ rightSeed := by
  obtain ⟨checked, hs, hv⟩ := joint_complete layout variant Topen adversary q initial choose joint hout
  have he := verify_evaluates layout variant Topen checked.claim joint.1 joint.2.hashTable joint.2.cipherHistory checked hv
  cases hl : checked.left with
  | error cause => simp only [wins, hs, hl, Bool.false_eq_true] at hwin
  | ok left =>
    cases hr : checked.right with
    | error cause => simp only [wins, hs, hl, hr, Bool.false_eq_true] at hwin
    | ok right =>
      have hw : left.hcom = right.hcom ∧ ∃ (e : Fin tau) (i : Fin N) (ls rs : Seed lambda),
          left.seeds e i = some ls ∧ right.seeds e i = some rs ∧ ls ≠ rs := by
        simpa only [wins, hs, hl, hr, decide_eq_true_eq] using hwin
      obtain ⟨e, i, ls, rs, hls, hrs, hne⟩ := hw.2
      exact ⟨checked.claim, left, right, e, i, ls, rs, by simpa only [hl] using he.2.1,
        by simpa only [hr] using he.2.2, hw.1, hls, hrs, hne⟩

/-- Transfer the joint bound at the source program boundary. The coverage
argument is a theorem obligation, discharged by the full/III source proofs;
it is not a cryptographic assumption or a field of the specification. -/
theorem event_bound {Tag : Type*} (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (Topen : Nat) (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity)
    (hcover : ∀ joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (verificationBudget tau N)
      (fun state => verifyProgram layout variant Topen (choose state))).support, wins joint.2 = true →
        (∃ pair, Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView joint.2) = true) ∨
          Spec.IdealCipherPairCollision.Witnessed project companion joint.1 joint.2.cipherHistory) :
    ((experiment layout variant Topen adversary q initial choose).map wins) true ≤
      ((q + verificationBudget tau N).choose 2 : ENNReal) *
        ((Fintype.card (Digest lambda) : ENNReal)⁻¹ + IdealCipherPairAdaptive.pairCost Block capacity (q + verificationBudget tau N)) := by
  exact HashCipherPipelineSecurity.event_bound adversary q initial procedure (verificationBudget tau N)
    (fun state => verifyProgram layout variant Topen (choose state)) project companion hinvolution hnofix capacity hcapacity wins hcover

end
end SDitH.Proofs.BAVCReconstructionGame
