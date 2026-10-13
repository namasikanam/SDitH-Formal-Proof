import SDitH.Proofs.HashCipherProgram
import SDitH.Proofs.BAVCHashVerification
import SDitH.Proofs.SourceSeedVerification
import SDitH.Proofs.HashCipherSecurity

/-! Operational links from the existing source verification programs into the
shared interpreter. These are component execution/coverage results; they do not
yet execute full BAVC tree reconstruction or the signature's honest services. -/

namespace SDitH.Proofs.HashCipherSourcePrograms

open Spec.HashCipherProgram
open scoped Classical ENNReal
noncomputable section

variable {Input Digest Key Block Tag : Type*} [Fintype Digest] [Nonempty Digest]

theorem seed_execution (family : Spec.IdealCipher.Family Key Block) (project : Block → Tag)
    (claim : Spec.SeedVerification.Claim Key Block) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) :
    Spec.HashCipher.runFixed procedure family 4 (liftCipher (Spec.SeedVerification.verifyProgram project claim)) table hashes ciphers =
      PMF.pure ⟨.done (Spec.SeedVerification.checked family project claim), table, hashes,
        Spec.SeedVerification.verificationTrace family claim ++ ciphers, false⟩ := by
  rw [HashCipherProgram.run_liftCipher, SeedVerification.run_verify, PMF.pure_map]
  rfl

/-- A successful seed check supplies the paired-cipher witness from its actual
four calls in the shared graph, even if none were present in the prefix. -/
theorem seed_witnessed (family : Spec.IdealCipher.Family Key Block) (project : Block → Tag)
    (claim : Spec.SeedVerification.Claim Key Block) (companion : Block → Block)
    (hrelated : claim.secondInput = companion claim.firstInput) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (out : Spec.HashCipher.Result Input Digest Key Block (Program Input Digest Key Block (Spec.SeedVerification.Checked Key Block Tag)))
    (hout : out ∈ (Spec.HashCipher.runFixed procedure family 4 (liftCipher (Spec.SeedVerification.verifyProgram project claim)) table hashes ciphers).support)
    (value : Spec.SeedVerification.Checked Key Block Tag) (hstate : out.state = .done value)
    (hwin : value.claim.left ≠ value.claim.right ∧ value.left = value.right) :
    Spec.IdealCipherPairCollision.Witnessed project companion family out.cipherHistory := by
  rw [seed_execution, PMF.mem_support_pure_iff] at hout
  subst out
  change Program.done (Spec.SeedVerification.checked family project claim) = Program.done value at hstate
  have hv := Program.done.inj hstate
  subst value
  have hfirst := congrArg Prod.fst hwin.2
  have hsecond := congrArg Prod.snd hwin.2
  refine ⟨⟨claim.left, claim.firstInput, family claim.left claim.firstInput⟩, ?_,
    ⟨claim.right, claim.firstInput, family claim.right claim.firstInput⟩, ?_, hwin.1, rfl, hfirst, ?_⟩
  · simp only [Spec.SeedVerification.verificationTrace, List.mem_append, List.mem_cons]
    tauto
  · simp only [Spec.SeedVerification.verificationTrace, List.mem_append, List.mem_cons]
    tauto
  · change project (family claim.left (companion claim.firstInput)) = project (family claim.right (companion claim.firstInput))
    rw [← hrelated]
    exact hsecond

variable {lambda tau N : Nat}

theorem hash_complete (p : Spec.BAVC.Primitives lambda) (family : Spec.IdealCipher.Family Key Block)
    (claim : Spec.BAVCBindingROM.Claim lambda tau N) (table : List Bool → Option (Spec.BAVC.Digest lambda))
    (hashes : List (List Bool × Spec.BAVC.Digest lambda)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (out : Spec.HashCipher.Result (List Bool) (Spec.BAVC.Digest lambda) Key Block
      (Program (List Bool) (Spec.BAVC.Digest lambda) Key Block (Spec.BAVCHashVerification.Checked lambda tau N)))
    (hout : out ∈ (Spec.HashCipher.runFixed procedure family (Spec.BAVCHashVerification.verificationBudget tau)
      (liftHash (Spec.BAVCHashVerification.verifyProgram claim)) table hashes ciphers).support) :
    ∃ checked, out.state = .done checked ∧ checked.claim = claim ∧
      Spec.BAVCBindingROM.observed p out.hashTable checked.claim.leftSalt checked.claim.left = true ∧
      Spec.BAVCBindingROM.observed p out.hashTable checked.claim.rightSalt checked.claim.right = true ∧
      Spec.BAVCBinding.rootHash (Spec.BAVCBindingROM.withTable p out.hashTable) checked.claim.leftSalt checked.claim.left = checked.leftRoot ∧
      Spec.BAVCBinding.rootHash (Spec.BAVCBindingROM.withTable p out.hashTable) checked.claim.rightSalt checked.claim.right = checked.rightRoot ∧
      out.cipherHistory = ciphers := by
  rw [HashCipherProgram.run_liftHash] at hout
  obtain ⟨original, ho, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  subst out
  obtain ⟨checked, hc, heval⟩ := OracleProgram.run_evaluates (Spec.BAVCHashVerification.verifyProgram claim)
    (Spec.BAVCHashVerification.verificationBudget tau) (BAVCHashVerification.verify_bounded claim) table hashes original ho
  have hv := BAVCHashVerification.verify_evaluates p original.table claim checked heval
  exact ⟨checked, by simp only [liftHashResult, hc, liftHash], hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, rfl⟩

/-- Equal computed roots for different leaf data yield actual stored hash
collisions in the shared interpreter, with every row/outer lookup executed. -/
theorem hash_collision (p : Spec.BAVC.Primitives lambda) (family : Spec.IdealCipher.Family Key Block)
    (claim : Spec.BAVCBindingROM.Claim lambda tau N) (table : List Bool → Option (Spec.BAVC.Digest lambda))
    (hashes : List (List Bool × Spec.BAVC.Digest lambda)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (out : Spec.HashCipher.Result (List Bool) (Spec.BAVC.Digest lambda) Key Block
      (Program (List Bool) (Spec.BAVC.Digest lambda) Key Block (Spec.BAVCHashVerification.Checked lambda tau N)))
    (hout : out ∈ (Spec.HashCipher.runFixed procedure family (Spec.BAVCHashVerification.verificationBudget tau)
      (liftHash (Spec.BAVCHashVerification.verifyProgram claim)) table hashes ciphers).support)
    (value : Spec.BAVCHashVerification.Checked lambda tau N) (hstate : out.state = .done value)
    (hwin : value.leftRoot = value.rightRoot ∧
      (value.claim.leftSalt ≠ value.claim.rightSalt ∨ value.claim.left ≠ value.claim.right)) :
    ∃ pair, Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView out) = true := by
  obtain ⟨checked, hc, _, hl, hr, hlroot, hrroot, _⟩ := hash_complete p family claim table hashes ciphers out hout
  have hv := Program.done.inj (hc.symm.trans hstate)
  subst value
  have hclaim : Spec.BAVCBindingROM.claimWins p checked.claim (Spec.HashCipher.hashView out) = true := by
    simp only [Spec.BAVCBindingROM.claimWins, Spec.HashCipher.hashView, hl, hr, Bool.true_and, decide_eq_true_eq]
    exact ⟨hlroot.trans (hwin.1.trans hrroot.symm), hwin.2⟩
  obtain ⟨pair, _, hp⟩ := BAVCBindingROM.winning_claim_collision p checked.claim (Spec.HashCipher.hashView out) hclaim
  exact ⟨pair, hp⟩

end
end SDitH.Proofs.HashCipherSourcePrograms
