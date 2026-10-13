import SDitH.Spec.HashCipherVerification
import SDitH.Proofs.HashCipherPipelineSecurity
import SDitH.Proofs.HashCipherSourcePrograms

namespace SDitH.Proofs.HashCipherVerification

open Spec.HashCipher Spec.HashCipherProgram Spec.HashCipherVerification
open scoped Classical ENNReal
noncomputable section

variable {Input Digest Key Block Tag State : Type*}
variable [Fintype Digest] [Nonempty Digest] [Fintype Key] [Fintype Block]

theorem seed_experiment_law (adversary : Procedure Input Digest Key Block State) (q : Nat) (initial : State)
    (project : Block → Tag) (choose : State → Spec.SeedVerification.Claim Key Block) :
    (seedExperiment adversary q initial project choose).map seedWins =
      directExperiment adversary q initial (fun family state =>
        decide ((choose state).left ≠ (choose state).right ∧
          (Spec.SeedVerification.checked family project (choose state)).left =
            (Spec.SeedVerification.checked family project (choose state)).right)) := by
  simp only [seedExperiment, Spec.HashCipherPipeline.experiment, Spec.HashCipherPipeline.jointExperiment,
    Spec.HashCipherPipeline.runFixed, PMF.map_bind, PMF.map_comp, Function.comp_def,
    HashCipherSourcePrograms.seed_execution, PMF.pure_map, directExperiment, jointExperiment,
    seedWins, markHash, Spec.SeedVerification.checked]
  rfl

/-- Every supported seed experiment performs all four calls on the same
family and appends their graph to the complete mixed adversarial history. -/
theorem seed_complete (adversary : Procedure Input Digest Key Block State) (q : Nat) (initial : State)
    (project : Block → Tag) (choose : State → Spec.SeedVerification.Claim Key Block)
    (joint : Spec.IdealCipher.Family Key Block × Result Input Digest Key Block (SeedState Input Digest Key Block Tag))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure 4
      (fun state => liftCipher (Spec.SeedVerification.verifyProgram project (choose state)))).support) :
    ∃ start ∈ (runFixed adversary joint.1 q initial (fun _ => none) [] []).support,
      joint.2 = ⟨.done (Spec.SeedVerification.checked joint.1 project (choose start.state)),
        start.hashTable, start.hashHistory,
        Spec.SeedVerification.verificationTrace joint.1 (choose start.state) ++ start.cipherHistory, start.hashCollided⟩ := by
  obtain ⟨start, hs, tail, ht, he⟩ := HashCipherPipeline.joint_decompose adversary q initial procedure 4
    (fun state => liftCipher (Spec.SeedVerification.verifyProgram project (choose state))) joint hout
  rw [HashCipherSourcePrograms.seed_execution, PMF.mem_support_pure_iff] at ht
  subst tail
  exact ⟨start, hs, by simpa only [markHash, Bool.or_false] using he⟩

theorem seed_winning_witnessed (adversary : Procedure Input Digest Key Block State) (q : Nat) (initial : State)
    (project : Block → Tag) (choose : State → Spec.SeedVerification.Claim Key Block) (companion : Block → Block)
    (hrelated : ∀ state, (choose state).secondInput = companion (choose state).firstInput)
    (joint : Spec.IdealCipher.Family Key Block × Result Input Digest Key Block (SeedState Input Digest Key Block Tag))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure 4
      (fun state => liftCipher (Spec.SeedVerification.verifyProgram project (choose state)))).support)
    (hwin : seedWins joint.2 = true) :
    Spec.IdealCipherPairCollision.Witnessed project companion joint.1 joint.2.cipherHistory := by
  obtain ⟨start, _, tail, ht, he⟩ := HashCipherPipeline.joint_decompose adversary q initial procedure 4
    (fun state => liftCipher (Spec.SeedVerification.verifyProgram project (choose state))) joint hout
  have hexact := ht
  rw [HashCipherSourcePrograms.seed_execution, PMF.mem_support_pure_iff] at hexact
  have hstate : tail.state = .done (Spec.SeedVerification.checked joint.1 project (choose start.state)) := by rw [hexact]
  have hw : (choose start.state).left ≠ (choose start.state).right ∧
      (Spec.SeedVerification.checked joint.1 project (choose start.state)).left =
        (Spec.SeedVerification.checked joint.1 project (choose start.state)).right := by
    simpa only [he, seedWins, markHash, hstate, decide_eq_true_eq] using hwin
  rw [he]
  exact HashCipherSourcePrograms.seed_witnessed joint.1 project (choose start.state) companion
    (hrelated start.state) start.hashTable start.hashHistory start.cipherHistory tail ht
    (Spec.SeedVerification.checked joint.1 project (choose start.state)) hstate hw

/-- Both verification commitments are included in q+4, where q bounds
mixed hash/cipher actions. No freshness or already-queried premise is needed. -/
theorem seed_binding_bound (adversary : Procedure Input Digest Key Block State) (q : Nat) (initial : State)
    (project : Block → Tag) (choose : State → Spec.SeedVerification.Claim Key Block) (companion : Block → Block)
    (hrelated : ∀ state, (choose state).secondInput = companion (choose state).firstInput)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((seedExperiment adversary q initial project choose).map seedWins) true ≤
      ((q + 4).choose 2 : ℝ≥0∞) * IdealCipherPairAdaptive.pairCost Block capacity (q + 4) := by
  apply le_trans ?_ (HashCipherPipelineSecurity.pair_bound adversary q initial procedure 4
    (fun state => liftCipher (Spec.SeedVerification.verifyProgram project (choose state)))
    project companion hinvolution hnofix capacity hcapacity)
  simp only [seedExperiment, Spec.HashCipherPipeline.experiment, PMF.map_comp, Function.comp_def]
  apply HashCipherPipelineSecurity.event_mass_le
  intro joint hs hw
  exact decide_eq_true (seed_winning_witnessed adversary q initial project choose companion hrelated joint hs hw)

variable {lambda tau N : Nat}

theorem hash_complete (p : Spec.BAVC.Primitives lambda)
    (adversary : Procedure (List Bool) (Spec.BAVC.Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Spec.BAVCBindingROM.Claim lambda tau N)
    (joint : Spec.IdealCipher.Family Key Block × Result (List Bool) (Spec.BAVC.Digest lambda) Key Block (HashState lambda tau N Key Block))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure
      (Spec.BAVCHashVerification.verificationBudget tau)
      (fun state => liftHash (Spec.BAVCHashVerification.verifyProgram (choose state)))).support) :
    ∃ start ∈ (runFixed adversary joint.1 q initial (fun _ => none) [] []).support,
      ∃ value, joint.2.state = .done value ∧ value.claim = choose start.state ∧
        Spec.BAVCBindingROM.observed p joint.2.hashTable value.claim.leftSalt value.claim.left = true ∧
        Spec.BAVCBindingROM.observed p joint.2.hashTable value.claim.rightSalt value.claim.right = true ∧
        Spec.BAVCBinding.rootHash (Spec.BAVCBindingROM.withTable p joint.2.hashTable) value.claim.leftSalt value.claim.left = value.leftRoot ∧
        Spec.BAVCBinding.rootHash (Spec.BAVCBindingROM.withTable p joint.2.hashTable) value.claim.rightSalt value.claim.right = value.rightRoot ∧
        joint.2.cipherHistory = start.cipherHistory := by
  obtain ⟨start, hs, tail, ht, he⟩ := HashCipherPipeline.joint_decompose adversary q initial procedure
    (Spec.BAVCHashVerification.verificationBudget tau)
    (fun state => liftHash (Spec.BAVCHashVerification.verifyProgram (choose state))) joint hout
  obtain ⟨value, hv, hc, hl, hr, hlroot, hrroot, htrace⟩ := HashCipherSourcePrograms.hash_complete p joint.1
    (choose start.state) start.hashTable start.hashHistory start.cipherHistory tail ht
  exact ⟨start, hs, value, by simpa only [he, markHash] using hv, hc,
    by simpa only [he, markHash] using hl, by simpa only [he, markHash] using hr,
    by simpa only [he, markHash] using hlroot, by simpa only [he, markHash] using hrroot,
    by simpa only [he, markHash] using htrace⟩

theorem hash_winning_collision (p : Spec.BAVC.Primitives lambda)
    (adversary : Procedure (List Bool) (Spec.BAVC.Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Spec.BAVCBindingROM.Claim lambda tau N)
    (joint : Spec.IdealCipher.Family Key Block × Result (List Bool) (Spec.BAVC.Digest lambda) Key Block (HashState lambda tau N Key Block))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure
      (Spec.BAVCHashVerification.verificationBudget tau)
      (fun state => liftHash (Spec.BAVCHashVerification.verifyProgram (choose state)))).support)
    (hwin : hashWins joint.2 = true) :
    ∃ pair, Spec.RandomOracleCollision.storedCollision pair (hashView joint.2) = true := by
  obtain ⟨start, _, tail, ht, he⟩ := HashCipherPipeline.joint_decompose adversary q initial procedure
    (Spec.BAVCHashVerification.verificationBudget tau)
    (fun state => liftHash (Spec.BAVCHashVerification.verifyProgram (choose state))) joint hout
  obtain ⟨value, hv, _, _, _, _, _, _⟩ := HashCipherSourcePrograms.hash_complete p joint.1
    (choose start.state) start.hashTable start.hashHistory start.cipherHistory tail ht
  have hw : value.leftRoot = value.rightRoot ∧
      (value.claim.leftSalt ≠ value.claim.rightSalt ∨ value.claim.left ≠ value.claim.right) := by
    simpa only [he, hashWins, markHash, hv, decide_eq_true_eq] using hwin
  obtain ⟨pair, hp⟩ := HashCipherSourcePrograms.hash_collision p joint.1 (choose start.state)
    start.hashTable start.hashHistory start.cipherHistory tail ht value hv hw
  exact ⟨pair, by simpa only [he, hashView, markHash, Spec.RandomOracleCollision.storedCollision, decide_eq_true_eq] using hp⟩

theorem hash_binding_bound (p : Spec.BAVC.Primitives lambda)
    (adversary : Procedure (List Bool) (Spec.BAVC.Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Spec.BAVCBindingROM.Claim lambda tau N) :
    ((hashExperiment adversary q initial choose).map hashWins) true ≤
      ((q + 2 * (tau + 1)).choose 2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (2 * lambda) := by
  have hb := HashCipherPipeline.hash_bound adversary q initial procedure (Spec.BAVCHashVerification.verificationBudget tau)
    (fun state => liftHash (Spec.BAVCHashVerification.verifyProgram (choose state)))
  have he : ((hashExperiment adversary q initial choose).map hashWins) true ≤
      ((Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (Spec.BAVCHashVerification.verificationBudget tau)
        (fun state => liftHash (Spec.BAVCHashVerification.verifyProgram (choose state)))).map (fun joint => joint.2.hashCollided)) true := by
    simp only [hashExperiment, Spec.HashCipherPipeline.experiment, PMF.map_comp, Function.comp_def]
    apply HashCipherPipelineSecurity.event_mass_le
    intro joint hs hw
    obtain ⟨pair, hp⟩ := hash_winning_collision p adversary q initial choose joint hs hw
    exact HashCipherPipeline.stored_collision_implies_flag adversary q initial procedure
      (Spec.BAVCHashVerification.verificationBudget tau)
      (fun state => liftHash (Spec.BAVCHashVerification.verifyProgram (choose state))) joint hs pair hp
  convert he.trans hb using 1
  simp [Spec.BAVCHashVerification.verificationBudget, Spec.BAVC.Digest, Spec.DomainSeparation.Bits, ENNReal.inv_pow]

end
end SDitH.Proofs.HashCipherVerification
