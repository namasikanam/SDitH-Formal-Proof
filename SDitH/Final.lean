import SDitH.Proofs.PIOPDiscrepancy
import SDitH.Proofs.ParameterChecks
import SDitH.Proofs.CommitmentDiscrepancies
import SDitH.Proofs.BAVCReconstruction
import SDitH.Assumptions

/-!
Small public theorem interface. Currently a discrepancy result only, not a
claim of completion of the requested specification or security proof.
-/

namespace SDitH.Final

open Polynomial Spec.PIOP

theorem literal_piop_not_complete :
    ∃ Δ : GaloisField 2 128,
      Δ ≠ 0 ∧
      HonestInputs (F := GaloisField 2 128) (n := 1) (m := 1) 2
        (fun _ => 0) (fun _ => 0) (fun _ => X) X ∧
      ¬ honestLiteralAccepts (n := 1) (m := 1) (fun _ => 0) (fun _ => 1)
        (fun _ => X) X Δ :=
  Proofs.categoryI_literal_completeness_counterexample

theorem table3_dimension_mismatch :
    ¬ Spec.RSDParameters.TensorDimensionsMatch Spec.RSDParameters.categoryI ∧
    ¬ Spec.RSDParameters.TensorDimensionsMatch Spec.RSDParameters.categoryIII ∧
    ¬ Spec.RSDParameters.TensorDimensionsMatch Spec.RSDParameters.categoryV :=
  Proofs.table3_tensor_dimensions_fail

theorem commitment_discrepancies :
    (∀ key : Spec.BAVC.Key 128 11 2048, ∃ opening : Spec.BAVC.Opening 128 11,
      Spec.BAVC.openCommitment key Proofs.BAVC.categoryIHidden 109 = .ok opening ∧
      ∀ (p : Spec.BAVC.Primitives 128) (salt : Spec.BAVC.Seed 128)
        (nodes : Spec.BAVC.NodesBinding 128 11 2048),
        Spec.BAVC.reconstructWithNodes p salt Proofs.BAVC.categoryIHidden opening 109 nodes =
          .error .boundRejected) ∧
    (∀ haux plain base deltaWitness : List (Fin 256), 0 < deltaWitness.length →
      Spec.commitLinesInput haux plain base deltaWitness ≠
        Spec.reconstructLinesInput haux plain base) :=
  ⟨fun key => ⟨Proofs.BAVC.categoryIOpening key, Proofs.BAVC.categoryI_open_succeeds key,
      Proofs.BAVCReconstruction.categoryI_full_rejection key⟩,
    Proofs.line_hash_inputs_differ⟩

end SDitH.Final
