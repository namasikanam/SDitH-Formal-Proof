import SDitH.Proofs.CommitDecomposition

/-! Splitting a collection at its last call. The collector over a list with
a final element is the collector over the initial segment bound to the
final call, which updates the accumulator at the final index. This
isolates the row hashes' last query, whose fresh run is the newest trace
entry after the head, for the outer input's freshness. -/

namespace SDitH.Proofs.CollectLast

open Spec.HashCipherProgram Spec.SharedSigner
open CommitDecomposition

variable {lambda s wit rnd : Nat}

/-- The collector over an initial segment followed by a final call. -/
theorem collect_append_single {ι B : Type*} [DecidableEq ι] (call : ι → SignerProgram lambda s wit rnd B)
    (l : List ι) (k : ι) (acc : ι → B) :
    collect call (l ++ [k]) acc =
      Spec.HashCipherProgram.bind (collect call l acc) fun acc' =>
        Spec.HashCipherProgram.bind (call k) fun value => Program.done (Function.update acc' k value) := by
  induction l generalizing acc with
  | nil =>
    simp only [List.nil_append, collect]
    rfl
  | cons i rest ih =>
    simp only [List.cons_append, collect]
    rw [bind_assoc]
    congr 1
    funext value
    exact ih (Function.update acc i value)

end SDitH.Proofs.CollectLast
