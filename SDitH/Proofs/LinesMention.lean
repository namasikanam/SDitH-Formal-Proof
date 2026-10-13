import SDitH.Proofs.BAVCChainInputs

/-! The lines query mentions its auxiliary digest. The lines query is a
byte prefix followed by the auxiliary digest and the tail, so its window at
offset eight is the auxiliary digest, which is therefore among the query's
mentions; and the lines query differs from the mask input by length. Hence
a lines input stored before the auxiliary digest was answered is a mention
of that fresh answer, the event already charged in the composed bound, and
the lines input cannot coincide with the prefix's own mask query. -/

namespace SDitH.Proofs.LinesMention

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCHashChain
open SDitH.Proofs.BAVCChainInputs

variable {lambda tau : Nat}

/-- The window of the lines query at offset eight is the auxiliary digest. -/
theorem window_linesQuery (auxiliary : Digest lambda) (tail : List Bool) :
    window (linesQuery auxiliary tail) 8 = auxiliary := by
  funext i
  simp only [window, linesQuery]
  rw [show 8 = (byteBits 3).length from (byteBits_length 3).symm, getD_append_right,
    getD_append_left _ _ _ (by simp [i.isLt]), getD_ofFn]

/-- The lines query mentions its auxiliary digest. -/
theorem auxiliary_mem_mentions_lines (auxiliary : Digest lambda) (tail : List Bool) :
    auxiliary ∈ mentions lambda tau (linesQuery auxiliary tail) :=
  Finset.mem_image.mpr ⟨8, by simp [offsets], window_linesQuery auxiliary tail⟩

/-- The lines query is never the mask input: their lengths differ. -/
theorem linesQuery_ne_maskInput (auxiliary auxiliary' : Digest lambda) (tail : List Bool) :
    linesQuery auxiliary tail ≠ maskInput auxiliary' := by
  intro h
  have hlen := congrArg List.length h
  simp only [linesQuery, maskInput, List.length_append, List.length_ofFn, byteBits_length] at hlen
  omega

end SDitH.Proofs.LinesMention
