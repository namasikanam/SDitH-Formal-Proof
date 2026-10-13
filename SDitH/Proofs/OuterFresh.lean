import SDitH.Proofs.ChainFresh
import SDitH.Proofs.CollectLast

/-! The outer input's freshness as a mention event. The outer string and a
row query have the same byte prefix but lengths of different parity, so
they differ; the row hashes' collection splits at its last execution, whose
fresh query is the newest trace entry; a stored outer string over the
recorded row hashes mentions that newest answer, raising the mention
event. Under the negation of the charged mention event the outer input is
fresh when the prefix asks it. -/

namespace SDitH.Proofs.OuterFresh

open Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.BAVCChainInputs Spec.BAVC
open Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner
open SDitH.Proofs.BAVCChainInputs ChainFresh CollectLast
open scoped Classical

variable {lambda tau N : Nat}

/-- The outer string is never a row query: their lengths have different
parity. -/
theorem outerString_ne_rowQuery (hl : 0 < lambda) (salt : Seed lambda) (rowHashes : Fin tau → Digest lambda)
    (commits : Spec.BAVCBinding.Commitments lambda tau N) (e : Fin tau) :
    outerString salt rowHashes ≠ Spec.BAVCBinding.rowQuery commits e := by
  intro h
  have hlen := congrArg List.length h
  simp only [outerString, Spec.BAVCBinding.rowQuery, List.length_append, List.length_ofFn, byteBits_length,
    BAVC.serializeArray_length] at hlen
  have hmul : lambda * (1 + tau * 2) = lambda * (N * 2) := by nlinarith [hlen]
  have hodd := Nat.eq_of_mul_eq_mul_left hl hmul
  omega

variable {M : Type*}

/-- After the last row query, a stored outer string over the recorded row
hashes is a mention event. -/
theorem outer_stored_mention (hl : 0 < lambda) (table : List Bool → Option (Digest lambda × M))
    (rowEntry : Entry (List Bool) (Digest lambda × M)) (older : List (Entry (List Bool) (Digest lambda × M)))
    (htraced : Traced table (rowEntry :: older)) (commits : Spec.BAVCBinding.Commitments lambda tau N) (e : Fin tau)
    (hrow : rowEntry.input = Spec.BAVCBinding.rowQuery commits e) (salt : Seed lambda) (rowHashes : Fin tau → Digest lambda)
    (hanswer : rowHashes e = rowEntry.answer.1) (d : Digest lambda × M)
    (hstored : table (outerString salt rowHashes) = some d) :
    prefixBad (digestMention (mentions lambda tau)) (rowEntry :: older) = true :=
  prefixBad_of_stored_head (mentions lambda tau) table rowEntry older htraced _ d hstored
    (by rw [hrow]; exact outerString_ne_rowQuery hl salt rowHashes commits e)
    (by rw [← hanswer]; exact rowHash_mem_mentions salt rowHashes e)

variable {s wit rnd : Nat}

/-- The last execution index. -/
def lastIndex (htau : tau ≠ 0) : Fin tau :=
  (List.finRange tau).getLast (List.ne_nil_of_length_pos (by rw [List.length_finRange]; omega))

/-- The row hashes' collection splits at its last execution. -/
theorem rows_collect_split {B : Type*} (htau : tau ≠ 0) (call : Fin tau → SignerProgram lambda s wit rnd B)
    (acc : Fin tau → B) :
    collect call (List.finRange tau) acc =
      Spec.HashCipherProgram.bind (collect call (List.finRange tau).dropLast acc) fun acc' =>
        Spec.HashCipherProgram.bind (call (lastIndex htau)) fun value =>
          Program.done (Function.update acc' (lastIndex htau) value) := by
  have hne : List.finRange tau ≠ [] := List.ne_nil_of_length_pos (by rw [List.length_finRange]; omega)
  have hsplit : (List.finRange tau).dropLast ++ [lastIndex htau] = List.finRange tau :=
    List.dropLast_append_getLast hne
  conv_lhs => rw [← hsplit]
  exact collect_append_single call (List.finRange tau).dropLast (lastIndex htau) acc

end SDitH.Proofs.OuterFresh
