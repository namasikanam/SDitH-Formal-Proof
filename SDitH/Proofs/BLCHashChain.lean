import SDitH.Spec.BLCHashChain
import SDitH.Proofs.BLCBinding
import SDitH.Proofs.HashCipherEvaluation

namespace SDitH.Proofs.BLCHashChain

open Spec.BAVC Spec.BLCHashChain Spec.HashCipherProgram Spec.HashCipherEvaluation
open scoped Classical
noncomputable section

variable {lambda : Nat} {Key Block State : Type*}

theorem done_eq {A : Type*} (family : Spec.IdealCipher.Family Key Block) (table : List Bool → Option (Digest lambda))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (a b : A)
    (h : Evaluates family table ciphers (.done a) b) : a = b := by
  cases h
  rfl

theorem bounded (root : Digest lambda) (tail : List Bool)
    (middle : Digest lambda → ChainProgram lambda Key Block (List Bool))
    (m : Nat) (hm : ∀ answer, Bounded m (middle answer)) : Bounded (m + 2) (program root tail middle) := by
  intro auxiliary
  exact HashCipherProgram.bounded_bind _ _ m 1 (hm auxiliary) (fun _ _ => trivial)

theorem evaluates (family : Spec.IdealCipher.Family Key Block) (table : List Bool → Option (Digest lambda))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (root : Digest lambda) (tail : List Bool)
    (middle : Digest lambda → ChainProgram lambda Key Block (List Bool)) (value : Result lambda)
    (h : Evaluates family table ciphers (program root tail middle) value) :
    table (auxQuery root tail) = some value.auxiliary ∧
      Evaluates family table ciphers (middle value.auxiliary) value.tail ∧
      table (linesQuery value.auxiliary value.tail) = some value.lines := by
  cases h with
  | hash _ _ auxiliary _ ha ht =>
    obtain ⟨tail, hm, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ value).mp ht
    cases ht with
    | hash _ _ lines _ hl hd =>
      cases hd
      exact ⟨ha, hm, hl⟩

theorem aux_header (left right : Digest lambda) (leftTail rightTail : List Bool)
    (h : auxQuery left leftTail = auxQuery right rightTail) : left = right :=
  BLCBinding.fixed_header_eq (byteBits 2) left right leftTail rightTail h

theorem lines_header (left right : Digest lambda) (leftTail rightTail : List Bool)
    (h : linesQuery left leftTail = linesQuery right rightTail) : left = right :=
  BLCBinding.fixed_header_eq (byteBits 3) left right leftTail rightTail h

/-- Equal line digests recover the root unless the actual two-call chains
exhibit a stored collision. The middle programs may make arbitrary further
hash/cipher queries; their evaluations refer to this same final table. -/
theorem equal_lines_root_or_collision (family : Spec.IdealCipher.Family Key Block)
    (out : Spec.HashCipher.Result (List Bool) (Digest lambda) Key Block State)
    (leftRoot rightRoot : Digest lambda) (leftTail rightTail : List Bool)
    (leftMiddle rightMiddle : Digest lambda → ChainProgram lambda Key Block (List Bool))
    (left right : Result lambda)
    (hl : Evaluates family out.hashTable out.cipherHistory (program leftRoot leftTail leftMiddle) left)
    (hr : Evaluates family out.hashTable out.cipherHistory (program rightRoot rightTail rightMiddle) right)
    (heq : left.lines = right.lines) :
    leftRoot = rightRoot ∨ ∃ pair, Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView out) = true := by
  obtain ⟨hla, _, hll⟩ := evaluates family out.hashTable out.cipherHistory leftRoot leftTail leftMiddle left hl
  obtain ⟨hra, _, hrl⟩ := evaluates family out.hashTable out.cipherHistory rightRoot rightTail rightMiddle right hr
  by_cases hlines : linesQuery left.auxiliary left.tail = linesQuery right.auxiliary right.tail
  · have haux := lines_header left.auxiliary right.auxiliary left.tail right.tail hlines
    by_cases hroot : auxQuery leftRoot leftTail = auxQuery rightRoot rightTail
    · exact Or.inl (aux_header leftRoot rightRoot leftTail rightTail hroot)
    · refine Or.inr ⟨(auxQuery leftRoot leftTail, auxQuery rightRoot rightTail), ?_⟩
      simp only [Spec.RandomOracleCollision.storedCollision, Spec.HashCipher.hashView, decide_eq_true_eq]
      exact ⟨hroot, left.auxiliary, hla, by simpa only [haux] using hra⟩
  · refine Or.inr ⟨(linesQuery left.auxiliary left.tail, linesQuery right.auxiliary right.tail), ?_⟩
    simp only [Spec.RandomOracleCollision.storedCollision, Spec.HashCipher.hashView, decide_eq_true_eq]
    exact ⟨hlines, left.lines, hll, by simpa only [heq] using hrl⟩

theorem source_aux_query (category : Spec.FieldRepresentation.Category) {tau kappa s wit rnd : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s) (root : Digest (Spec.FieldRepresentation.width category))
    (corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2) :
    auxQuery root (sourceTail encoding corrections) = Spec.BLCBinding.auxQuery category encoding ⟨root, corrections⟩ := rfl

theorem source_lines_query (category : Spec.FieldRepresentation.Category) {tau kappa s : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s) (auxiliary : Digest (Spec.FieldRepresentation.width category))
    (plain : Fin s → ZMod 2) (base : Fin s → Fin tau → Fin kappa → ZMod 2) :
    linesQuery auxiliary (encoding.vector plain ++ encoding.base base) =
      Spec.BLCBinding.linesQuery category encoding ⟨auxiliary, plain, base⟩ := by
  simp only [linesQuery, Spec.BLCBinding.linesQuery, Spec.BLCRecompute.linesPayload, List.append_assoc]

theorem source_middle_bounded (category : Spec.FieldRepresentation.Category) {tau kappa s : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s) (plain : Fin s → ZMod 2)
    (base : Digest (Spec.FieldRepresentation.width category) → ChainProgram (Spec.FieldRepresentation.width category) Key Block
      (Fin s → Fin tau → Fin kappa → ZMod 2)) (m : Nat) (hm : ∀ answer, Bounded m (base answer))
    (auxiliary : Digest (Spec.FieldRepresentation.width category)) :
    Bounded m (sourceMiddle category encoding plain base auxiliary) :=
  HashCipherProgram.bounded_bind _ _ m 0 (hm auxiliary) (fun _ => trivial)

/-- The source constructor queries exactly the submitted Aux/Lines payloads.
It neither inserts the signer's missing fourth field nor supplies line 21. -/
theorem source_evaluates (category : Spec.FieldRepresentation.Category) {tau kappa s wit rnd : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s) (root : Digest (Spec.FieldRepresentation.width category))
    (corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2) (plain : Fin s → ZMod 2)
    (base : Digest (Spec.FieldRepresentation.width category) → ChainProgram (Spec.FieldRepresentation.width category) Key Block
      (Fin s → Fin tau → Fin kappa → ZMod 2)) (family : Spec.IdealCipher.Family Key Block)
    (table : List Bool → Option (Digest (Spec.FieldRepresentation.width category))) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (value : Result (Spec.FieldRepresentation.width category))
    (h : Evaluates family table ciphers (sourceProgram category encoding root corrections plain base) value) :
    ∃ matrix, Evaluates family table ciphers (base value.auxiliary) matrix ∧
      table (Spec.BLCBinding.auxQuery category encoding ⟨root, corrections⟩) = some value.auxiliary ∧
      table (Spec.BLCBinding.linesQuery category encoding ⟨value.auxiliary, plain, matrix⟩) = some value.lines := by
  obtain ⟨ha, hm, hl⟩ := evaluates family table ciphers root (sourceTail encoding corrections)
    (sourceMiddle category encoding plain base) value h
  obtain ⟨matrix, hb, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ value.tail).mp hm
  have htail := done_eq family table ciphers _ _ ht
  rw [← htail, source_lines_query] at hl
  exact ⟨matrix, hb, by simpa only [source_aux_query] using ha, hl⟩

theorem partial_bounded {Error : Type*} (root : Digest lambda) (tail : List Bool)
    (middle : Digest lambda → ChainProgram lambda Key Block (Except Error (List Bool)))
    (m : Nat) (hm : ∀ answer, Bounded m (middle answer)) : Bounded (m + 2) (partialProgram root tail middle) := by
  intro auxiliary
  apply HashCipherProgram.bounded_bind _ _ m 1 (hm auxiliary)
  intro result
  cases result with
  | error cause => trivial
  | ok tail => intro _; trivial

theorem partial_evaluates {Error : Type*} (family : Spec.IdealCipher.Family Key Block) (table : List Bool → Option (Digest lambda))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (root : Digest lambda) (tail : List Bool)
    (middle : Digest lambda → ChainProgram lambda Key Block (Except Error (List Bool))) (value : Result lambda)
    (h : Evaluates family table ciphers (partialProgram root tail middle) (.ok value)) :
    table (auxQuery root tail) = some value.auxiliary ∧
      Evaluates family table ciphers (middle value.auxiliary) (.ok value.tail) ∧
      table (linesQuery value.auxiliary value.tail) = some value.lines := by
  cases h with
  | hash _ _ auxiliary _ ha ht =>
    obtain ⟨middleResult, hm, ht⟩ :=
      (HashCipherEvaluation.evaluates_bind family table ciphers _ _ (Except.ok value)).mp ht
    cases middleResult with
    | error cause => cases ht
    | ok tail =>
      cases ht with
      | hash _ _ lines _ hl hd =>
        cases hd
        exact ⟨ha, hm, hl⟩

theorem partial_equal_lines_root_or_collision {Error : Type*} (family : Spec.IdealCipher.Family Key Block)
    (out : Spec.HashCipher.Result (List Bool) (Digest lambda) Key Block State)
    (leftRoot rightRoot : Digest lambda) (leftTail rightTail : List Bool)
    (leftMiddle rightMiddle : Digest lambda → ChainProgram lambda Key Block (Except Error (List Bool)))
    (left right : Result lambda)
    (hl : Evaluates family out.hashTable out.cipherHistory (partialProgram leftRoot leftTail leftMiddle) (.ok left))
    (hr : Evaluates family out.hashTable out.cipherHistory (partialProgram rightRoot rightTail rightMiddle) (.ok right))
    (heq : left.lines = right.lines) :
    leftRoot = rightRoot ∨ ∃ pair, Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView out) = true := by
  obtain ⟨hla, _, hll⟩ := partial_evaluates family out.hashTable out.cipherHistory leftRoot leftTail leftMiddle left hl
  obtain ⟨hra, _, hrl⟩ := partial_evaluates family out.hashTable out.cipherHistory rightRoot rightTail rightMiddle right hr
  by_cases hlines : linesQuery left.auxiliary left.tail = linesQuery right.auxiliary right.tail
  · have haux := lines_header left.auxiliary right.auxiliary left.tail right.tail hlines
    by_cases hroot : auxQuery leftRoot leftTail = auxQuery rightRoot rightTail
    · exact Or.inl (aux_header leftRoot rightRoot leftTail rightTail hroot)
    · refine Or.inr ⟨(auxQuery leftRoot leftTail, auxQuery rightRoot rightTail), ?_⟩
      simp only [Spec.RandomOracleCollision.storedCollision, Spec.HashCipher.hashView, decide_eq_true_eq]
      exact ⟨hroot, left.auxiliary, hla, by simpa only [haux] using hra⟩
  · refine Or.inr ⟨(linesQuery left.auxiliary left.tail, linesQuery right.auxiliary right.tail), ?_⟩
    simp only [Spec.RandomOracleCollision.storedCollision, Spec.HashCipher.hashView, decide_eq_true_eq]
    exact ⟨hlines, left.lines, hll, by simpa only [heq] using hrl⟩

theorem partial_source_middle_bounded {Error : Type*} (category : Spec.FieldRepresentation.Category) {tau kappa s : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s) (plain : Fin s → ZMod 2)
    (base : Digest (Spec.FieldRepresentation.width category) → ChainProgram (Spec.FieldRepresentation.width category) Key Block
      (Except Error (Fin s → Fin tau → Fin kappa → ZMod 2))) (m : Nat) (hm : ∀ answer, Bounded m (base answer))
    (auxiliary : Digest (Spec.FieldRepresentation.width category)) :
    Bounded m (partialSourceMiddle category encoding plain base auxiliary) :=
  HashCipherProgram.bounded_bind _ _ m 0 (hm auxiliary) (fun _ => trivial)

theorem partial_source_evaluates {Error : Type*} (category : Spec.FieldRepresentation.Category) {tau kappa s wit rnd : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s) (root : Digest (Spec.FieldRepresentation.width category))
    (corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2) (plain : Fin s → ZMod 2)
    (base : Digest (Spec.FieldRepresentation.width category) → ChainProgram (Spec.FieldRepresentation.width category) Key Block
      (Except Error (Fin s → Fin tau → Fin kappa → ZMod 2))) (family : Spec.IdealCipher.Family Key Block)
    (table : List Bool → Option (Digest (Spec.FieldRepresentation.width category))) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (value : Result (Spec.FieldRepresentation.width category))
    (h : Evaluates family table ciphers (partialSourceProgram category encoding root corrections plain base) (.ok value)) :
    ∃ matrix, Evaluates family table ciphers (base value.auxiliary) (.ok matrix) ∧
      table (Spec.BLCBinding.auxQuery category encoding ⟨root, corrections⟩) = some value.auxiliary ∧
      table (Spec.BLCBinding.linesQuery category encoding ⟨value.auxiliary, plain, matrix⟩) = some value.lines := by
  obtain ⟨ha, hm, hl⟩ := partial_evaluates family table ciphers root (sourceTail encoding corrections)
    (partialSourceMiddle category encoding plain base) value h
  obtain ⟨result, hb, ht⟩ :=
    (HashCipherEvaluation.evaluates_bind family table ciphers (base value.auxiliary)
      (fun result => .done (result.map (fun value => encoding.vector plain ++ encoding.base value)))
      (Except.ok value.tail)).mp hm
  have htail := done_eq family table ciphers _ _ ht
  cases result with
  | error cause => cases htail
  | ok matrix =>
    have he := Except.ok.inj htail
    rw [← he, source_lines_query] at hl
    exact ⟨matrix, hb, by simpa only [source_aux_query] using ha, hl⟩

end
end SDitH.Proofs.BLCHashChain
