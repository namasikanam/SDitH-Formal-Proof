import SDitH.Proofs.BAVCReconstructionProgram

/-! Every revealed seed's actual commitment calls occur in the final cipher
graph of the ordered reconstruction. This discharges source query coverage
from execution, including repeated and previously absent calls. -/

namespace SDitH.Proofs.BAVCReconstructionCoverage

open Spec.BAVC Spec.BAVCCipherProgram Spec.HashCipherProgram Spec.HashCipherEvaluation
open Spec.IdealCipher

variable {lambda tau N : Nat} {Key Block A B : Type*}

theorem cipher_bindExcept (family : Family Key Block) (table : List Bool → Option (Digest lambda))
    (ciphers : List (Entry Key Block)) (program : CipherProgram Key Block (Except ReconstructionError A))
    (next : A → CipherProgram Key Block (Except ReconstructionError B)) (result : Except ReconstructionError B) :
    Evaluates family table ciphers (liftCipher (Spec.BAVCCipherProgram.bindExcept program next)) result ↔
      ∃ middle, Evaluates family table ciphers (liftCipher program) middle ∧
        match middle with
        | .error cause => result = .error cause
        | .ok value => Evaluates family table ciphers (liftCipher (next value)) result := by
  rw [Spec.BAVCCipherProgram.bindExcept, HashCipherEvaluation.liftCipher_bind, HashCipherEvaluation.evaluates_bind]
  constructor
  · rintro ⟨middle, hm, ht⟩
    refine ⟨middle, hm, ?_⟩
    cases middle with
    | error cause => cases ht; rfl
    | ok value => exact ht
  · rintro ⟨middle, hm, ht⟩
    refine ⟨middle, hm, ?_⟩
    cases middle with
    | error cause => subst result; exact .done _
    | ok value => exact ht

theorem expand_calls (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (table : List Bool → Option (Digest lambda)) (ciphers : List (Entry Key Block))
    (salt : Seed lambda) (address : Nat) (seed : Seed lambda) (result : Seed lambda × Seed lambda)
    (h : Evaluates family table ciphers (liftCipher (expandProgram layout variant salt address seed)) result) :
    ∀ side : Bool, entry (.encrypt (layout.key seed) (layout.input (Spec.SeedPrimitives.cipherInput variant salt address side)))
      (family (layout.key seed) (layout.input (Spec.SeedPrimitives.cipherInput variant salt address side))) ∈ ciphers := by
  cases h with
  | cipher _ _ _ hl ht =>
    cases ht with
    | cipher _ _ _ hr ht =>
      intro side
      cases side
      · exact hl
      · exact hr

theorem commit_calls (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (table : List Bool → Option (Digest lambda)) (ciphers : List (Entry Key Block))
    (leafCount : Nat) (salt seed : Seed lambda) (index : Nat) (result : Digest lambda)
    (h : Evaluates family table ciphers (liftCipher (commitProgram layout leafCount variant salt seed index)) result) :
    ∀ side : Bool, entry (.encrypt (layout.key seed) (layout.input (Spec.SeedPrimitives.cipherInput variant salt (leafCount + index) side)))
      (family (layout.key seed) (layout.input (Spec.SeedPrimitives.cipherInput variant salt (leafCount + index) side))) ∈ ciphers := by
  rw [commitProgram, Spec.OracleProgram.map, HashCipherEvaluation.liftCipher_bind,
    HashCipherEvaluation.evaluates_bind] at h
  obtain ⟨pair, hp, _⟩ := h
  exact expand_calls layout variant family table ciphers salt (leafCount + index) seed pair hp

theorem leaf_calls (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (table : List Bool → Option (Digest lambda)) (ciphers : List (Entry Key Block))
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (e : Fin tau) (i : Fin N) (leaf : ReconstructedLeaf lambda)
    (h : Evaluates family table ciphers (liftCipher (leafProgram layout variant salt hidden opening nodes e i)) (.ok leaf))
    (seed : Seed lambda) (hs : leaf.seed = some seed) :
    ∀ side : Bool, entry (.encrypt (layout.key seed)
      (layout.input (Spec.SeedPrimitives.cipherInput variant salt (tau * N + Spec.SeedTree.leafOffset e i) side)))
      (family (layout.key seed) (layout.input (Spec.SeedPrimitives.cipherInput variant salt (tau * N + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers := by
  unfold leafProgram at h
  split at h
  · cases h
    contradiction
  · cases hr : readNode nodes (leafNode e i) with
    | error cause => rw [hr] at h; cases h
    | ok stored =>
      rw [hr] at h
      dsimp only at h
      rw [Spec.OracleProgram.map, HashCipherEvaluation.liftCipher_bind,
        HashCipherEvaluation.evaluates_bind] at h
      obtain ⟨digest, hd, ht⟩ := h
      cases ht
      have he : stored = seed := Option.some.inj hs
      subst seed
      exact commit_calls layout variant family table ciphers (tau * N) salt stored (Spec.SeedTree.leafOffset e i) digest hd

theorem row_calls (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (table : List Bool → Option (Digest lambda)) (ciphers : List (Entry Key Block))
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (e : Fin tau) (count : Nat) (hc : count ≤ N) (row : Vector (ReconstructedLeaf lambda) count)
    (h : Evaluates family table ciphers (liftCipher (rowThrough layout variant salt hidden opening nodes e count hc)) (.ok row))
    (i : Nat) (hi : i < count) (seed : Seed lambda) (hs : row[i].seed = some seed) :
    ∀ side : Bool, entry (.encrypt (layout.key seed)
      (layout.input (Spec.SeedPrimitives.cipherInput variant salt (tau * N + Spec.SeedTree.leafOffset e ⟨i, hi.trans_le hc⟩) side)))
      (family (layout.key seed) (layout.input (Spec.SeedPrimitives.cipherInput variant salt (tau * N + Spec.SeedTree.leafOffset e ⟨i, hi.trans_le hc⟩) side))) ∈ ciphers := by
  induction count with
  | zero => omega
  | succ count ih =>
    obtain ⟨previous, hp, ht⟩ := (cipher_bindExcept family table ciphers _ _ (.ok row)).mp h
    cases previous with
    | error cause => cases ht
    | ok previous =>
      obtain ⟨last, hl, ht⟩ := (cipher_bindExcept family table ciphers _ _ (.ok row)).mp ht
      cases last with
      | error cause => cases ht
      | ok last =>
        cases ht
        by_cases hlt : i < count
        · rw [Vector.getElem_push_lt hlt] at hs
          exact ih (by omega) previous hp hlt hs
        · have heq : i = count := by omega
          subst i
          rw [Vector.getElem_push_eq] at hs
          exact leaf_calls layout variant family table ciphers salt hidden opening nodes e ⟨count, by omega⟩ last hl seed hs

theorem rows_calls (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (table : List Bool → Option (Digest lambda)) (ciphers : List (Entry Key Block))
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (count : Nat) (hc : count ≤ tau) (rows : Spec.BAVCReconstructionProgram.Rows lambda N count)
    (h : Evaluates family table ciphers (Spec.BAVCReconstructionProgram.rowsThrough layout variant salt hidden opening nodes count hc) (.ok rows))
    (e : Nat) (he : e < count) (i : Fin N) (seed : Seed lambda) (hs : rows.leaves[e][i].seed = some seed) :
    ∀ side : Bool, entry (.encrypt (layout.key seed)
      (layout.input (Spec.SeedPrimitives.cipherInput variant salt (tau * N + Spec.SeedTree.leafOffset ⟨e, he.trans_le hc⟩ i) side)))
      (family (layout.key seed) (layout.input (Spec.SeedPrimitives.cipherInput variant salt (tau * N + Spec.SeedTree.leafOffset ⟨e, he.trans_le hc⟩ i) side))) ∈ ciphers := by
  induction count with
  | zero => omega
  | succ count ih =>
    obtain ⟨previous, hp, ht⟩ := (BAVCReconstructionProgram.evaluates_bindExcept family table ciphers _ _ (.ok rows)).mp h
    cases previous with
    | error cause => cases ht
    | ok previous =>
      obtain ⟨row, hr, ht⟩ := (BAVCReconstructionProgram.evaluates_bindExcept family table ciphers _ _ (.ok rows)).mp ht
      cases row with
      | error cause => cases ht
      | ok row =>
        cases ht with
        | hash _ _ digest _ _ hd =>
          cases hd
          by_cases hlt : e < count
          · rw [Vector.getElem_push_lt hlt] at hs
            exact ih (by omega) previous hp hlt hs
          · have heq : e = count := by omega
            subst e
            rw [Vector.getElem_push_eq] at hs
            exact row_calls layout variant family table ciphers salt hidden opening nodes ⟨count, by omega⟩ N le_rfl row hr i.val i.isLt seed hs

theorem reconstruction_calls (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (table : List Bool → Option (Digest lambda)) (ciphers : List (Entry Key Block))
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat) (initial : NodesBinding lambda tau N)
    (result : Reconstructed lambda tau N)
    (h : Evaluates family table ciphers (Spec.BAVCReconstructionProgram.reconstruct layout variant salt hidden opening Topen initial) (.ok result))
    (e : Fin tau) (i : Fin N) (seed : Seed lambda) (hs : result.seeds e i = some seed) :
    ∀ side : Bool, entry (.encrypt (layout.key seed)
      (layout.input (Spec.SeedPrimitives.cipherInput variant salt (tau * N + Spec.SeedTree.leafOffset e i) side)))
      (family (layout.key seed) (layout.input (Spec.SeedPrimitives.cipherInput variant salt (tau * N + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers := by
  unfold Spec.BAVCReconstructionProgram.reconstruct at h
  cases hp : prefill hidden opening Topen with
  | error cause => rw [hp] at h; cases h
  | ok tree =>
    rw [hp] at h
    obtain ⟨nodes, _, ht⟩ := (BAVCReconstructionProgram.evaluates_bindExcept family table ciphers _ _ (.ok result)).mp h
    cases nodes with
    | error cause => cases ht
    | ok nodes =>
      obtain ⟨rows, hr, ht⟩ := (BAVCReconstructionProgram.evaluates_bindExcept family table ciphers _ _ (.ok result)).mp ht
      cases rows with
      | error cause => cases ht
      | ok rows =>
        cases ht with
        | hash _ _ root _ _ hd =>
          cases hd
          exact rows_calls layout variant family table ciphers salt hidden opening nodes tau le_rfl rows hr e.val e.isLt i seed hs

end SDitH.Proofs.BAVCReconstructionCoverage
