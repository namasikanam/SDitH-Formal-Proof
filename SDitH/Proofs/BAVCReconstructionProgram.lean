import SDitH.Spec.BAVCReconstructionProgram
import SDitH.Proofs.HashCipherEvaluation
import SDitH.Proofs.BAVCCipherProgram
import SDitH.Proofs.BAVCBindingReconstruction

namespace SDitH.Proofs.BAVCReconstructionProgram

open Spec.BAVC Spec.BAVCReconstructionProgram Spec.HashCipherProgram Spec.HashCipherEvaluation

variable {lambda tau N : Nat} {Key Block A B : Type*}

theorem bounded_bindExcept (program : ReconstructionProgram lambda Key Block (Except ReconstructionError A))
    (next : A → ReconstructionProgram lambda Key Block (Except ReconstructionError B)) (q k : Nat)
    (hp : Bounded q program) (hn : ∀ a, Bounded k (next a)) : Bounded (q + k) (bindExcept program next) := by
  apply HashCipherProgram.bounded_bind _ _ q k hp
  intro value
  cases value with
  | error cause => cases k <;> trivial
  | ok value => exact hn value

theorem evaluates_bindExcept (family : Spec.IdealCipher.Family Key Block)
    (table : List Bool → Option (Digest lambda)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (program : ReconstructionProgram lambda Key Block (Except ReconstructionError A))
    (next : A → ReconstructionProgram lambda Key Block (Except ReconstructionError B)) (result : Except ReconstructionError B) :
    Evaluates family table ciphers (bindExcept program next) result ↔
      ∃ middle, Evaluates family table ciphers program middle ∧
        match middle with
        | .error cause => result = .error cause
        | .ok value => Evaluates family table ciphers (next value) result := by
  rw [bindExcept, HashCipherEvaluation.evaluates_bind]
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

theorem rows_bounded (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (count : Nat) (hc : count ≤ tau) :
    Bounded ((2 * N + 1) * count) (rowsThrough layout variant salt hidden opening nodes count hc) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    rw [Nat.mul_add, Nat.mul_one]
    apply bounded_bindExcept _ _ ((2 * N + 1) * count) (2 * N + 1) (ih (by omega))
    intro rows
    exact bounded_bindExcept _ _ (2 * N) 1
      (HashCipherProgram.bounded_liftCipher _ _ (BAVCCipherProgram.row_bounded layout variant salt hidden opening nodes ⟨count, by omega⟩ N le_rfl))
      (fun _ _ => trivial)

theorem reconstruction_bounded (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat) (initial : NodesBinding lambda tau N) :
    Bounded (budget tau N) (Spec.BAVCReconstructionProgram.reconstruct layout variant salt hidden opening Topen initial) := by
  unfold Spec.BAVCReconstructionProgram.reconstruct
  cases prefill hidden opening Topen with
  | error cause => cases budget tau N <;> trivial
  | ok tree =>
    rw [budget, Nat.add_assoc]
    apply bounded_bindExcept _ _ (2 * (tau * N - 1)) ((2 * N + 1) * tau + 1)
      (HashCipherProgram.bounded_liftCipher _ _ (BAVCCipherProgram.expansion_bounded layout variant salt tree initial (tau * N - 1) le_rfl))
    intro nodes
    exact bounded_bindExcept _ _ ((2 * N + 1) * tau) 1
      (rows_bounded layout variant salt hidden opening nodes tau le_rfl) (fun _ _ => trivial)

theorem covered_push (table : List Bool → Option (Digest lambda)) {count : Nat} (rows : Rows lambda N count)
    (row : Vector (ReconstructedLeaf lambda) N) (digest : Digest lambda)
    (hr : RowsCovered table rows) (hd : table (rowInput row) = some digest) :
    RowsCovered table (⟨rows.leaves.push row, rows.hashes.push digest⟩ : Rows lambda N (count + 1)) := by
  intro e
  change table (rowInput (rows.leaves.push row)[e.val]) = some (rows.hashes.push digest)[e.val]
  by_cases he : e.val < count
  · simpa only [Vector.getElem_push_lt he] using hr ⟨e.val, he⟩
  · have heq : e.val = count := by have hi := e.isLt; omega
    simpa only [heq, Vector.getElem_push_eq] using hd

theorem rows_evaluates (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Spec.IdealCipher.Family Key Block) (table : List Bool → Option (Digest lambda))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (count : Nat) (hc : count ≤ tau) (result : Except ReconstructionError (Rows lambda N count))
    (h : Evaluates family table ciphers (rowsThrough layout variant salt hidden opening nodes count hc) result) :
    match result with
    | .error cause => reconstructRowsThrough (primitives (tau := tau) (N := N) layout variant family table) salt hidden opening nodes count hc = .error cause
    | .ok rows => reconstructRowsThrough (primitives (tau := tau) (N := N) layout variant family table) salt hidden opening nodes count hc = .ok rows.leaves ∧
        RowsCovered table rows := by
  induction count with
  | zero =>
    cases h
    exact ⟨rfl, fun e => Fin.elim0 e⟩
  | succ count ih =>
    obtain ⟨earlier, he, ht⟩ := (evaluates_bindExcept family table ciphers _ _ result).mp h
    have hi := ih (by omega) earlier he
    cases earlier with
    | error cause =>
      subst result
      simp only [reconstructRowsThrough, hi, Bind.bind, Except.bind]
    | ok earlier =>
      obtain ⟨rowResult, hr, ht⟩ := (evaluates_bindExcept family table ciphers _ _ result).mp ht
      have hv := HashCipherEvaluation.liftCipher_value family table ciphers _ _ hr []
      rw [BAVCCipherProgram.row_value layout variant family (fun input => (table input).getD (fun _ => false))] at hv
      change reconstructRowThrough (primitives (tau := tau) (N := N) layout variant family table) salt hidden opening nodes ⟨count, by omega⟩ N le_rfl = rowResult at hv
      cases rowResult with
      | error cause =>
        subst result
        simp only [reconstructRowsThrough, hi.1, hv, Bind.bind, Except.bind]
      | ok row =>
        cases ht with
        | hash _ _ digest _ stored hd =>
          cases hd
          exact ⟨by simp only [reconstructRowsThrough, hi.1, hv, Bind.bind, Except.bind], covered_push table earlier row digest hi.2 stored⟩

/-- Coverage forces the stored row digests to be exactly the hash equations
used by the source. The fallback value is irrelevant at every queried input. -/
theorem covered_hashes (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Spec.IdealCipher.Family Key Block) (table : List Bool → Option (Digest lambda))
    (rows : Rows lambda N tau) (h : RowsCovered table rows) :
    (fun e : Fin tau => rows.hashes[e]) =
      (fun e : Fin tau => hashBavc (primitives (tau := tau) (N := N) layout variant family table)
        (serializeArray fun i : Fin N => rows.leaves[e][i].commitment)) := by
  funext e
  change rows.hashes[e] = (table (rowInput rows.leaves[e])).getD (fun _ => false)
  rw [h e]
  rfl

theorem finish_evaluates (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Spec.IdealCipher.Family Key Block) (table : List Bool → Option (Digest lambda))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (salt : Seed lambda) (rows : Rows lambda N tau)
    (hr : RowsCovered table rows) (result : Except ReconstructionError (Reconstructed lambda tau N))
    (h : Evaluates family table ciphers (finish salt rows) result) :
    result = .ok (reconstructionHashes (primitives (tau := tau) (N := N) layout variant family table) salt rows.leaves) ∧
      Spec.BAVCBindingROM.observed (primitives (tau := tau) (N := N) layout variant family table) table salt
        (Spec.BAVCBinding.rowCommitments rows.leaves) = true := by
  cases h with
  | hash _ _ root _ stored ht =>
    cases ht
    have hhash := covered_hashes layout variant family table rows hr
    have houter : table (Spec.BAVCBinding.outerQuery (primitives (tau := tau) (N := N) layout variant family table)
        salt (Spec.BAVCBinding.rowCommitments rows.leaves)) = some root := by
      simpa only [outerInput, hhash, Spec.BAVCBinding.outerQuery, Spec.BAVCBinding.rowCommitments,
        Spec.BAVCBinding.rowQuery, hashBavc] using stored
    refine ⟨?_, ?_⟩
    · have hroot : root = hashBavc (primitives (tau := tau) (N := N) layout variant family table)
          (List.ofFn salt ++ serializeArray (fun e : Fin tau => hashBavc
            (primitives (tau := tau) (N := N) layout variant family table)
            (serializeArray fun i : Fin N => rows.leaves[e][i].commitment))) := by
        change root = (table (Spec.BAVCBinding.outerQuery (primitives (tau := tau) (N := N) layout variant family table)
          salt (Spec.BAVCBinding.rowCommitments rows.leaves))).getD (fun _ => false)
        rw [houter]
        rfl
      exact congrArg (fun digest => Except.ok (Reconstructed.mk digest (fun e i => rows.leaves[e][i].seed))) hroot
    · apply List.all_eq_true.mpr
      intro input hin
      simp only [Spec.BAVCBinding.hashQueries, List.mem_append, List.mem_ofFn, List.mem_singleton] at hin
      rcases hin with ⟨e, rfl⟩ | rfl
      · change (table (rowInput rows.leaves[e])).isSome = true
        rw [hr e]
        rfl
      · change (table (Spec.BAVCBinding.outerQuery (primitives (tau := tau) (N := N) layout variant family table)
          salt (Spec.BAVCBinding.rowCommitments rows.leaves))).isSome = true
        rw [houter]
        rfl

/-- The ordered query program agrees with the staged source value, including
every error. Successful returns additionally expose the actual stored hash
coverage; this is a consequence of evaluation, not an acceptance condition. -/
theorem reconstruction_evaluates (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Spec.IdealCipher.Family Key Block) (table : List Bool → Option (Digest lambda))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat) (initial : NodesBinding lambda tau N)
    (result : Except ReconstructionError (Reconstructed lambda tau N))
    (h : Evaluates family table ciphers (Spec.BAVCReconstructionProgram.reconstruct layout variant salt hidden opening Topen initial) result) :
    reconstructWithNodes (primitives (tau := tau) (N := N) layout variant family table) salt hidden opening Topen initial = result ∧
      ∀ value, result = .ok value → ∃ rows,
        Spec.BAVCBinding.reconstructionRows (primitives (tau := tau) (N := N) layout variant family table) salt hidden opening Topen initial = .ok rows ∧
        value = reconstructionHashes (primitives (tau := tau) (N := N) layout variant family table) salt rows ∧
        Spec.BAVCBindingROM.observed (primitives (tau := tau) (N := N) layout variant family table) table salt (Spec.BAVCBinding.rowCommitments rows) = true := by
  unfold Spec.BAVCReconstructionProgram.reconstruct at h
  cases hp : prefill hidden opening Topen with
  | error cause =>
    rw [hp] at h
    cases h
    refine ⟨by simp only [reconstructWithNodes, hp, Bind.bind, Except.bind], ?_⟩
    intro value hv
    cases hv
  | ok tree =>
    rw [hp] at h
    obtain ⟨nodesResult, hn, ht⟩ := (evaluates_bindExcept family table ciphers _ _ result).mp h
    have he := HashCipherEvaluation.liftCipher_value family table ciphers _ _ hn []
    rw [BAVCCipherProgram.expansion_value layout variant family (fun input => (table input).getD (fun _ => false))] at he
    change expandPartialThrough (primitives (tau := tau) (N := N) layout variant family table) salt tree initial (tau * N - 1) le_rfl = nodesResult at he
    cases nodesResult with
    | error cause =>
      subst result
      refine ⟨by simp only [reconstructWithNodes, hp, he, Bind.bind, Except.bind], ?_⟩
      intro value hv
      cases hv
    | ok nodes =>
      obtain ⟨rowsResult, hr, ht⟩ := (evaluates_bindExcept family table ciphers _ _ result).mp ht
      have hv := rows_evaluates layout variant family table ciphers salt hidden opening nodes tau le_rfl rowsResult hr
      cases rowsResult with
      | error cause =>
        subst result
        refine ⟨by simp only [reconstructWithNodes, hp, he, hv, Bind.bind, Except.bind], ?_⟩
        intro value hv
        cases hv
      | ok rows =>
        obtain ⟨hresult, hcoverage⟩ := finish_evaluates layout variant family table ciphers salt rows hv.2 result ht
        refine ⟨?_, ?_⟩
        · simpa only [reconstructWithNodes, hp, he, hv.1, Bind.bind, Except.bind] using hresult.symm
        · intro value hout
          exact ⟨rows.leaves, by simp only [Spec.BAVCBinding.reconstructionRows, hp, he, hv.1, Bind.bind, Except.bind],
            Except.ok.inj (hout.symm.trans hresult), hcoverage⟩

/-- Every supported execution terminates at the source result. Errors are
explicit results too. The budget counts all repeated and newly made calls. -/
theorem run_complete (layout : Spec.BAVCCipherProgram.Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Spec.IdealCipher.Family Key Block) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat) (initial : NodesBinding lambda tau N)
    (table : List Bool → Option (Digest lambda)) (hashes : List (List Bool × Digest lambda))
    (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (out : Spec.HashCipher.Result (List Bool) (Digest lambda) Key Block
      (ReconstructionProgram lambda Key Block (Except ReconstructionError (Reconstructed lambda tau N))))
    (hout : out ∈ (Spec.HashCipher.runFixed procedure family (budget tau N)
      (Spec.BAVCReconstructionProgram.reconstruct layout variant salt hidden opening Topen initial) table hashes ciphers).support) :
    ∃ result, out.state = .done result ∧
      Evaluates family out.hashTable out.cipherHistory (Spec.BAVCReconstructionProgram.reconstruct layout variant salt hidden opening Topen initial) result ∧
      reconstructWithNodes (primitives (tau := tau) (N := N) layout variant family out.hashTable) salt hidden opening Topen initial = result ∧
      ∀ value, result = .ok value → ∃ rows,
        Spec.BAVCBinding.reconstructionRows (primitives (tau := tau) (N := N) layout variant family out.hashTable) salt hidden opening Topen initial = .ok rows ∧
        value = reconstructionHashes (primitives (tau := tau) (N := N) layout variant family out.hashTable) salt rows ∧
        Spec.BAVCBindingROM.observed (primitives (tau := tau) (N := N) layout variant family out.hashTable) out.hashTable salt (Spec.BAVCBinding.rowCommitments rows) = true := by
  obtain ⟨result, hs, he⟩ := HashCipherEvaluation.run_evaluates family _ (budget tau N)
    (reconstruction_bounded layout variant salt hidden opening Topen initial) table hashes ciphers out hout
  exact ⟨result, hs, he, reconstruction_evaluates layout variant family out.hashTable out.cipherHistory salt hidden opening Topen initial result he⟩

end SDitH.Proofs.BAVCReconstructionProgram
