import SDitH.Proofs.BAVCPrefill
import SDitH.Proofs.BAVCTrace

namespace SDitH.Proofs.BAVCReconstruction

open Spec.BAVC

theorem readNode_ok_iff {lambda tau N : Nat} (nodes : NodesBinding lambda tau N)
    (i : NodeAddress tau N) (seed : Seed lambda) :
    readNode nodes i = .ok seed ↔ ∃ values, nodes = some values ∧ values i = some seed := by
  cases nodes with
  | none => simp [readNode]
  | some values =>
    cases hv : values i <;> simp [readNode, hv]

theorem expandPartialStep_empty_tree {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (nodes : NodesBinding lambda tau N) (i : Fin (tau * N - 1)) :
    expandPartialStep p salt (fun _ => none) nodes i = .ok nodes := rfl

theorem expandPartialThrough_empty_tree {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (nodes : NodesBinding lambda tau N) (count : Nat) (hc : count ≤ tau * N - 1) :
    expandPartialThrough p salt (fun _ => none) nodes count hc = .ok nodes := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [expandPartialThrough, ih, Bind.bind, Except.bind, expandPartialStep_empty_tree]

/-- The printed step cannot create a binding for the undeclared nodes array:
its first attempted use is a read on the right side of the assignment. -/
theorem expandPartialStep_unbound {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (tree : PartialTree lambda tau N) (i : Fin (tau * N - 1)) (out : NodesBinding lambda tau N)
    (h : expandPartialStep p salt tree none i = .ok out) : out = none := by
  cases ht : tree (internalNode i) <;> simp [expandPartialStep, ht] at h
  exact h.symm

theorem expandPartialThrough_unbound {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (tree : PartialTree lambda tau N) (count : Nat) (hc : count ≤ tau * N - 1)
    (out : NodesBinding lambda tau N)
    (h : expandPartialThrough p salt tree none count hc = .ok out) : out = none := by
  induction count generalizing out with
  | zero => simpa only [expandPartialThrough, Except.ok.injEq] using h.symm
  | succ count ih =>
    obtain ⟨previous, hp, hs⟩ := (bind_ok_iff _ _ out).mp h
    have he := ih (by omega) previous hp
    subst previous
    exact expandPartialStep_unbound p salt tree _ out hs

theorem reconstructLeaf_hidden {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau)
    (nodes : NodesBinding lambda tau N) (e : Fin tau) :
    reconstructLeaf p salt hidden opening nodes e (hidden e) =
      .ok ⟨none, opening.hiddenCommitments e⟩ := by simp [reconstructLeaf]

theorem reconstructLeaf_revealed {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau)
    (nodes : NodesBinding lambda tau N) (e : Fin tau) (i : Fin N) (hi : i ≠ hidden e)
    (out : ReconstructedLeaf lambda) (h : reconstructLeaf p salt hidden opening nodes e i = .ok out) :
    ∃ seed, readNode nodes (leafNode e i) = .ok seed ∧
      out = ⟨some seed, p.commitSeed salt seed (Spec.SeedTree.leafOffset e i)⟩ := by
  rw [reconstructLeaf, if_neg hi] at h
  obtain ⟨seed, hs, ho⟩ := (bind_ok_iff _ _ out).mp h
  exact ⟨seed, hs, Except.ok.inj ho.symm⟩

/-- Every successful row entry is the actual corresponding leaf computation,
proved from the increasing loop and its length-indexed pushes. -/
theorem reconstructRow_coordinate {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau)
    (nodes : NodesBinding lambda tau N) (e : Fin tau) (count : Nat) (hc : count ≤ N)
    (out : Vector (ReconstructedLeaf lambda) count)
    (h : reconstructRowThrough p salt hidden opening nodes e count hc = .ok out)
    (j : Nat) (hj : j < count) :
    reconstructLeaf p salt hidden opening nodes e ⟨j, hj.trans_le hc⟩ = .ok out[j] := by
  induction count with
  | zero => omega
  | succ count ih =>
    obtain ⟨previous, hp, hs⟩ := (bind_ok_iff _ _ out).mp h
    obtain ⟨last, hl, ho⟩ := (bind_ok_iff _ _ out).mp hs
    have he : previous.push last = out := Except.ok.inj ho
    subst out
    by_cases hlt : j < count
    · rw [Vector.getElem_push_lt hlt]
      exact ih (by omega) previous hp hlt
    · have heq : j = count := by omega
      subst j
      rw [Vector.getElem_push_eq]
      exact hl

theorem reconstructRows_coordinate {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (count : Nat) (hc : count ≤ tau) (out : Vector (Vector (ReconstructedLeaf lambda) N) count)
    (h : reconstructRowsThrough p salt hidden opening nodes count hc = .ok out)
    (e : Nat) (he : e < count) :
    reconstructRowThrough p salt hidden opening nodes ⟨e, he.trans_le hc⟩ N le_rfl = .ok out[e] := by
  induction count with
  | zero => omega
  | succ count ih =>
    obtain ⟨previous, hp, hs⟩ := (bind_ok_iff _ _ out).mp h
    obtain ⟨last, hl, ho⟩ := (bind_ok_iff _ _ out).mp hs
    have heq : previous.push last = out := Except.ok.inj ho
    subst out
    by_cases hlt : e < count
    · rw [Vector.getElem_push_lt hlt]
      exact ih (by omega) previous hp hlt
    · have heq : e = count := by omega
      subst e
      rw [Vector.getElem_push_eq]
      exact hl

theorem exists_revealed_index {N : Nat} (hn : 1 < N) (hidden : Fin N) : ∃ i : Fin N, i ≠ hidden := by
  by_cases hz : hidden.val = 0
  · refine ⟨⟨1, hn⟩, ?_⟩
    intro he
    have hv := congrArg Fin.val he
    change 1 = hidden.val at hv
    omega
  · refine ⟨⟨0, by omega⟩, ?_⟩
    intro he
    exact hz (congrArg Fin.val he).symm

/-- A nontrivial execution has a revealed leaf, so it cannot finish its row
without ever having a binding for nodes. No seed is fabricated for that read. -/
theorem reconstructRow_unbound {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (e : Fin tau) (hn : 1 < N)
    (out : Vector (ReconstructedLeaf lambda) N) :
    reconstructRowThrough p salt hidden opening none e N le_rfl ≠ .ok out := by
  intro h
  obtain ⟨i, hi⟩ := exists_revealed_index hn (hidden e)
  have hc := reconstructRow_coordinate p salt hidden opening none e N le_rfl out h i.val i.isLt
  simp [reconstructLeaf, hi, readNode, Bind.bind, Except.bind] at hc

theorem reconstructRows_unbound {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (ht : 0 < tau) (hn : 1 < N)
    (out : Vector (Vector (ReconstructedLeaf lambda) N) tau) :
    reconstructRowsThrough p salt hidden opening none tau le_rfl ≠ .ok out := by
  intro h
  have hr := reconstructRows_coordinate p salt hidden opening none tau le_rfl out h 0 ht
  exact reconstructRow_unbound p salt hidden opening ⟨0, ht⟩ hn out[0] hr

/-- For tau>0 and N>1 the full literal body cannot return a reconstruction
while nodes remains undeclared. It may reject earlier, or reach an undefined
read. This does not insert a correction or assert a rejection-only behavior. -/
theorem reconstruct_undeclared_no_return {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat)
    (ht : 0 < tau) (hn : 1 < N) (out : Reconstructed lambda tau N) :
    reconstruct p salt hidden opening Topen ≠ .ok out := by
  intro h
  obtain ⟨tree, _, hexpand⟩ := (bind_ok_iff _ _ out).mp h
  obtain ⟨nodes, hnrun, hrows⟩ := (bind_ok_iff _ _ out).mp hexpand
  have he := expandPartialThrough_unbound p salt tree _ le_rfl nodes hnrun
  subst nodes
  obtain ⟨rows, hr, _⟩ := (bind_ok_iff _ _ out).mp hrows
  exact reconstructRows_unbound p salt hidden opening ht hn rows hr

theorem reconstructWithNodes_ok_iff {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat)
    (initial : NodesBinding lambda tau N) (out : Reconstructed lambda tau N) :
    reconstructWithNodes p salt hidden opening Topen initial = .ok out ↔
      ∃ tree nodes rows,
        prefill hidden opening Topen = .ok tree ∧
        expandPartialThrough p salt tree initial (tau * N - 1) le_rfl = .ok nodes ∧
        reconstructRowsThrough p salt hidden opening nodes tau le_rfl = .ok rows ∧
        out = reconstructionHashes p salt rows := by
  constructor
  · intro h
    obtain ⟨tree, ht, hexpand⟩ := (bind_ok_iff _ _ out).mp h
    obtain ⟨nodes, hn, hrows⟩ := (bind_ok_iff _ _ out).mp hexpand
    obtain ⟨rows, hr, ho⟩ := (bind_ok_iff _ _ out).mp hrows
    exact ⟨tree, nodes, rows, ht, hn, hr, Except.ok.inj ho.symm⟩
  · rintro ⟨tree, nodes, rows, ht, hn, hr, rfl⟩
    simp only [reconstructWithNodes, ht, Bind.bind, Except.bind, hn, hr]

theorem successful_rows_hidden {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (rows : Vector (Vector (ReconstructedLeaf lambda) N) tau)
    (hr : reconstructRowsThrough p salt hidden opening nodes tau le_rfl = .ok rows) (e : Fin tau) :
    rows[e][hidden e] = ⟨none, opening.hiddenCommitments e⟩ := by
  have hrow := reconstructRows_coordinate p salt hidden opening nodes tau le_rfl rows hr e.val e.isLt
  have hleaf := reconstructRow_coordinate p salt hidden opening nodes e N le_rfl rows[e] hrow
    (hidden e).val (hidden e).isLt
  exact Except.ok.inj (hleaf.symm.trans (reconstructLeaf_hidden p salt hidden opening nodes e))

theorem successful_rows_revealed {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (rows : Vector (Vector (ReconstructedLeaf lambda) N) tau)
    (hr : reconstructRowsThrough p salt hidden opening nodes tau le_rfl = .ok rows)
    (e : Fin tau) (i : Fin N) (hi : i ≠ hidden e) :
    ∃ seed, readNode nodes (leafNode e i) = .ok seed ∧
      rows[e][i] = ⟨some seed, p.commitSeed salt seed (Spec.SeedTree.leafOffset e i)⟩ := by
  have hrow := reconstructRows_coordinate p salt hidden opening nodes tau le_rfl rows hr e.val e.isLt
  have hleaf := reconstructRow_coordinate p salt hidden opening nodes e N le_rfl rows[e] hrow i.val i.isLt
  exact reconstructLeaf_revealed p salt hidden opening nodes e i hi rows[e][i] hleaf

theorem reconstructed_hidden_absent {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat)
    (initial : NodesBinding lambda tau N) (out : Reconstructed lambda tau N)
    (h : reconstructWithNodes p salt hidden opening Topen initial = .ok out) (e : Fin tau) :
    out.seeds e (hidden e) = none := by
  obtain ⟨_, nodes, rows, _, _, hr, rfl⟩ := (reconstructWithNodes_ok_iff p salt hidden opening Topen initial out).mp h
  exact congrArg ReconstructedLeaf.seed (successful_rows_hidden p salt hidden opening nodes rows hr e)

/-- At the padded length, a successful run cannot expand any prefilled seed.
Its revealed values must all come from the externally supplied nodes binding.
This describes the literal loop, without asserting that such a binding exists. -/
theorem padded_reconstruct_iff {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat)
    (initial : NodesBinding lambda tau N) (out : Reconstructed lambda tau N)
    (hlong : Topen * lambda ≤ opening.path.length) :
    reconstructWithNodes p salt hidden opening Topen initial = .ok out ↔
      ∃ rows, prefill hidden opening Topen = .ok (fun _ => none) ∧
        reconstructRowsThrough p salt hidden opening initial tau le_rfl = .ok rows ∧
        out = reconstructionHashes p salt rows := by
  constructor
  · intro h
    obtain ⟨tree, nodes, rows, hp, he, hr, ho⟩ := (reconstructWithNodes_ok_iff p salt hidden opening Topen initial out).mp h
    have ht := (padded_prefill_success hidden opening Topen tree hlong hp).1
    subst tree
    have hn : nodes = initial := Except.ok.inj
      (he.symm.trans (expandPartialThrough_empty_tree p salt initial _ le_rfl))
    subst nodes
    exact ⟨rows, hp, hr, ho⟩
  · rintro ⟨rows, hp, hr, rfl⟩
    simp only [reconstructWithNodes, hp, Bind.bind, Except.bind, expandPartialThrough_empty_tree, hr]

/-- Undeclared variables are only diagnosed when read: in the single-leaf
case every leaf is hidden, so the full body returns without accessing nodes.
This is a degenerate parameter case, not a submitted parameter row. -/
theorem single_hidden_leaf_returns {lambda : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (commitment : Digest lambda) (Topen : Nat) :
    reconstruct p salt (fun _ : Fin 1 => (0 : Fin 1))
      ⟨List.replicate (Topen * lambda) false, fun _ => commitment⟩ Topen =
      .ok { hcom := hashBavc p (List.ofFn salt ++ List.ofFn (hashBavc p (List.ofFn commitment)))
            seeds := fun _ _ => none } := by
  simp [reconstruct, reconstructWithNodes, prefill, openingQueue, Spec.SeedTree.leafAddress,
    Spec.SeedTree.leafOffset, prefillLoop.eq_def, expandPartialThrough, reconstructRowsThrough,
    reconstructRowThrough, reconstructLeaf, reconstructionHashes, serializeArray, Bind.bind, Except.bind]

/-- The complete submitted-parameter trace reaches Algorithm 9's explicit
capacity rejection before any access to the undeclared nodes variable.
This result therefore holds for every supplied binding, cipher and hash. -/
theorem categoryI_full_rejection (key : Key 128 11 2048) (p : Primitives 128) (salt : Seed 128)
    (initial : NodesBinding 128 11 2048) :
    reconstructWithNodes p salt BAVC.categoryIHidden (BAVC.categoryIOpening key) 109 initial =
      .error .boundRejected := by
  have hlen := BAVC.openCommitment_path_length key BAVC.categoryIHidden 109 (by decide)
    (BAVC.categoryIOpening key) (BAVC.categoryI_open_succeeds key)
  have hpre : prefillLoop (lambda := 128) (tau := 11) (N := 2048)
      109 (openingQueue BAVC.categoryIHidden) (BAVC.categoryIOpening key).path
      (fun _ => none) = .error ReconstructionError.boundRejected := by
    rw [BAVC.categoryI_queue, prefillLoop.eq_def]
    norm_num [hlen, BAVC.sibling_formula]
  simp only [reconstructWithNodes, prefill, hpre, Bind.bind, Except.bind]

end SDitH.Proofs.BAVCReconstruction
