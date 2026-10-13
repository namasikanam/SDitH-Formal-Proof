import SDitH.Spec.BAVCReconstruction
import SDitH.Proofs.BAVCOpeningSafety

namespace SDitH.Proofs.BAVCReconstruction

open Spec.BAVC

universe u v

theorem bind_ok_iff {E : Type u} {A B : Type v} (first : Except E A) (next : A → Except E B) (out : B) :
    (first >>= next) = .ok out ↔ ∃ value, first = .ok value ∧ next value = .ok out := by
  cases first <;> simp [Bind.bind, Except.bind]

theorem pathSeed_take {lambda : Nat} (path : List Bool) (enough : lambda ≤ path.length) :
    List.ofFn (pathSeed path enough) = path.take lambda := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left enough]
  · intro j hj hk
    simp only [List.getElem_ofFn, pathSeed, List.getElem_take]

theorem pathSeed_reassembles {lambda : Nat} (path : List Bool) (enough : lambda ≤ path.length) :
    List.ofFn (pathSeed path enough) ++ path.drop lambda = path := by
  rw [pathSeed_take, List.take_append_drop]

/-- A path already at the printed upper bound can never enter the extraction
branch. If the queue traversal succeeds, it leaves all memory and bits unchanged.
This is proved for the full loop, not only its first sibling comparison. -/
theorem full_path_unchanged {lambda tau N : Nat} (Topen : Nat) (queue : List Nat)
    (path : List Bool) (tree : PartialTree lambda tau N) (out : Prefilled lambda tau N)
    (hlong : Topen * lambda ≤ path.length) (h : prefillLoop Topen queue path tree = .ok out) :
    out = ⟨tree, path⟩ := by
  induction queue, path, tree using prefillLoop.induct Topen generalizing out with
  | case1 path tree => simp [prefillLoop.eq_def] at h
  | case2 rest path tree => simpa [prefillLoop.eq_def] using h.symm
  | case3 j path tree hne hgt hlen => simp at hlen
  | case4 j path tree hne hgt tail sibling hlen ih =>
    dsimp only [sibling] at *
    rw [prefillLoop.eq_def] at h
    simp only [if_neg hne, if_pos hgt, if_pos hlen] at h
    exact ih out hlong h
  | case5 j path tree hne hgt k tail sibling hks hcap hs hp hlen ih => omega
  | case6 j path tree hne hgt k tail sibling hks hcap hs hp hlen => omega
  | case7 j path tree hne hgt k tail sibling hks hcap hs hlen => omega
  | case8 j path tree hne hgt k tail sibling hks hcap hlen =>
    dsimp only [sibling] at *
    rw [prefillLoop.eq_def] at h
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks, if_neg hcap] at h
    contradiction
  | case9 j rest path tree hne hgt hlen ih =>
    rw [prefillLoop.eq_def] at h
    simp only [if_neg hne, if_pos hgt, if_neg hlen] at h
    exact ih out hlong h
  | case10 j rest path tree hne hgt => simp [prefillLoop.eq_def, hne, hgt] at h

/-- Successful consumption removes an exact number of complete seeds, with
every removed bit in bounds. The remaining path is the actual suffix. -/
theorem prefill_consumption {lambda tau N : Nat} (Topen : Nat) (queue : List Nat)
    (path : List Bool) (tree : PartialTree lambda tau N) (out : Prefilled lambda tau N)
    (h : prefillLoop Topen queue path tree = .ok out) :
    ∃ used : Nat, used * lambda ≤ path.length ∧ out.remaining = path.drop (used * lambda) := by
  induction queue, path, tree using prefillLoop.induct Topen generalizing out with
  | case1 path tree => simp [prefillLoop.eq_def] at h
  | case2 rest path tree =>
    have he : out = ⟨tree, path⟩ := by simpa [prefillLoop.eq_def] using h.symm
    subst out
    exact ⟨0, by simp, by simp⟩
  | case3 j path tree hne hgt hlen => simp at hlen
  | case4 j path tree hne hgt tail sibling hlen ih =>
    dsimp only [sibling] at *
    rw [prefillLoop.eq_def] at h
    simp only [if_neg hne, if_pos hgt, if_pos hlen] at h
    exact ih out h
  | case5 j path tree hne hgt k tail sibling hks hcap hs hp hlen ih =>
    dsimp only [sibling] at *
    rw [prefillLoop.eq_def] at h
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks, if_pos hcap] at h
    rw [dif_pos hs, dif_pos hp] at h
    obtain ⟨used, hbound, he⟩ := ih out h
    refine ⟨used + 1, ?_, ?_⟩
    · simp only [List.length_drop] at hbound
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · rw [he, List.drop_drop]
      congr 1
      ring
  | case6 j path tree hne hgt k tail sibling hks hcap hs hp hlen =>
    dsimp only [sibling] at *
    rw [prefillLoop.eq_def] at h
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks, if_pos hcap] at h
    rw [dif_pos hs, dif_neg hp] at h
    contradiction
  | case7 j path tree hne hgt k tail sibling hks hcap hs hlen =>
    dsimp only [sibling] at *
    rw [prefillLoop.eq_def] at h
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks, if_pos hcap] at h
    rw [dif_neg hs] at h
    contradiction
  | case8 j path tree hne hgt k tail sibling hks hcap hlen =>
    dsimp only [sibling] at *
    rw [prefillLoop.eq_def] at h
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks, if_neg hcap] at h
    contradiction
  | case9 j rest path tree hne hgt hlen ih =>
    rw [prefillLoop.eq_def] at h
    simp only [if_neg hne, if_pos hgt, if_neg hlen] at h
    exact ih out h
  | case10 j rest path tree hne hgt => simp [prefillLoop.eq_def, hne, hgt] at h

theorem any_true_nonempty (bits : List Bool) (h : bits.any id = true) : 0 < bits.length := by
  cases bits <;> simp_all

theorem padding_guard_iff (bits : List Bool) :
    ¬(0 < bits.length ∧ bits.any id = true) ↔ ∀ bit ∈ bits, bit = false := by
  have hn : (0 < bits.length ∧ bits.any id = true) ↔ bits.any id = true :=
    ⟨And.right, fun h => ⟨any_true_nonempty bits h, h⟩⟩
  rw [hn, List.any_eq_true]
  simp only [id_eq, Bool.not_eq_true, not_exists, not_and]

/-- Any successful prefill of an already padded opening has an entirely empty
tree and zero path bits: the printed guard has permitted no seed extraction. -/
theorem padded_prefill_success {lambda tau N : Nat} (hidden : Fin tau → Fin N)
    (opening : Opening lambda tau) (Topen : Nat) (tree : PartialTree lambda tau N)
    (hlong : Topen * lambda ≤ opening.path.length) (h : prefill hidden opening Topen = .ok tree) :
    tree = (fun _ => none) ∧ ∀ bit ∈ opening.path, bit = false := by
  obtain ⟨filled, hf, hrest⟩ := (bind_ok_iff _ _ tree).mp h
  have he := full_path_unchanged Topen (openingQueue hidden) opening.path (fun _ => none) filled hlong hf
  subst filled
  change (if 0 < opening.path.length ∧ opening.path.any id = true then
    Except.error ReconstructionError.paddingRejected else Except.ok (fun _ => none)) = .ok tree at hrest
  by_cases hz : 0 < opening.path.length ∧ opening.path.any id = true
  · rw [if_pos hz] at hrest
    contradiction
  · refine ⟨?_, (padding_guard_iff opening.path).mp hz⟩
    rw [if_neg hz] at hrest
    exact Except.ok.inj hrest.symm

/-- The padded shape is derived from Algorithm 8's actual successful run. -/
theorem open_then_prefill_empty {lambda tau N : Nat} (key : Key lambda tau N)
    (hidden : Fin tau → Fin N) (Topen : Nat) (hl : 0 < lambda) (opening : Opening lambda tau)
    (ho : openCommitment key hidden Topen = .ok opening) (tree : PartialTree lambda tau N)
    (hr : prefill hidden opening Topen = .ok tree) :
    tree = (fun _ => none) ∧ ∀ bit ∈ opening.path, bit = false := by
  have hlen := BAVC.openCommitment_path_length key hidden Topen hl opening ho
  exact padded_prefill_success hidden opening Topen tree (by omega) hr

/-- On allocated nonempty queues the only prefill-loop errors are its explicit
capacity rejection or an attempted extraction from too few path bits. -/
def PrefillOutcome {lambda tau N : Nat} : Except ReconstructionError (Prefilled lambda tau N) → Prop
  | .ok _ => True
  | .error err => err = .boundRejected ∨ err = .undefinedPathRead

theorem prefillLoop_safe_queue {lambda tau N : Nat} (Topen : Nat) (queue : List Nat)
    (path : List Bool) (tree : PartialTree lambda tau N) (hq : BAVC.ValidQueue (tau * N) queue) :
    PrefillOutcome (prefillLoop Topen queue path tree) := by
  induction queue, path, tree using prefillLoop.induct Topen with
  | case1 path tree => exact (hq.1 rfl).elim
  | case2 rest path tree => simp [prefillLoop.eq_def, PrefillOutcome]
  | case3 j path tree hne hgt hlen => simp at hlen
  | case4 j path tree hne hgt tail sibling hlen ih =>
    have hj := hq.2 j (by simp)
    have htail : ∀ k ∈ tail, 0 < k ∧ k < 2 * (tau * N) := by
      intro k hk
      exact hq.2 k (by simp [hk])
    dsimp only [sibling] at *
    rw [prefillLoop.eq_def]
    simp only [if_neg hne, if_pos hgt, if_pos hlen]
    exact ih (BAVC.parent_queue_valid hgt hj.2 htail)
  | case5 j path tree hne hgt k tail sibling hks hcap hs hp hlen ih =>
    have hj := hq.2 j (by simp)
    have htail : ∀ x ∈ k :: tail, 0 < x ∧ x < 2 * (tau * N) := by
      intro x hx
      exact hq.2 x (by simp [hx])
    dsimp only [sibling] at *
    rw [prefillLoop.eq_def]
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks, if_pos hcap]
    rw [dif_pos hs, dif_pos hp]
    exact ih (BAVC.parent_queue_valid hgt hj.2 htail)
  | case6 j path tree hne hgt k tail sibling hks hcap hs hp hlen =>
    dsimp only [sibling] at *
    rw [prefillLoop.eq_def]
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks, if_pos hcap]
    rw [dif_pos hs, dif_neg hp]
    exact Or.inr rfl
  | case7 j path tree hne hgt k tail sibling hks hcap hs hlen =>
    have hj := hq.2 j (by simp)
    exact (hs (BAVC.sibling_in_bounds hgt hj.2)).elim
  | case8 j path tree hne hgt k tail sibling hks hcap hlen =>
    dsimp only [sibling] at *
    rw [prefillLoop.eq_def]
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks, if_neg hcap]
    exact Or.inl rfl
  | case9 j rest path tree hne hgt hlen ih =>
    have hj := hq.2 j (by simp)
    have htail : ∀ k ∈ rest, 0 < k ∧ k < 2 * (tau * N) := by
      intro k hk
      exact hq.2 k (by simp [hk])
    rw [prefillLoop.eq_def]
    simp only [if_neg hne, if_pos hgt, if_neg hlen]
    exact ih (BAVC.parent_queue_valid hgt hj.2 htail)
  | case10 j rest path tree hne hgt =>
    have hj := (hq.2 j (by simp)).1
    omega

end SDitH.Proofs.BAVCReconstruction
