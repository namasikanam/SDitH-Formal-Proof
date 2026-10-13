import SDitH.Proofs.CommitRunLeaf
import SDitH.Proofs.CommitHistoryKeys
import SDitH.Proofs.HiddenKeysExchange
import SDitH.Proofs.FiberCountingSided
import SDitH.Proofs.RunKeys

/-! The phase view under the exchange of a leaf's value. The phase view is
the phase's run after the expansion, kept as the commitments, the hash
state and the cipher history pruned at a key list. At the exchanged leaf
the view pruned at the exchanged family's own hidden keys is the view
pruned at the family's own hidden keys: each view prunes as well at the
other family's key of the leaf, the enlarged lists have the same members,
and the exchanged run's history pruned at the three exchanged keys is the
run's. The hidden leaf's value thus enters only after the phase. -/

namespace SDitH.Proofs.PhaseViewLeaf

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open Spec.SharedScheme
open Spec.IdealCipher (Family)
open RunCongr RunHistoryShift CommitPhaseExchange TreeRunClosed TreeHistoryExchange TreeExchange HiddenLeafNode RunBind
open NodeExchange CommitRunExchange ProgramRelabel CommitPhaseLeaf CommitRunLeaf HiddenEntries HiddenKeys HiddenKeysExchange
open CommitHistoryKeys FiberCountingSided RunKeys SharedResample
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {lambda tau kappa s wit rnd : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)

/-- The commitments of a finished phase. -/
def commitsOf : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda) →
    Fin tau × Fin (2 ^ kappa) → Digest lambda
  | .done c => c
  | _ => fun _ => fun _ => false

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem commitsOf_mapKeys (ρ : Bits lambda → Bits lambda)
    (p : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda)) :
    commitsOf (mapKeys ρ p) = commitsOf p := by
  cases p <;> rfl

/-- The view of a phase result at a key list: the commitments, the hash
state and the history pruned at the list. -/
def viewOf (K : List (Bits lambda))
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda))) :
    Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda)) :=
  ⟨.done (commitsOf out.state), out.hashTable, out.hashHistory, pruneAt K out.cipherHistory, out.hashCollided, out.trace⟩

/-- The phase's run from a world's state after the expansion. -/
def phaseRun (g : Family (Bits lambda) (Bits lambda)) (root : Bits lambda) (w₀ : World lambda s wit rnd) :
    PMF (Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda))) :=
  runFixed procedure g (phaseBudget tau kappa) (commitPhase S salt (baseTree S salt g root)) w₀.hashTable w₀.hashHistory
    (treeHistory S.layout g S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1) ++ w₀.cipherHistory) w₀.trace

/-- The phase view at a key list. -/
def phaseView (g : Family (Bits lambda) (Bits lambda)) (root : Bits lambda) (K : List (Bits lambda)) (w₀ : World lambda s wit rnd) :
    PMF (Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda))) :=
  (phaseRun S salt g root w₀).map (viewOf K)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The views at two key lists with the same members coincide. -/
theorem phaseView_congr_mem (g : Family (Bits lambda) (Bits lambda)) (root : Bits lambda) (K₁ K₂ : List (Bits lambda))
    (h : ∀ x, x ∈ K₁ ↔ x ∈ K₂) (w₀ : World lambda s wit rnd) :
    phaseView S salt g root K₁ w₀ = phaseView S salt g root K₂ w₀ := by
  unfold phaseView
  refine congrArg _ (funext fun out => ?_)
  show PMF.pure (viewOf K₁ out) = PMF.pure (viewOf K₂ out)
  unfold viewOf
  rw [pruneAt_congr_mem K₁ K₂ h]

omit [Field F] [Algebra (ZMod 2) F] in
/-- Every entry the phase records over the world's history is at the key
of a node of the tree. -/
theorem phaseRun_keys (g : Family (Bits lambda) (Bits lambda)) (root : Bits lambda) (w₀ : World lambda s wit rnd)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda)))
    (hout : out ∈ (phaseRun S salt g root w₀).support) :
    ∀ e ∈ out.cipherHistory, e ∈ w₀.cipherHistory ∨
      ∃ c, 1 ≤ c ∧ c < 2 * (tau * 2 ^ kappa) ∧
        e.key = S.layout.key (Spec.SeedTree.node (treeExpand S.layout g S.variant salt) root c) := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  intro e he
  rcases runFixed_keys (leafKeys S (baseTree S salt g root)) g _ _ (queriesIn_commitPhase S salt _) _ _ _ _ out hout e he with
    hmem | ⟨e', i, hk⟩
  · rw [List.mem_append] at hmem
    rcases hmem with htree | hold
    · obtain ⟨c, h1, hk, hc⟩ := treeHistory_key S.layout g S.variant salt root (fun _ => root) _ e htree
      exact Or.inr ⟨c, h1, by omega, hc⟩
    · exact Or.inl hold
  · have hleaf := SDitH.Proofs.SeedTree.leafAddress_bounds e' i
    refine Or.inr ⟨(leafNode e' i).val, by show 1 ≤ Spec.SeedTree.leafAddress e' i; omega, hleaf.2, ?_⟩
    rw [hk, baseTree_leaf]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The view at a key list equals the view at the list with a key added that
no recorded entry uses. -/
theorem phaseView_cons_of_fresh (g : Family (Bits lambda) (Bits lambda)) (root : Bits lambda) (K : List (Bits lambda))
    (κ : Bits lambda) (w₀ : World lambda s wit rnd)
    (hfresh : ∀ out ∈ (phaseRun S salt g root w₀).support, ∀ e ∈ out.cipherHistory, e.key ≠ κ) :
    phaseView S salt g root (κ :: K) w₀ = phaseView S salt g root K w₀ := by
  unfold phaseView
  show (phaseRun S salt g root w₀).bind (PMF.pure ∘ viewOf (κ :: K)) = (phaseRun S salt g root w₀).bind (PMF.pure ∘ viewOf K)
  refine bind_congr_support _ _ _ fun out hout => ?_
  simp only [Function.comp_apply, viewOf, pruneAt_cons_of_no_entry K κ _ (hfresh out hout)]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The phase at two trees agreeing on the nodes coincides. -/
theorem commitPhase_congr (n₁ n₂ : Nat → Seed lambda) (h : ∀ a, 0 < a → a < 2 * (tau * 2 ^ kappa) → n₁ a = n₂ a) :
    commitPhase S salt n₁ = commitPhase S salt n₂ := by
  unfold commitPhase
  congr 1
  funext pair
  rw [h (leafNode pair.1 pair.2).val (SDitH.Proofs.SeedTree.leafAddress_bounds pair.1 pair.2).1
    (SDitH.Proofs.SeedTree.leafAddress_bounds pair.1 pair.2).2]

section Exchange

variable (w : World lambda s wit rnd) (root : Bits lambda) (b : Nat) (hb : 1 < b) (hbL : b < 2 * (tau * 2 ^ kappa))
  (v' : Bits lambda) (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (hp : parentKey S.layout w.family S.variant salt root b ≠
    S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)))
  (hp' : parentKey S.layout w.family S.variant salt root b ≠ S.layout.key (S.layout.output v'))
  (G1 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) → c ≠ b / 2 →
    S.layout.key (Spec.SeedTree.node (treeExpand S.layout w.family S.variant salt) root c) ≠
      parentKey S.layout w.family S.variant salt root b)
  (G2 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) → c ≠ b →
    S.layout.key (Spec.SeedTree.node (treeExpand S.layout w.family S.variant salt) root c) ≠
      S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)))
  (G3 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (Spec.SeedTree.node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key (S.layout.output v'))
  (G4 : ∀ c, c < 2 * (tau * 2 ^ kappa) → c / 2 = b / 2 → c ≠ b →
    w.family (parentKey S.layout w.family S.variant salt root b) (S.layout.input (nodeTweak S.variant salt c)) ≠ v')
  (hfκ : ∀ e ∈ w.cipherHistory, e.key ≠ S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)))
  (hfκ' : ∀ e ∈ w.cipherHistory, e.key ≠ S.layout.key (S.layout.output v'))
  (a : Nat) (ha : a < 2 * (tau * 2 ^ kappa)) (hpath : b ∈ pathAddresses a)

omit [Field F] [Algebra (ZMod 2) F] in
include hin hl hL hb hbL hp hp' G1 G2 G3 G4 in
/-- The phase at the exchanged expansion's tree is the phase at the tree
with the node set. -/
theorem commitPhase_baseTree_exchanged :
    commitPhase S salt (baseTree S salt (exchanged S.layout w.family S.variant salt root b v') root) =
      commitPhase S salt (Function.update (baseTree S salt w.family root) b (S.layout.output v')) := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  have hsub : tau * 2 ^ kappa - 1 + 1 = tau * 2 ^ kappa := Nat.sub_add_cancel hpos
  refine commitPhase_congr S salt _ _ fun c hc0 hcL => ?_
  unfold baseTree
  rw [run_exchanged S.layout hin hl (tau * 2 ^ kappa) hL w.family S.variant salt root (fun _ => root) b hb hbL v' hp hp'
    G1 G2 G3 G4 (tau * 2 ^ kappa - 1) (by omega) c hc0 (by omega), Function.update_apply]

omit [Field F] [Algebra (ZMod 2) F] in
include hin hl hL hb hbL hp hp' G1 G2 G3 G4 in
/-- The phase view under the exchange, pruned at a list containing the three
exchanged keys, is the family's phase view. -/
theorem phaseView_exchanged_of_subset (K : List (Bits lambda))
    (hK : ∀ k ∈ exchangedKeys S.layout w.family S.variant salt root b v', k ∈ K) :
    phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root K w =
      phaseView S salt w.family root K w := by
  unfold phaseView phaseRun
  rw [commitPhase_baseTree_exchanged S salt w root b hb hbL v' hin hl hL hp hp' G1 G2 G3 G4, runFixed_history_shift]
  conv_rhs => rw [runFixed_history_shift]
  have hphase := commitPhase_run_exchanged S salt w.family root b hb hbL v' hp' G1 G2 G3 (phaseBudget tau kappa) w.hashTable
    w.hashHistory [] w.trace
  simp only [List.map_nil] at hphase
  rw [hphase, PMF.map_comp, PMF.map_comp, PMF.map_comp]
  refine congrArg _ (funext fun out => ?_)
  simp only [Function.comp_apply, viewOf]
  rw [leaf_history_pruned S salt hin hl hL w.family root b hb hbL v' hp hp' G1 G2 G3 G4 K hK w.cipherHistory out]
  simp only [appendHistory, mapResult, commitsOf_mapKeys]

omit [Field F] [Algebra (ZMod 2) F] in
include hb hbL hin hl hL hp hp' G1 G2 G3 G4 hfκ hfκ' ha hpath in
/-- The phase view pruned at the family's own hidden keys is the same under
the exchange of a path node, the leaf included. -/
theorem phaseView_exchanged :
    phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
        (hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a) w =
      phaseView S salt w.family root (hiddenKeys S.layout w.family S.variant salt root a) w := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  have hnode := node_exchanged S.layout hin hl (tau * 2 ^ kappa) hL w.family S.variant salt root b hb hbL v' hp hp'
    G1 G2 G3 G4
  have hb' : Spec.SeedTree.node (treeExpand S.layout w.family S.variant salt) root b =
      S.layout.output (nodeBlock S.layout w.family S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout w.family S.variant salt root b hb
  have hκ'mem : S.layout.key (S.layout.output v') ∈
      hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a := by
    rw [mem_hiddenKeys]
    exact ⟨b, Or.inr hpath, by rw [hnode b (by omega), if_pos rfl]⟩
  have hκmem : S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ∈
      hiddenKeys S.layout w.family S.variant salt root a := by
    rw [mem_hiddenKeys]
    exact ⟨b, Or.inr hpath, by rw [hb']⟩
  have hpmem : parentKey S.layout w.family S.variant salt root b ∈ hiddenKeys S.layout w.family S.variant salt root a := by
    rw [mem_hiddenKeys]
    exact ⟨b / 2, parent_mem_pathAddresses hpath, rfl⟩
  -- step A: the exchanged view prunes as well at the old key
  have hA : phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
      (hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a) w =
      phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
        (S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ::
          hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a) w := by
    by_cases hmem : S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ∈
        hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a
    · refine phaseView_congr_mem S salt _ root _ _ (fun x => ?_) w
      simp only [List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hx)
        · exact hmem
        · exact hx
    · refine (phaseView_cons_of_fresh S salt _ root _ _ w fun out hout e he => ?_).symm
      rcases phaseRun_keys S salt _ root w out hout e he with hold | ⟨c, hc1, hcL, hc⟩
      · exact hfκ e hold
      · rw [hc, hnode c hcL]
        by_cases hcb : c = b
        · rw [if_pos hcb]
          intro h
          exact hmem (h ▸ hκ'mem)
        · rw [if_neg hcb]
          exact G2 c hc1 hcL hcb
  -- step B: the enlarged lists have the same members
  have hB : phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
      (S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ::
        hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a) w =
      phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
        (S.layout.key (S.layout.output v') :: hiddenKeys S.layout w.family S.variant salt root a) w :=
    phaseView_congr_mem S salt _ root _ _
      (mem_hiddenKeys_exchanged S.layout hin hl (tau * 2 ^ kappa) hL w.family S.variant salt root b hb hbL v' hp hp'
        G1 G2 G3 G4 a ha hpath) w
  -- step C: the run's view under the exchange
  have hC : phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
      (S.layout.key (S.layout.output v') :: hiddenKeys S.layout w.family S.variant salt root a) w =
      phaseView S salt w.family root (S.layout.key (S.layout.output v') :: hiddenKeys S.layout w.family S.variant salt root a) w := by
    refine phaseView_exchanged_of_subset S salt w root b hb hbL v' hin hl hL hp hp' G1 G2 G3 G4 _ fun x hx => ?_
    simp only [exchangedKeys, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact List.mem_cons_of_mem _ hpmem
    · exact List.mem_cons_of_mem _ hκmem
    · exact List.mem_cons_self
  -- step D: the family's view prunes as well at the new key
  have hD : phaseView S salt w.family root
      (S.layout.key (S.layout.output v') :: hiddenKeys S.layout w.family S.variant salt root a) w =
      phaseView S salt w.family root (hiddenKeys S.layout w.family S.variant salt root a) w := by
    by_cases hmem : S.layout.key (S.layout.output v') ∈ hiddenKeys S.layout w.family S.variant salt root a
    · refine phaseView_congr_mem S salt _ root _ _ (fun x => ?_) w
      simp only [List.mem_cons]
      constructor
      · rintro (rfl | hx)
        · exact hmem
        · exact hx
      · exact Or.inr
    · refine phaseView_cons_of_fresh S salt _ root _ _ w fun out hout e he => ?_
      rcases phaseRun_keys S salt _ root w out hout e he with hold | ⟨c, hc1, hcL, hc⟩
      · exact hfκ' e hold
      · rw [hc]
        exact G3 c hc1 hcL
  exact hA.trans (hB.trans (hC.trans hD))

end Exchange

end
end SDitH.Proofs.PhaseViewLeaf
