import SDitH.Proofs.PhaseViewLeaf
import SDitH.Proofs.HonestLeafBound
import SDitH.Proofs.HiddenKeysAllExchange

/-! The phase view pruned at a key list depending on the family, under the
exchange of a leaf's value: for any list function containing the three
exchanged keys and with the expected members under the exchange, the
view is unchanged; in particular at the hidden keys of all executions.
The posterior bound at the leaf is then stated for any bounded weight
invariant under the exchange on the good fiber, and instantiated to the
view pruned at the hidden keys of all executions. -/

namespace SDitH.Proofs.PhaseViewLeafAll

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open Spec.SharedScheme
open Spec.SeedTree (leafAddress)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open RunCongr RunHistoryShift CommitPhaseExchange TreeRunClosed TreeHistoryExchange TreeExchange HiddenLeafNode RunBind
open NodeExchange CommitRunExchange ProgramRelabel CommitPhaseLeaf CommitRunLeaf HiddenEntries HiddenKeys HiddenKeysExchange
open CommitHistoryKeys FiberCountingSided RunKeys SharedResample PhaseViewLeaf HiddenTuple HiddenKeysAllExchange
open PosteriorNodeBound HonestNodeBound HonestLeafBound CipherResample ChargeExpect TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {lambda tau kappa s wit rnd : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)

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

omit [Field F] [Algebra (ZMod 2) F] in
include hb hbL hin hl hL hp hp' G1 G2 G3 G4 hfκ hfκ' in
/-- The phase view pruned at a family-dependent key list is the same under
the exchange, when the list contains the exchanged keys as expected. -/
theorem phaseView_exchanged_of_mem (K : Family (Bits lambda) (Bits lambda) → List (Bits lambda))
    (hκ'mem : S.layout.key (S.layout.output v') ∈ K (exchanged S.layout w.family S.variant salt root b v'))
    (hκmem : S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ∈ K w.family)
    (hpmem : parentKey S.layout w.family S.variant salt root b ∈ K w.family)
    (hmem : ∀ x, x ∈ S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ::
        K (exchanged S.layout w.family S.variant salt root b v') ↔
      x ∈ S.layout.key (S.layout.output v') :: K w.family) :
    phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
        (K (exchanged S.layout w.family S.variant salt root b v')) w =
      phaseView S salt w.family root (K w.family) w := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  have hnode := node_exchanged S.layout hin hl (tau * 2 ^ kappa) hL w.family S.variant salt root b hb hbL v' hp hp'
    G1 G2 G3 G4
  -- step A: the exchanged view prunes as well at the old key
  have hA : phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
      (K (exchanged S.layout w.family S.variant salt root b v')) w =
      phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
        (S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ::
          K (exchanged S.layout w.family S.variant salt root b v')) w := by
    by_cases hmem' : S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ∈
        K (exchanged S.layout w.family S.variant salt root b v')
    · refine phaseView_congr_mem S salt _ root _ _ (fun x => ?_) w
      simp only [List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun hx => hx ▸ hmem') id⟩
    · refine (phaseView_cons_of_fresh S salt _ root _ _ w fun out hout e he => ?_).symm
      rcases phaseRun_keys S salt _ root w out hout e he with hold | ⟨c, hc1, hcL, hc⟩
      · exact hfκ e hold
      · rw [hc, hnode c hcL]
        by_cases hcb : c = b
        · rw [if_pos hcb]
          intro h
          exact hmem' (h ▸ hκ'mem)
        · rw [if_neg hcb]
          exact G2 c hc1 hcL hcb
  -- step B: the enlarged lists have the same members
  have hB : phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
      (S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ::
        K (exchanged S.layout w.family S.variant salt root b v')) w =
      phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
        (S.layout.key (S.layout.output v') :: K w.family) w :=
    phaseView_congr_mem S salt _ root _ _ hmem w
  -- step C: the run's view under the exchange
  have hC : phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
      (S.layout.key (S.layout.output v') :: K w.family) w =
      phaseView S salt w.family root (S.layout.key (S.layout.output v') :: K w.family) w := by
    refine phaseView_exchanged_of_subset S salt w root b hb hbL v' hin hl hL hp hp' G1 G2 G3 G4 _ fun x hx => ?_
    simp only [exchangedKeys, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact List.mem_cons_of_mem _ hpmem
    · exact List.mem_cons_of_mem _ hκmem
    · exact List.mem_cons_self
  -- step D: the family's view prunes as well at the new key
  have hD : phaseView S salt w.family root (S.layout.key (S.layout.output v') :: K w.family) w =
      phaseView S salt w.family root (K w.family) w := by
    by_cases hmem' : S.layout.key (S.layout.output v') ∈ K w.family
    · refine phaseView_congr_mem S salt _ root _ _ (fun x => ?_) w
      simp only [List.mem_cons]
      exact ⟨fun h => h.elim (fun hx => hx ▸ hmem') id, Or.inr⟩
    · refine phaseView_cons_of_fresh S salt _ root _ _ w fun out hout e he => ?_
      rcases phaseRun_keys S salt _ root w out hout e he with hold | ⟨c, hc1, hcL, hc⟩
      · exact hfκ' e hold
      · rw [hc]
        exact G3 c hc1 hcL
  exact hA.trans (hB.trans (hC.trans hD))

omit [Field F] [Algebra (ZMod 2) F] in
include hb hbL hin hl hL hp hp' G1 G2 G3 G4 hfκ hfκ' in
/-- The phase view pruned at the hidden keys of all executions is the same
under the exchange of a node on some execution's hidden path. -/
theorem phaseView_exchanged_all (hidden : Fin tau → Fin (2 ^ kappa)) (e : Fin tau)
    (hpath : b ∈ pathAddresses (leafAddress e (hidden e))) :
    phaseView S salt (exchanged S.layout w.family S.variant salt root b v') root
        (hiddenKeysAll S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root hidden) w =
      phaseView S salt w.family root (hiddenKeysAll S.layout w.family S.variant salt root hidden) w := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  have hnode := node_exchanged S.layout hin hl (tau * 2 ^ kappa) hL w.family S.variant salt root b hb hbL v' hp hp'
    G1 G2 G3 G4
  have hb' : Spec.SeedTree.node (treeExpand S.layout w.family S.variant salt) root b =
      S.layout.output (nodeBlock S.layout w.family S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout w.family S.variant salt root b hb
  refine phaseView_exchanged_of_mem S salt w root b hb hbL v' hin hl hL hp hp' G1 G2 G3 G4 hfκ hfκ'
    (fun g => hiddenKeysAll S.layout g S.variant salt root hidden) ?_ ?_ ?_
    (mem_hiddenKeysAll_exchanged S.layout w.family S.variant salt root hidden hin hl hL b hb hbL v' hp hp' G1 G2 G3 G4 e hpath)
  · have h := key_mem_hiddenKeysAll S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root
      hidden e b (Or.inr hpath)
    rwa [hnode b (by omega), if_pos rfl] at h
  · have h := key_mem_hiddenKeysAll S.layout w.family S.variant salt root hidden e b (Or.inr hpath)
    rwa [hb'] at h
  · exact key_mem_hiddenKeysAll S.layout w.family S.variant salt root hidden e (b / 2) (parent_mem_pathAddresses hpath)

end Exchange

section Bound

variable (w₀ : World lambda s wit rnd) (root : Bits lambda) (b : Nat) (q : Bits lambda)
  (Φ : Family (Bits lambda) (Bits lambda) → ℝ≥0∞)

/-- A weight on the fresh fiber of a parent seed. -/
def weightA (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (Spec.SeedTree.node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g)) * Φ g

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem weightA_le_one (hΦ : ∀ g, Φ g ≤ 1) (g : Family (Bits lambda) (Bits lambda)) : weightA S salt w₀ root b q Φ g ≤ 1 := by
  unfold weightA
  calc _ ≤ 1 * 1 := mul_le_mul'
        (by by_cases h : (Spec.SeedTree.node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g) <;>
          simp [h, indicator])
        (hΦ g)
    _ = 1 := mul_one _

variable (v : Bits lambda) (hb : 1 < b) (hbL : b < 2 * (tau * 2 ^ kappa)) (hin : Function.Injective S.layout.input)
  (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hb hbL hin hl hL in
/-- The weight does not decrease under the exchange on the good fiber, for a
weight invariant under the exchange there. -/
theorem weightA_exchanged
    (hinv : ∀ v' g, OnFiber S.layout S.variant salt root b q v g → Good S.layout (tau * 2 ^ kappa) S.variant salt root b q v g →
      ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root b q w₀.cipherHistory v' g → Fresh S salt w₀ root b g →
      Φ (exchanged S.layout g S.variant salt root b v') = Φ g)
    (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda))
    (hg : OnFiber S.layout S.variant salt root b q v g)
    (hgood : Good S.layout (tau * 2 ^ kappa) S.variant salt root b q v g)
    (hbad : ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root b q w₀.cipherHistory v' g) :
    weightA S salt w₀ root b q Φ g ≤ weightA S salt w₀ root b q Φ (exchanged S.layout g S.variant salt root b v') := by
  have hparent : parentKey S.layout g S.variant salt root b = S.layout.key q := by
    unfold parentKey
    rw [hg.1]
  have hb' : Spec.SeedTree.node (treeExpand S.layout g S.variant salt) root b =
      S.layout.output (nodeBlock S.layout g S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout g S.variant salt root b hb
  unfold weightA
  by_cases hcond : Spec.SeedTree.node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g
  · have hfr := hcond.2
    have hpκ : S.layout.key q ≠ S.layout.key (S.layout.output v) := by
      rw [← hparent, ← hg.2, ← hb']
      exact hfr.2.2
    have hbad' := hbad
    simp only [Bad, not_or, not_exists, not_and] at hbad'
    obtain ⟨hbH, hbp, hb3, hb4⟩ := hbad'
    have hnode := node_exchanged S.layout hin hl (tau * 2 ^ kappa) hL g S.variant salt root b hb hbL v'
      (by rw [hparent, hg.2]; exact hpκ) (by rw [hparent]; exact fun h => hbp h.symm)
      (fun c h1 hc hcb => by rw [hparent]; exact hgood.1 c h1 hc hcb)
      (fun c h1 hc hcb => by rw [hg.2]; exact hgood.2 c h1 hc hcb)
      (fun c _ hc => hb3 c hc)
      (fun c hc hsib hcb => by rw [hparent]; exact hb4 c hc hsib hcb)
    have hhalf : Spec.SeedTree.node (treeExpand S.layout (exchanged S.layout g S.variant salt root b v') S.variant salt) root (b / 2) = q := by
      rw [hnode (b / 2) (by omega), if_neg (by omega), hg.1]
    have hcond' : Spec.SeedTree.node (treeExpand S.layout (exchanged S.layout g S.variant salt root b v') S.variant salt) root (b / 2) = q ∧
        Fresh S salt w₀ root b (exchanged S.layout g S.variant salt root b v') := by
      refine ⟨hhalf, ?_, ?_, ?_⟩
      · show S.layout.key (Spec.SeedTree.node (treeExpand S.layout (exchanged S.layout g S.variant salt root b v') S.variant salt) root (b / 2)) ∉ _
        rw [hhalf, ← hparent]
        exact hfr.1
      · rw [hnode b (by omega), if_pos rfl]
        exact hbH
      · show S.layout.key (Spec.SeedTree.node (treeExpand S.layout (exchanged S.layout g S.variant salt root b v') S.variant salt) root (b / 2)) ≠ _
        rw [hhalf, hnode b (by omega), if_pos rfl]
        exact fun h => hbp h.symm
    rw [hinv v' g hg hgood hbad hfr]
    simp only [hcond, hcond']
    exact le_rfl
  · simp only [hcond, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hb hbL hin hl hL in
/-- The posterior bound at the leaf for an invariant bounded weight. -/
theorem honest_leaf_bound_gen (hΦ : ∀ g, Φ g ≤ 1)
    (hinv : ∀ v' g, OnFiber S.layout S.variant salt root b q v g → Good S.layout (tau * 2 ^ kappa) S.variant salt root b q v g →
      ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root b q w₀.cipherHistory v' g → Fresh S salt w₀ root b g →
      Φ (exchanged S.layout g S.variant salt root b v') = Φ g)
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory)
    (hfp : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key q) (hfκ : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v))
    (hpκ : S.layout.key q ≠ S.layout.key (S.layout.output v)) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior w₀.cipherHistory) (fun g => weightA S salt w₀ root b q Φ g *
          indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v)))) ≤
      mean (posterior w₀.cipherHistory) (weightA S salt w₀ root b q Φ) :=
  posterior_node_bound S.layout hin hl (tau * 2 ^ kappa) hL S.variant salt root b hb hbL q v
    w₀.cipherHistory hpos hfp hfκ hpκ (weightA S salt w₀ root b q Φ) (weightA_le_one S salt w₀ root b q Φ hΦ)
    (fun v' g hg hgood hbad => weightA_exchanged S salt w₀ root b q Φ v hb hbL hin hl hL hinv v' g hg hgood hbad) c hfiber

end Bound

section All

variable (w₀ : World lambda s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa)) (root : Bits lambda)
  (w : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
    (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda)) → ℝ≥0∞)

/-- The phase view pruned at the hidden keys of all executions. -/
def phaseViewAll (g : Family (Bits lambda) (Bits lambda)) :
    PMF (Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda))) :=
  phaseView S salt g root (hiddenKeysAll S.layout g S.variant salt root hidden) w₀

omit [Field F] [Algebra (ZMod 2) F] in
/-- The mean of a view function under the all-executions phase view is
invariant under the exchange of a node on some execution's hidden path, on
the good fiber. -/
theorem phaseViewAll_mean_exchanged (b : Nat) (hb : 1 < b) (hbL : b < 2 * (tau * 2 ^ kappa))
    (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (e : Fin tau) (hpath : b ∈ pathAddresses (leafAddress e (hidden e)))
    (q v v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda)) (hg : OnFiber S.layout S.variant salt root b q v g)
    (hgood : Good S.layout (tau * 2 ^ kappa) S.variant salt root b q v g)
    (hbad : ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root b q w₀.cipherHistory v' g) (hfr : Fresh S salt w₀ root b g) :
    mean (phaseViewAll S salt w₀ hidden root (exchanged S.layout g S.variant salt root b v')) w =
      mean (phaseViewAll S salt w₀ hidden root g) w := by
  have hparent : parentKey S.layout g S.variant salt root b = S.layout.key q := by
    unfold parentKey
    rw [hg.1]
  have hb' : Spec.SeedTree.node (treeExpand S.layout g S.variant salt) root b =
      S.layout.output (nodeBlock S.layout g S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout g S.variant salt root b hb
  have hfκ : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v) := fun e he h =>
    hfr.2.1 (by rw [hb', hg.2]; exact mem_keysOf.mpr ⟨e, he, h⟩)
  have hpκ : S.layout.key q ≠ S.layout.key (S.layout.output v) := by
    rw [← hparent, ← hg.2, ← hb']
    exact hfr.2.2
  simp only [Bad, not_or, not_exists, not_and] at hbad
  obtain ⟨hbH, hbp, hb3, hb4⟩ := hbad
  have hfκ' : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v') := fun e he h =>
    hbH (by rw [← h]; exact mem_keysOf.mpr ⟨e, he, rfl⟩)
  have hview := phaseView_exchanged_all S salt { w₀ with family := g } root b hb hbL v' hin hl hL
    (by rw [hparent, hg.2]; exact hpκ) (by rw [hparent]; exact fun h => hbp h.symm)
    (fun c h1 hc hcb => by rw [hparent]; exact hgood.1 c h1 hc hcb)
    (fun c h1 hc hcb => by rw [hg.2]; exact hgood.2 c h1 hc hcb)
    (fun c _ hc => hb3 c hc)
    (fun c hc hsib hcb => by rw [hparent]; exact hb4 c hc hsib hcb)
    (fun e he => by rw [hg.2]; exact hfκ e he) hfκ' hidden e hpath
  simp only at hview
  rw [phaseView_setFamily, phaseView_setFamily] at hview
  unfold phaseViewAll
  rw [hview]
  rfl

end All

end
end SDitH.Proofs.PhaseViewLeafAll
