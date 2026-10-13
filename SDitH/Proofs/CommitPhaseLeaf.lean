import SDitH.Proofs.CommitRunExchange
import SDitH.Proofs.ProgramRelabel

/-! The commitment phase under the exchange of a leaf's value. The phase
commits every leaf at the leaf's own key; under the exchange at a leaf the
leaf's value and so its key move, while the other leaves' keys are
untouched. So the phase at the exchanged tree is the phase at the tree
with the two keys swapped, and the exchanged family agrees with the family
through that swap at the leaves' keys; the run of the exchanged phase is
then the relabelled run of the phase. -/

namespace SDitH.Proofs.CommitPhaseLeaf

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open RunCongr RunHistoryShift CommitPhaseExchange TreeRunClosed TreeHistoryExchange TreeExchange HiddenLeafNode RunBind
open NodeExchange CommitRunExchange ProgramRelabel
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {lambda tau kappa s wit rnd : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)

/-- The leaf commitments of a tree, in the source's pair order. -/
def commitPhase (nodes : Nat → Seed lambda) :
    SignerProgram lambda s wit rnd (Fin tau × Fin (2 ^ kappa) → Digest lambda) :=
  collect (fun pair : Fin tau × Fin (2 ^ kappa) =>
      commitCall S.layout (tau * 2 ^ kappa) S.variant salt (nodes (leafNode pair.1 pair.2).val)
        (Spec.SeedTree.leafOffset pair.1 pair.2))
    (Spec.SharedSlopeExec.allPairs tau kappa) fun _ => fun _ => false

/-- The rest is the phase followed by the tail. -/
theorem commitRest_eq (nodes : Nat → Seed lambda) :
    commitRest S salt witness nodes = bind (commitPhase S salt nodes) (commitTail S salt witness nodes) := rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The phase queries only at the leaves' keys. -/
theorem queriesIn_commitPhase (nodes : Nat → Seed lambda) : QueriesIn (leafKeys S nodes) (commitPhase S salt nodes) :=
  queriesIn_collect _ _ (fun pair : Fin tau × Fin (2 ^ kappa) =>
    queriesIn_commitCall S salt (leafKeys S nodes) (tau * 2 ^ kappa) (nodes (leafNode pair.1 pair.2).val)
      (Spec.SeedTree.leafOffset pair.1 pair.2) ⟨pair.1, pair.2, rfl⟩) _ _

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- Relabelling a collection relabels each call. -/
theorem mapKeys_collect {ι B : Type*} [DecidableEq ι] (ρ : Bits lambda → Bits lambda) (call : ι → SignerProgram lambda s wit rnd B) :
    ∀ (l : List ι) (acc : ι → B), mapKeys ρ (collect call l acc) = collect (fun i => mapKeys ρ (call i)) l acc := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons k rest ih =>
    intro acc
    simp only [collect, mapKeys_bind]
    congr 1
    funext value
    exact ih _

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- Relabelling a commitment call moves its seed's key. -/
theorem mapKeys_commitCall (ρ : Bits lambda → Bits lambda) (leafCount : Nat) (seed seed' : Bits lambda) (index : Nat)
    (h : ρ (S.layout.key seed) = S.layout.key seed') :
    mapKeys ρ (commitCall (s := s) (wit := wit) (rnd := rnd) S.layout leafCount S.variant salt seed index) =
      commitCall S.layout leafCount S.variant salt seed' index := by
  simp only [commitCall, expandCall, Spec.HashCipherProgram.bind, mapKeys, mapKey, h]

section Exchange

variable (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (f : Family (Bits lambda) (Bits lambda)) (root : Bits lambda) (b : Nat) (hb : 1 < b) (hbL : b < 2 * (tau * 2 ^ kappa))
  (v' : Bits lambda)
  (hp : parentKey S.layout f S.variant salt root b ≠ S.layout.key (S.layout.output (nodeBlock S.layout f S.variant salt root b)))
  (hp' : parentKey S.layout f S.variant salt root b ≠ S.layout.key (S.layout.output v'))
  (G1 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) → c ≠ b / 2 →
    S.layout.key (Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root c) ≠ parentKey S.layout f S.variant salt root b)
  (G2 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) → c ≠ b →
    S.layout.key (Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root c) ≠
      S.layout.key (S.layout.output (nodeBlock S.layout f S.variant salt root b)))
  (G3 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root c) ≠ S.layout.key (S.layout.output v'))

/-- The swap of the leaf's old and new keys. -/
def leafSwap : Bits lambda → Bits lambda :=
  Equiv.swap (S.layout.key (S.layout.output (nodeBlock S.layout f S.variant salt root b))) (S.layout.key (S.layout.output v'))

omit [Field F] [Algebra (ZMod 2) F] in
/-- A leaf's value in the expansion's tree is the tree's node. -/
theorem baseTree_leaf (e : Fin tau) (i : Fin (2 ^ kappa)) :
    baseTree S salt f root (leafNode e i).val =
      Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root (leafNode e i).val := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  have hleaf := SDitH.Proofs.SeedTree.leafAddress_bounds e i
  have hval' : (leafNode e i).val = Spec.SeedTree.leafAddress e i := rfl
  exact SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ hleaf.1 (by show _ ≤ 2 * (tau * 2 ^ kappa - 1) + 1; omega)

omit [Field F] [Algebra (ZMod 2) F] in
include hb hbL hp' G1 G2 G3 in
/-- The exchanged family agrees with the family through the swap at the
leaves' keys. -/
theorem exchanged_leafSwap : ∀ κ ∈ leafKeys S (baseTree S salt f root),
    exchanged S.layout f S.variant salt root b v' (leafSwap S salt f root b v' κ) = f κ := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  rintro κ ⟨e, i, rfl⟩
  have hleaf := SDitH.Proofs.SeedTree.leafAddress_bounds e i
  have hval' : (leafNode e i).val = Spec.SeedTree.leafAddress e i := rfl
  have hge : tau * 2 ^ kappa ≤ Spec.SeedTree.leafAddress e i := Nat.le_add_right _ _
  rw [baseTree_leaf, hval']
  have hb' : Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root b =
      S.layout.output (nodeBlock S.layout f S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout f S.variant salt root b hb
  have hne3 := G3 _ hleaf.1 hleaf.2
  have hnep := G1 _ hleaf.1 hleaf.2 (by show ¬ (_ = b / 2); omega)
  unfold leafSwap exchanged
  by_cases hcb : Spec.SeedTree.leafAddress e i = b
  · rw [hcb, hb', Equiv.swap_apply_left]
    exact swapNode_apply_right _ _ _ _ _ _ (Ne.symm hp')
  · have hne2 := G2 _ hleaf.1 hleaf.2 hcb
    rw [Equiv.swap_apply_of_ne_of_ne hne2 hne3]
    exact swapNode_apply_of_ne _ _ _ _ _ _ _ hnep hne2 hne3

omit [Field F] [Algebra (ZMod 2) F] in
include hb G2 G3 in
/-- The phase at the tree with the leaf set is the phase at the tree with
the two keys swapped. -/
theorem commitPhase_exchanged :
    mapKeys (leafSwap S salt f root b v') (commitPhase S salt (baseTree S salt f root)) =
      commitPhase S salt (Function.update (baseTree S salt f root) b (S.layout.output v')) := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  unfold commitPhase
  rw [mapKeys_collect]
  congr 1
  funext pair
  have hleaf := SDitH.Proofs.SeedTree.leafAddress_bounds pair.1 pair.2
  have hval' : (leafNode pair.1 pair.2).val = Spec.SeedTree.leafAddress pair.1 pair.2 := rfl
  have hb' : Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root b =
      S.layout.output (nodeBlock S.layout f S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout f S.variant salt root b hb
  refine mapKeys_commitCall S salt _ _ _ _ _ ?_
  rw [Function.update_apply]
  by_cases hcb : (leafNode pair.1 pair.2).val = b
  · rw [if_pos hcb, baseTree_leaf, hcb, hb']
    exact Equiv.swap_apply_left _ _
  · rw [if_neg hcb, baseTree_leaf]
    exact Equiv.swap_apply_of_ne_of_ne (G2 _ hleaf.1 hleaf.2 hcb) (G3 _ hleaf.1 hleaf.2)

omit [Field F] [Algebra (ZMod 2) F] in
include hb hbL hp' G1 G2 G3 in
/-- The run of the phase at the exchanged tree under the exchanged family
is the relabelled run of the phase. -/
theorem commitPhase_run_exchanged (fuel : Nat) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure (exchanged S.layout f S.variant salt root b v') fuel
        (commitPhase S salt (Function.update (baseTree S salt f root) b (S.layout.output v'))) table hashes
        (ciphers.map (mapEntry (leafSwap S salt f root b v'))) log =
      (runFixed procedure f fuel (commitPhase S salt (baseTree S salt f root)) table hashes ciphers log).map
        (mapResult (leafSwap S salt f root b v')) := by
  rw [← commitPhase_exchanged S salt f root b hb v' G2 G3]
  exact runFixed_mapKeys (leafKeys S (baseTree S salt f root)) f _ _ (exchanged_leafSwap S salt f root b hb hbL v' hp' G1 G2 G3) fuel _
    (queriesIn_commitPhase S salt _) table hashes ciphers log

end Exchange

end
end SDitH.Proofs.CommitPhaseLeaf
