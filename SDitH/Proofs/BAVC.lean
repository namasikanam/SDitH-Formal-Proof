import SDitH.Spec.BAVC
import SDitH.Proofs.SeedTree
import Mathlib.Tactic

namespace SDitH.Proofs.BAVC

open Spec Spec.BAVC

theorem buildTree_eq_node {lambda tau N : Nat} (p : Primitives lambda)
    (salt root : DomainSeparation.Bits lambda) (initial : Nat → Seed lambda)
    (hL : 0 < tau * N) (a : NodeAddress tau N) :
    buildTree p salt root initial a = Spec.SeedTree.node (p.expandSeed salt) root a.val := by
  apply SeedTree.run_matches_node
  · exact a.property.1
  · have ha := a.property.2
    omega

theorem buildTree_independent_of_initial {lambda tau N : Nat} (p : Primitives lambda)
    (salt root : DomainSeparation.Bits lambda) (first second : Nat → Seed lambda)
    (hL : 0 < tau * N) :
    (buildTree p salt root first : Tree lambda tau N) = buildTree p salt root second := by
  funext a
  rw [buildTree_eq_node p salt root first hL a, buildTree_eq_node p salt root second hL a]

/-- Every output, including the opening key and both hash layers, agrees with
the recursively characterized tree. This is functional correctness of Algorithm
7's construction; it is not a hiding or binding theorem. -/
theorem commit_eq_recursive_tree {lambda tau N : Nat} (p : Primitives lambda)
    (salt root : DomainSeparation.Bits lambda) (hL : 0 < tau * N) :
    (commit p salt root : CommitResult lambda tau N) =
      commitFromTree p salt (fun a => Spec.SeedTree.node (p.expandSeed salt) root a.val) := by
  unfold commit
  congr 1
  funext a
  exact buildTree_eq_node p salt root (fun _ => root) hL a

theorem commit_seed {lambda tau N : Nat} (p : Primitives lambda)
    (salt root : DomainSeparation.Bits lambda) (hL : 0 < tau * N)
    (e : Fin tau) (i : Fin N) :
    (commit p salt root : CommitResult lambda tau N).seeds e i =
      Spec.SeedTree.node (p.expandSeed salt) root (Spec.SeedTree.leafAddress e i) := by
  exact buildTree_eq_node p salt root (fun _ => root) hL (leafNode e i)

theorem commit_key_matches_seed {lambda tau N : Nat} (p : Primitives lambda)
    (salt root : DomainSeparation.Bits lambda) (e : Fin tau) (i : Fin N) :
    (commit p salt root : CommitResult lambda tau N).key.commitments e i =
      p.commitSeed salt ((commit p salt root : CommitResult lambda tau N).seeds e i)
        (Spec.SeedTree.leafOffset e i) := rfl

theorem serializeArray_length {n bits : Nat} (v : Fin n → DomainSeparation.Bits bits) :
    (serializeArray v).length = n * bits := by
  simp [serializeArray, List.length_flatMap, List.map_ofFn, Function.comp_def, List.ofFn_const]

end SDitH.Proofs.BAVC
