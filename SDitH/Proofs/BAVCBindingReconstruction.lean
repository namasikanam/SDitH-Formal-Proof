import SDitH.Proofs.BAVCBinding
import SDitH.Proofs.SeedPrimitives

/-! Successful actual reconstructions with a common root and inconsistent
revealed seeds yield a computed hash collision or a same-index seed-commitment
collision. No collision resistance or successful reconstruction is postulated. -/

namespace SDitH.Proofs.BAVCBindingReconstruction

open Spec.BAVC Spec.BAVCBinding

theorem reconstructionRows_refines {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat)
    (initial : NodesBinding lambda tau N) :
    (reconstructionRows p salt hidden opening Topen initial).map (reconstructionHashes p salt) =
      reconstructWithNodes p salt hidden opening Topen initial := by
  unfold reconstructionRows reconstructWithNodes
  cases hp : prefill hidden opening Topen with
  | error cause => rfl
  | ok tree =>
    simp only [Bind.bind, Except.bind]
    cases he : expandPartialThrough p salt tree initial (tau * N - 1) le_rfl with
    | error cause => rfl
    | ok nodes =>
      cases hr : reconstructRowsThrough p salt hidden opening nodes tau le_rfl <;> rfl

theorem reconstructionRows_ok {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat)
    (initial : NodesBinding lambda tau N) (out : Reconstructed lambda tau N)
    (h : reconstructWithNodes p salt hidden opening Topen initial = .ok out) :
    ∃ rows, reconstructionRows p salt hidden opening Topen initial = .ok rows ∧
      out = reconstructionHashes p salt rows ∧
      ∃ nodes, reconstructRowsThrough p salt hidden opening nodes tau le_rfl = .ok rows := by
  obtain ⟨tree, nodes, rows, hp, he, hr, hout⟩ :=
    (BAVCReconstruction.reconstructWithNodes_ok_iff p salt hidden opening Topen initial out).mp h
  exact ⟨rows, by simp only [reconstructionRows, hp, he, hr, Bind.bind, Except.bind], hout, nodes, hr⟩

theorem row_seed_commitment {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (rows : Vector (Vector (ReconstructedLeaf lambda) N) tau)
    (hr : reconstructRowsThrough p salt hidden opening nodes tau le_rfl = .ok rows)
    (e : Fin tau) (i : Fin N) (seed : Seed lambda) (hs : (rows[e][i]).seed = some seed) :
    (rows[e][i]).commitment = p.commitSeed salt seed (Spec.SeedTree.leafOffset e i) := by
  by_cases hi : i = hidden e
  · subst i
    rw [BAVCReconstruction.successful_rows_hidden p salt hidden opening nodes rows hr e] at hs
    contradiction
  · obtain ⟨stored, _, hrow⟩ :=
      BAVCReconstruction.successful_rows_revealed p salt hidden opening nodes rows hr e i hi
    rw [hrow] at hs
    have he : stored = seed := Option.some.inj hs
    simp only [hrow, he]

/-- If the finder sees identical hash inputs, equality of the actually computed
leaf commitments gives a seed collision whenever revealed values disagree. -/
theorem rows_disagreement_without_hash_collision {lambda tau N : Nat} (p : Primitives lambda)
    (leftSalt rightSalt : Seed lambda) (leftHidden rightHidden : Fin tau → Fin N)
    (leftOpening rightOpening : Opening lambda tau) (leftNodes rightNodes : NodesBinding lambda tau N)
    (left right : Vector (Vector (ReconstructedLeaf lambda) N) tau)
    (hl : reconstructRowsThrough p leftSalt leftHidden leftOpening leftNodes tau le_rfl = .ok left)
    (hr : reconstructRowsThrough p rightSalt rightHidden rightOpening rightNodes tau le_rfl = .ok right)
    (e : Fin tau) (i : Fin N) (leftSeed rightSeed : Seed lambda)
    (hls : (left[e][i]).seed = some leftSeed) (hrs : (right[e][i]).seed = some rightSeed)
    (hne : leftSeed ≠ rightSeed)
    (hfind : findHashCollision p leftSalt rightSalt (rowCommitments left) (rowCommitments right) = none) :
    leftSalt = rightSalt ∧ IsSeedCollision p leftSalt (Spec.SeedTree.leafOffset e i) leftSeed rightSeed := by
  obtain ⟨hsalt, hcommits⟩ := BAVCBinding.find_none_implies_equal p leftSalt rightSalt _ _ hfind
  refine ⟨hsalt, hne, ?_⟩
  have he := congrFun (congrFun hcommits e) i
  change (left[e][i]).commitment = (right[e][i]).commitment at he
  rw [row_seed_commitment p leftSalt leftHidden leftOpening leftNodes left hl e i leftSeed hls,
    row_seed_commitment p rightSalt rightHidden rightOpening rightNodes right hr e i rightSeed hrs] at he
  simpa only [← hsalt] using he

/-- This is a deterministic reduction for two successful staged reconstructions.
It returns an actual hash collision, or its none result certifies a seed
commitment collision at the two supplied revealed values and the same index.
The unresolved source nodes environments are explicit inputs throughout. -/
theorem reconstruction_disagreement_collision {lambda tau N : Nat} (p : Primitives lambda)
    (leftSalt rightSalt : Seed lambda) (leftHidden rightHidden : Fin tau → Fin N)
    (leftOpening rightOpening : Opening lambda tau) (Topen : Nat)
    (leftNodes rightNodes : NodesBinding lambda tau N) (left right : Reconstructed lambda tau N)
    (hl : reconstructWithNodes p leftSalt leftHidden leftOpening Topen leftNodes = .ok left)
    (hr : reconstructWithNodes p rightSalt rightHidden rightOpening Topen rightNodes = .ok right)
    (hroot : left.hcom = right.hcom) (e : Fin tau) (i : Fin N) (leftSeed rightSeed : Seed lambda)
    (hls : left.seeds e i = some leftSeed) (hrs : right.seeds e i = some rightSeed)
    (hne : leftSeed ≠ rightSeed) :
    (∃ pair, findReconstructionCollision p leftSalt rightSalt leftHidden rightHidden
      leftOpening rightOpening Topen leftNodes rightNodes = .ok (some pair) ∧ IsHashCollision p pair) ∨
    (findReconstructionCollision p leftSalt rightSalt leftHidden rightHidden
      leftOpening rightOpening Topen leftNodes rightNodes = .ok none ∧
      leftSalt = rightSalt ∧ IsSeedCollision p leftSalt (Spec.SeedTree.leafOffset e i) leftSeed rightSeed) := by
  obtain ⟨leftRows, hlr, hleft, ln, hln⟩ := reconstructionRows_ok p leftSalt leftHidden leftOpening Topen leftNodes left hl
  obtain ⟨rightRows, hrr, hright, rn, hrn⟩ := reconstructionRows_ok p rightSalt rightHidden rightOpening Topen rightNodes right hr
  subst left
  subst right
  have hrun : findReconstructionCollision p leftSalt rightSalt leftHidden rightHidden
      leftOpening rightOpening Topen leftNodes rightNodes =
      .ok (findHashCollision p leftSalt rightSalt (rowCommitments leftRows) (rowCommitments rightRows)) := by
    simp only [findReconstructionCollision, hlr, hrr, Bind.bind, Except.bind]
  cases hfind : findHashCollision p leftSalt rightSalt (rowCommitments leftRows) (rowCommitments rightRows) with
  | none =>
    exact Or.inr ⟨by simpa only [hfind] using hrun,
      rows_disagreement_without_hash_collision p leftSalt rightSalt leftHidden rightHidden
        leftOpening rightOpening ln rn leftRows rightRows hln hrn e i leftSeed rightSeed hls hrs hne hfind⟩
  | some pair =>
    exact Or.inl ⟨pair, by simpa only [hfind] using hrun,
      (BAVCBinding.find_some_collision p leftSalt rightSalt _ _ hroot pair hfind).1⟩

/-- A seed-commitment collision in the actual two-call construction is equality
of both cipher outputs under the two different seed keys. No permutation or
ideal-cipher probability law is assumed for encStar, including truncation. -/
theorem commitSeed_eq_iff {lambda : Nat} (leafCount : Nat)
    (variant : Spec.DomainSeparation.Grinding)
    (encStar : Seed lambda → Seed lambda → Seed lambda)
    (salt left right : Seed lambda) (index : Nat) :
    Spec.SeedPrimitives.commitSeed leafCount variant encStar salt left index =
      Spec.SeedPrimitives.commitSeed leafCount variant encStar salt right index ↔
    ∀ side : Bool, encStar left (Spec.SeedPrimitives.cipherInput variant salt (leafCount + index) side) =
      encStar right (Spec.SeedPrimitives.cipherInput variant salt (leafCount + index) side) := by
  constructor
  · intro h side
    cases side with
    | false =>
      funext j
      have hj := congrFun h ⟨j.val, by have hj := j.isLt; omega⟩
      simpa only [Spec.SeedPrimitives.commitSeed, Spec.SeedPrimitives.expandSeed,
        SeedPrimitives.concatenate_left] using hj
    | true =>
      funext j
      have hj := congrFun h ⟨lambda + j.val, by have hj := j.isLt; omega⟩
      simpa only [Spec.SeedPrimitives.commitSeed, Spec.SeedPrimitives.expandSeed,
        SeedPrimitives.concatenate_right] using hj
  · intro h
    simp only [Spec.SeedPrimitives.commitSeed, Spec.SeedPrimitives.expandSeed, h]

theorem seed_collision_cipher_witness {lambda leafCount index : Nat}
    (hlambda : 26 ≤ lambda) (hcount : 4 * leafCount ≤ 2 ^ 24) (hindex : index < leafCount)
    (variant : Spec.DomainSeparation.Grinding)
    (encStar : Seed lambda → Seed lambda → Seed lambda) (hash : List Bool → Digest lambda)
    (salt left right : Seed lambda)
    (hcollision : IsSeedCollision (Spec.SeedPrimitives.bavcPrimitives leafCount variant encStar hash)
      salt index left right) :
    left ≠ right ∧
      Spec.SeedPrimitives.cipherInput variant salt (leafCount + index) false ≠
        Spec.SeedPrimitives.cipherInput variant salt (leafCount + index) true ∧
      ∀ side : Bool, encStar left (Spec.SeedPrimitives.cipherInput variant salt (leafCount + index) side) =
        encStar right (Spec.SeedPrimitives.cipherInput variant salt (leafCount + index) side) := by
  refine ⟨hcollision.1, ?_, (commitSeed_eq_iff leafCount variant encStar salt left right index).mp hcollision.2⟩
  intro h
  have he := (SeedPrimitives.cipherInput_injective hlambda hcount (by omega) (by omega)
    variant salt false true h).2
  contradiction

end SDitH.Proofs.BAVCBindingReconstruction
