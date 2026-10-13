import SDitH.Proofs.TreeEntries
import SDitH.Proofs.PRGHypothesis

/-! The hidden-share step under the posterior family. Conditioned on a
history that records the ancestry of the hidden leaf's parent and in which
the parent's key is fresh, every consistent family computes the same parent,
the leaf is a uniform seed under the posterior family, its PRG vector is
uniform under the PRG hypothesis, and the honest revealed data of that
vector is uniform whatever the witness-dependent constants. This is the
per-signature hidden-share step with its two inputs explicit: the
fresh-parent-key event and the PRG hypothesis. -/

namespace SDitH.Proofs.HiddenShareStep

open Spec.IdealCipher Spec.SeedTree Spec.BAVCCipherProgram Spec.DomainSeparation Spec.FieldRepresentation
open HiddenLeafNode FreshKeyUniform LeafSeedUniform PosteriorLeafUniform HonestViewUniform PRGHypothesis
open scoped Classical ENNReal

noncomputable section

variable {lambda : Nat} {Key Block : Type*} [Fintype Key] [Fintype Block] [Nonempty Block]

/-- Under the posterior family, a node below the root whose parent's ancestry
is recorded and whose parent key is fresh is a uniform seed. -/
theorem posterior_node_uniform (layout : Layout lambda Key Block) (hout : OutputUniform layout) (variant : Grinding)
    (salt root : Bits lambda) (world : World Key Block) (reference : Candidates world) (a : Nat) (ha : 1 < a)
    (hrec : AncestryRecorded layout reference.val variant salt root world.history (a / 2))
    (hkey : FreshKey world (layout.key (node (treeExpand layout reference.val variant salt) root (a / 2)))) :
    (PMF.uniformOfFintype (Candidates world)).map
        (fun family => node (treeExpand layout family.val variant salt) root a) =
      PMF.uniformOfFintype (Bits lambda) := by
  have hnode : (fun family : Candidates world => node (treeExpand layout family.val variant salt) root a) =
      fun family => layout.output (family.val (layout.key (node (treeExpand layout reference.val variant salt) root (a / 2)))
        (layout.input (nodeTweak variant salt a))) := by
    funext family
    rw [node_eq_child layout family.val variant salt root a ha,
      node_determined layout reference.val family.val variant salt root world.history family.property (a / 2) hrec]
  rw [hnode]
  exact posterior_leaf_uniform layout hout world _ (nodeTweak variant salt a) hkey

variable (category : Category) {tau kappa s wit d : Nat}

/-- The hidden-share step: under the fresh-parent-key event and the PRG
hypothesis, the honest data of the hidden leaf's PRG vector is uniform under
the posterior family, whatever the witness-dependent constants. -/
theorem hidden_share_step (layout : Layout (width category) Key Block) (hout : OutputUniform layout) (variant : Grinding)
    (salt root : Bits (width category)) (world : World Key Block) (reference : Candidates world) (a : Nat) (ha : 1 < a)
    (hrec : AncestryRecorded layout reference.val variant salt root world.history (a / 2))
    (hkey : FreshKey world (layout.key (node (treeExpand layout reference.val variant salt) root (a / 2))))
    (p : Spec.BLCCommit.Primitives (width category) tau kappa s wit (width category * (d - 1))) (count : Nat)
    (enough : s + (wit + width category * (d - 1)) ≤ 8 * count) (e : Fin tau)
    (hprg : PRGUniform p salt count enough e)
    (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A : Fin wit → ZMod 2)
    (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2) (Qc st : Fin (d - 1) → QuotientRing category) :
    (PMF.uniformOfFintype (Candidates world)).map (fun family =>
        honestData category M A B Cc Qc st
          (prgVector p salt count enough e (node (treeExpand layout family.val variant salt) root a))) =
      PMF.uniformOfFintype ((Fin wit → ZMod 2) × (Fin (d - 1) → QuotientRing category) × (Fin s → ZMod 2)) := by
  have h : (fun family : Candidates world =>
      honestData category M A B Cc Qc st
        (prgVector p salt count enough e (node (treeExpand layout family.val variant salt) root a))) =
      (honestData category M A B Cc Qc st ∘ prgVector p salt count enough e) ∘
        (fun family => node (treeExpand layout family.val variant salt) root a) := rfl
  rw [h, ← PMF.map_comp, posterior_node_uniform layout hout variant salt root world reference a ha hrec hkey,
    ← PMF.map_comp, hprg]
  exact honestData_uniform category M A B Cc Qc st

end
end SDitH.Proofs.HiddenShareStep
