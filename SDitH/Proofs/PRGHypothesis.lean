import SDitH.Spec.BLCCommit
import SDitH.Proofs.HonestViewUniform

/-! The PRG hypothesis of the hidden-share step, as an explicit statement.
The random table's row of a party is the binary sampling of the PRG stream
of its seed (with the salt and execution tweak), so a party's vector is a
fixed function of its seed; the hypothesis that this function maps a
uniform seed to a uniform vector is the PRG assumption (or a random-oracle
model for the PRG), carried as an explicit theorem hypothesis. Under it,
the honest data of a uniformly seeded hidden party is uniform and
independent of the witness-dependent constants. -/

namespace SDitH.Proofs.PRGHypothesis

open Spec.BLCCommit Spec.DomainSeparation Spec.FieldRepresentation HonestViewUniform
open scoped BigOperators Classical

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- A party's random vector as a function of its seed. -/
def prgVector (p : Primitives lambda tau kappa s wit rnd) (salt : Bits lambda) (count : Nat)
    (enough : s + (wit + rnd) ≤ 8 * count) (e : Fin tau) (seed : Bits lambda) : Fin (s + (wit + rnd)) → ZMod 2 :=
  fun j => bitField ((Spec.ByteSampling.sampleBinary ⟨p.prg seed salt e.val, 0⟩ (s + (wit + rnd)) count enough).value j)

/-- The random table's row is the PRG vector of the party's seed. -/
theorem randomTable_eq (p : Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (seeds : Fin tau → Fin (2 ^ kappa) → Bits lambda) (count : Nat) (enough : s + (wit + rnd) ≤ 8 * count)
    (e : Fin tau) (i : Fin (2 ^ kappa)) :
    randomTable p salt seeds count enough e i = prgVector p salt count enough e (seeds e i) := rfl

/-- The PRG hypothesis: a uniform seed gives a uniform vector. -/
def PRGUniform (p : Primitives lambda tau kappa s wit rnd) (salt : Bits lambda) (count : Nat)
    (enough : s + (wit + rnd) ≤ 8 * count) (e : Fin tau) : Prop :=
  (PMF.uniformOfFintype (Bits lambda)).map (prgVector p salt count enough e) =
    PMF.uniformOfFintype (Fin (s + (wit + rnd)) → ZMod 2)

variable (category : Category) {d : Nat}

/-- Under the PRG hypothesis, the honest data of a uniformly seeded hidden
party is uniform. -/
theorem honestData_uniform_of_prg (p : Primitives lambda tau kappa s wit (width category * (d - 1))) (salt : Bits lambda)
    (count : Nat) (enough : s + (wit + width category * (d - 1)) ≤ 8 * count) (e : Fin tau)
    (hprg : PRGUniform p salt count enough e)
    (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A : Fin wit → ZMod 2)
    (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2) (Qc st : Fin (d - 1) → QuotientRing category) :
    (PMF.uniformOfFintype (Bits lambda)).map (fun seed =>
        honestData category M A B Cc Qc st (prgVector p salt count enough e seed)) =
      PMF.uniformOfFintype ((Fin wit → ZMod 2) × (Fin (d - 1) → QuotientRing category) × (Fin s → ZMod 2)) := by
  have h : (fun seed => honestData category M A B Cc Qc st (prgVector p salt count enough e seed)) =
      honestData category M A B Cc Qc st ∘ prgVector p salt count enough e := rfl
  rw [h, ← PMF.map_comp, hprg]
  exact honestData_uniform category M A B Cc Qc st

/-- Under the PRG hypothesis, the honest data's distribution over the hidden
seed does not depend on the witness-dependent constants. -/
theorem honestData_independent_of_prg (p : Primitives lambda tau kappa s wit (width category * (d - 1)))
    (salt : Bits lambda) (count : Nat) (enough : s + (wit + width category * (d - 1)) ≤ 8 * count) (e : Fin tau)
    (hprg : PRGUniform p salt count enough e)
    (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A A' : Fin wit → ZMod 2)
    (B B' : Fin (d - 1) → QuotientRing category) (Cc Cc' : Fin s → ZMod 2)
    (Qc Qc' st st' : Fin (d - 1) → QuotientRing category) :
    (PMF.uniformOfFintype (Bits lambda)).map (fun seed =>
        honestData category M A B Cc Qc st (prgVector p salt count enough e seed)) =
      (PMF.uniformOfFintype (Bits lambda)).map (fun seed =>
        honestData category M A' B' Cc' Qc' st' (prgVector p salt count enough e seed)) := by
  rw [honestData_uniform_of_prg category p salt count enough e hprg,
    honestData_uniform_of_prg category p salt count enough e hprg]

end
end SDitH.Proofs.PRGHypothesis
