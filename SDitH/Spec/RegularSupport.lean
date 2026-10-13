import SDitH.Spec.UniformChallenges
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Perm

/-! The support-counting experiment of §5.1, printed pp. 42–43.
Here n = w*m, and the product index records the w consecutive chunks of
size m explicitly. A uniform permutation acts on one fixed weight-w support.
This event is distinct from the existence of some regular solution to a
permuted syndrome-decoding instance. No conditional solver distribution or
heuristic uniqueness estimate is assumed here. -/

namespace SDitH.Spec.RegularSupport

noncomputable section
open scoped Classical

abbrev Coordinate (w m : Nat) := Fin w × Fin m

/-- Exactly one occupied coordinate in every chunk. -/
def Regular {w m : Nat} (support : Finset (Coordinate w m)) : Prop :=
  ∀ i, ∃! j, (i, j) ∈ support

def graph {w m : Nat} (positions : Fin w → Fin m) : Finset (Coordinate w m) :=
  Finset.univ.image (fun i => (i, positions i))

/-- All supports of weight w in w*m coordinates. -/
def weightSupports (w m : Nat) : Finset (Finset (Coordinate w m)) :=
  Finset.univ.powersetCard w

def permute {A : Type*} (sigma : Equiv.Perm A) (support : Finset A) : Finset A :=
  support.image sigma

end
end SDitH.Spec.RegularSupport
