import SDitH.Spec.BLCRecompute

/-! Extractor-side environment for Algorithm 12's folding loop. A complete
seed vector supplies the undeclared `seed` array, every `rshare` starts at
zero and `phi_mu` is the Gray row. These are explicit environment values used
by an extractor for its own computation; they are not a claim about the
source's intended bindings, and the source's absent-binding behavior is kept
separately in `BLCRecompute.prepare`. The slope and intercept are computed
from the seed vector and the transmitted auxiliary data only. -/

namespace SDitH.Spec.BLCSeedFold

open BLCRecompute DomainSeparation

variable {lambda tau kappa s wit rnd : Nat}

def extractedBindings (nodes : BAVC.NodesBinding lambda tau (2 ^ kappa))
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) : Bindings lambda tau kappa (s + (wit + rnd)) :=
  ⟨nodes, some (fun e i => some (full e i)), fun _ => some 0, some (fun _ i j => GrayCode.grayFieldRow i j)⟩

/-- Lines 15–16 as read by the verifier: the transmitted slot e-1 for
positive e, nothing at e=0. -/
def correctionTerm (aux : BLCCommit.Auxiliary tau s wit rnd) (e : Fin tau)
    (c : Fin (s + (wit + rnd))) : ZMod 2 :=
  if he : 0 < e.val then aux.corrections (correctionIndex e he) c else 0

/-- The direct Algorithm-10 fold of the extracted leaf randomness at one execution. -/
def folded (p : BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (e : Fin tau) : BLC.Folded (ZMod 2) (s + (wit + rnd)) kappa :=
  BLC.foldExecution GrayCode.grayFieldRow (BLCCommit.randomTable p salt full randomCount enough e)

def slope (p : BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : BLCCommit.Auxiliary tau s wit rnd)
    (e : Fin tau) (c : Fin (s + (wit + rnd))) : ZMod 2 :=
  (folded p salt full randomCount enough e).acc c + correctionTerm aux e c

def intercept (p : BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (e : Fin tau) (c : Fin (s + (wit + rnd)))
    (j : Fin kappa) : ZMod 2 :=
  (folded p salt full randomCount enough e).base c j

/-- The value the verifier's fold produces at hidden index i, as an affine
function of the Gray row of i. -/
def affine (p : BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : BLCCommit.Auxiliary tau s wit rnd)
    (e : Fin tau) (i : Fin (2 ^ kappa)) (c : Fin (s + (wit + rnd))) (j : Fin kappa) : ZMod 2 :=
  slope p salt full randomCount enough aux e c * GrayCode.grayFieldRow i j +
    intercept p salt full randomCount enough e c j

end SDitH.Spec.BLCSeedFold
