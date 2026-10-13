import SDitH.Spec.IdealCipher

/-! Events for the two-call seed-collision argument. A witnessed pair records
one matching half in the observed graph and tests the companion half in the
same hidden family. The event can therefore occur before all four calls have
been made. FirstPair identifies a new matching half with an unobserved companion. -/

namespace SDitH.Spec.IdealCipherPairCollision

open IdealCipher

variable {Key Block Tag : Type*}

def Unseen (history : List (Entry Key Block)) (key : Key) (input : Block) : Prop :=
  ∀ e ∈ history, e.key = key → e.input ≠ input

def FirstHalf (project : Block → Tag) (history : List (Entry Key Block))
    (newest old : Entry Key Block) : Prop :=
  Unseen history newest.key newest.input ∧ newest.key ≠ old.key ∧
    newest.input = old.input ∧ project newest.output = project old.output

def PairWitness (project : Block → Tag) (companion : Block → Block)
    (family : Family Key Block) (left right : Entry Key Block) : Prop :=
  left.key ≠ right.key ∧ left.input = right.input ∧ project left.output = project right.output ∧
    project (family left.key (companion left.input)) = project (family right.key (companion left.input))

def Witnessed (project : Block → Tag) (companion : Block → Block)
    (family : Family Key Block) (history : List (Entry Key Block)) : Prop :=
  ∃ left ∈ history, ∃ right ∈ history, PairWitness project companion family left right

def FirstPair (project : Block → Tag) (companion : Block → Block) (family : Family Key Block)
    (history : List (Entry Key Block)) (newest old : Entry Key Block) : Prop :=
  Unseen history newest.key newest.input ∧ PairWitness project companion family newest old ∧
    (Unseen (newest :: history) newest.key (companion newest.input) ∨
     Unseen (newest :: history) old.key (companion newest.input))

end SDitH.Spec.IdealCipherPairCollision
