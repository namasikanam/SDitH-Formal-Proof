import SDitH.Spec.Parameters

/-! Complete Tables 4/5, printed pp. 40–41, and the distinct parameter-selection
prose on p. 39. The latter is recorded separately because it disagrees with
the tables. These are literal data and numerical formulas, not cryptographic
security claims or a byte codec. No table is silently corrected from the prose.
-/

namespace SDitH.Spec.MainParameterTables

open RSDParameters

inductive Tradeoff where
  | short
  | fast
  deriving DecidableEq, Repr

structure Row where
  rsd : RSDParameters
  tradeoff : Tradeoff
  proof : ProofParameters
  publicBytes : Nat
  secretBytes : Nat
  signatureBytes : Nat
  deriving DecidableEq, Repr

def table4 : List Row :=
  [⟨categoryI, .short, ⟨11,11,9,109,16⟩, 70,147,3721⟩,
   ⟨categoryI, .fast, ⟨7,18,4,107,16⟩, 70,147,4914⟩,
   ⟨categoryIII, .short, ⟨11,17,7,169,16⟩, 98,208,8484⟩,
   ⟨categoryIII, .fast, ⟨7,27,5,161,16⟩, 98,208,10852⟩,
   ⟨categoryV, .short, ⟨11,23,5,228,16⟩, 132,275,15147⟩,
   ⟨categoryV, .fast, ⟨7,36,6,216,16⟩, 132,275,19144⟩]

def table5 : List Row :=
  [⟨categoryI, .short, ⟨11,11,9,109,16⟩, 70,147,3721⟩,
   ⟨categoryI, .fast, ⟨7,17,11,101,16⟩, 70,147,4643⟩,
   ⟨categoryIII, .short, ⟨11,17,7,169,16⟩, 98,208,8484⟩,
   ⟨categoryIII, .fast, ⟨7,26,12,155,16⟩, 98,208,10452⟩,
   ⟨categoryV, .short, ⟨11,23,5,228,16⟩, 132,275,15147⟩,
   ⟨categoryV, .fast, ⟨7,36,6,216,16⟩, 132,275,19144⟩]

def rowsFor (tradeoff : Tradeoff) (rows : List Row) : List Row :=
  rows.filter (fun row => row.tradeoff == tradeoff)

/-- Prose N=2^11,2^12,2^12 for short variants, in category order I/III/V. -/
def proseShortKappas : List Nat := [11,12,12]

/-- Prose N=2^8 for every fast variant. -/
def proseFastKappa : Nat := 8

def proseFastGrinding : Nat := 2

/-- The prose gives a set, not a category-indexed list. -/
def proseShortGrindingValues : List Nat := [2,6,9]

end SDitH.Spec.MainParameterTables
