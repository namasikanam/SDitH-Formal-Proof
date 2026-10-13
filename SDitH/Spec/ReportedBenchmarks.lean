import SDitH.Spec.MainParameterTables

/-! Human/empirical boundary: the numbers reported in Table 6, printed p. 41.
These definitions transcribe reported medians. No theorem identifies them with
measured executions of this Lean specification or a reference implementation.
Raw observations, measurement conditions and reproducibility require external
evidence. Storing these numbers as data is not a proof of their empirical truth.
-/

namespace SDitH.Spec.ReportedBenchmarks

open MainParameterTables

def processor : String := "Intel Xeon Platinum 8259CL CPU @ 2.50GHz"
def runs : Nat := 10000
def statistic : String := "median"

/-- Reported cycle counts, converting the displayed Mc decimal numbers
exactly (1 Mc = 1,000,000 cycles). These retain the precision of the report,
not an assertion that the underlying unrounded median is this integer. -/
structure Timings where
  keygen : Nat
  sign : Nat
  verify : Nat
  deriving DecidableEq, Repr

structure Row where
  lambda : Nat
  tradeoff : Tradeoff
  hashGrinding : Timings
  cipherGrinding : Timings
  deriving DecidableEq, Repr

def table6 : List Row :=
  [⟨128, .short, ⟨66000,10140000,9040000⟩, ⟨67000,9210000,9010000⟩⟩,
   ⟨128, .fast, ⟨66000,2110000,1860000⟩, ⟨66000,2080000,1780000⟩⟩,
   ⟨192, .short, ⟨96000,36930000,36110000⟩, ⟨96000,37050000,36670000⟩⟩,
   ⟨192, .fast, ⟨96000,8040000,7390000⟩, ⟨97000,8490000,7270000⟩⟩,
   ⟨256, .short, ⟨148000,55940000,55210000⟩, ⟨148000,57050000,56270000⟩⟩,
   ⟨256, .fast, ⟨148000,12210000,11330000⟩, ⟨148000,12430000,11610000⟩⟩]

end SDitH.Spec.ReportedBenchmarks
