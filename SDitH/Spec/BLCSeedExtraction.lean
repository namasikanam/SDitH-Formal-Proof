import SDitH.Spec.BLCReconstructionChain

/-! Completing one execution's leaf seeds from two chain executions whose
hidden indices differ at that execution. The merged vector is defined
pointwise from the two revealed maps. The failure event asks whether a unique
complete vector agreeing with both revealed maps exists. This is a seed-vector
statement about the defined game; it is not a witness extractor, not
signature acceptance, and does not resolve any source binding. -/

namespace SDitH.Spec.BLCSeedExtraction

open BAVC BLCHashChain BLCReconstructionChain

variable {lambda tau N : Nat} {Key Block Context Error : Type*}

/-- The two revealed maps agree at every leaf of execution e revealed by both. -/
def Consistent (left right : Reconstructed lambda tau N) (e : Fin tau) : Prop :=
  ∀ (i : Fin N) (ls rs : Seed lambda), left.seeds e i = some ls → right.seeds e i = some rs → ls = rs

/-- A complete leaf-seed vector agreeing with both revealed maps at execution e. -/
def Agrees (left right : Reconstructed lambda tau N) (e : Fin tau) (full : Fin N → Seed lambda) : Prop :=
  (∀ (i : Fin N) (s : Seed lambda), left.seeds e i = some s → full i = s) ∧
    ∀ (i : Fin N) (s : Seed lambda), right.seeds e i = some s → full i = s

/-- Pointwise merge preferring the left map. The all-false value is only a
placeholder at a coordinate revealed by neither side; uniqueness below shows
that no such coordinate exists when the hidden indices differ. -/
def merge (left right : Reconstructed lambda tau N) (e : Fin tau) (i : Fin N) : Seed lambda :=
  match left.seeds e i with
  | some s => s
  | none =>
    match right.seeds e i with
    | some s => s
    | none => fun _ => false

/-- Failure: both chains succeed with equal line digests, some execution has
different hidden indices, and no unique complete seed vector agrees with both. -/
noncomputable def extractionFails (out : HashCipher.Result (List Bool) (Digest lambda) Key Block
    (ChainProgram lambda Key Block (Checked lambda tau N Key Block Context Error))) : Bool := by
  classical
  exact match out.state with
  | .done checked => match checked.left, checked.right with
    | .ok left, .ok right => decide (left.hashes.lines = right.hashes.lines ∧
        ∃ e : Fin tau, checked.claim.left.opening.hidden e ≠ checked.claim.right.opening.hidden e ∧
          ¬ ∃ full : Fin N → Seed lambda, Agrees left.reconstruction right.reconstruction e full ∧
            ∀ other, Agrees left.reconstruction right.reconstruction e other → other = full)
    | _, _ => false
  | .hash _ _ | .cipher _ _ => false

end SDitH.Spec.BLCSeedExtraction
