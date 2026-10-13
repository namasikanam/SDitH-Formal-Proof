import SDitH.Spec.IdealCipherProgram
import SDitH.Spec.IdealCipherPipeline
import SDitH.Spec.SeedPrimitives
import SDitH.Spec.IdealCipherSeed

/-! Both seed commitments are computed on the adversary's shared cipher. Four
calls are made, including repeated or previously unqueried inputs. The claim's
two inputs are explicit; the source definitions use the literal two tweaks. -/

namespace SDitH.Spec.SeedVerification

open IdealCipher OracleProgram DomainSeparation SeedPrimitives

structure Claim (Key Block : Type*) where
  left : Key
  right : Key
  firstInput : Block
  secondInput : Block

structure Checked (Key Block Tag : Type*) where
  claim : Claim Key Block
  left : Tag × Tag
  right : Tag × Tag

variable {Key Block Tag State : Type*}

def commitProgram (project : Block → Tag) (key : Key) (left right : Block) :
    Program (Query Key Block) Block (Tag × Tag) :=
  .query (.encrypt key left) fun first =>
    .query (.encrypt key right) fun second => .done (project first, project second)

def verifyProgram (project : Block → Tag) (claim : Claim Key Block) :
    Program (Query Key Block) Block (Checked Key Block Tag) :=
  OracleProgram.bind (commitProgram project claim.left claim.firstInput claim.secondInput) fun left =>
    OracleProgram.bind (commitProgram project claim.right claim.firstInput claim.secondInput) fun right =>
      .done ⟨claim, left, right⟩

abbrev VerificationState (Key Block Tag : Type*) := Program (Query Key Block) Block (Checked Key Block Tag)

def checked (family : Family Key Block) (project : Block → Tag) (claim : Claim Key Block) : Checked Key Block Tag :=
  ⟨claim, (project (family claim.left claim.firstInput), project (family claim.left claim.secondInput)),
    (project (family claim.right claim.firstInput), project (family claim.right claim.secondInput))⟩

/-- Newest-first log, matching the interpreter's order. -/
def verificationTrace (family : Family Key Block) (claim : Claim Key Block) : List (Entry Key Block) :=
  [⟨claim.right, claim.secondInput, family claim.right claim.secondInput⟩,
   ⟨claim.right, claim.firstInput, family claim.right claim.firstInput⟩,
   ⟨claim.left, claim.secondInput, family claim.left claim.secondInput⟩,
   ⟨claim.left, claim.firstInput, family claim.left claim.firstInput⟩]

noncomputable def wins (out : Result Key Block (VerificationState Key Block Tag)) : Bool := by
  classical
  exact match out.state with
  | .query _ _ => false
  | .done value => decide (value.claim.left ≠ value.claim.right ∧ value.left = value.right)

noncomputable def experiment [Fintype Key] [Fintype Block]
    (adversary : Procedure Key Block State) (q : Nat) (initial : State)
    (project : Block → Tag) (choose : State → Claim Key Block) :
    PMF (Result Key Block (VerificationState Key Block Tag)) :=
  IdealCipherPipeline.experiment adversary q initial IdealCipherProgram.procedure 4
    (fun state => verifyProgram project (choose state))

structure SourceClaim (lambda leaves : Nat) where
  salt : Bits lambda
  left : Bits lambda
  right : Bits lambda
  index : Fin leaves

def fullClaim {lambda leaves : Nat} (variant : Grinding) (claim : SourceClaim lambda leaves) : Claim (Bits lambda) (Bits lambda) :=
  ⟨claim.left, claim.right, cipherInput variant claim.salt (leaves + claim.index.val) false,
    cipherInput variant claim.salt (leaves + claim.index.val) true⟩

def truncatedClaim {leaves : Nat} (variant : Grinding) (claim : SourceClaim 192 leaves) : Claim (Bits 256) (Bits 256) :=
  ⟨pad192 claim.left, pad192 claim.right, pad192 (cipherInput variant claim.salt (leaves + claim.index.val) false),
    pad192 (cipherInput variant claim.salt (leaves + claim.index.val) true)⟩

noncomputable def fullExperiment {lambda leaves : Nat}
    (variant : Grinding) (adversary : Procedure (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → SourceClaim lambda leaves) :=
  experiment adversary q initial id (fun state => fullClaim variant (choose state))

noncomputable def truncatedExperiment {leaves : Nat}
    (variant : Grinding) (adversary : Procedure (Bits 256) (Bits 256) State)
    (q : Nat) (initial : State) (choose : State → SourceClaim 192 leaves) :=
  experiment adversary q initial IdealCipherSeed.project192 (fun state => truncatedClaim variant (choose state))

/-- The literal same-salt, same-index source commitment collision predicate.
It has no transcript-membership, freshness or program-completion condition. -/
noncomputable def sourceWins {lambda leaves : Nat} (variant : Grinding)
    (encStar : Bits lambda → Bits lambda → Bits lambda) (claim : SourceClaim lambda leaves) : Bool := by
  classical
  exact decide (claim.left ≠ claim.right ∧
    commitSeed leaves variant encStar claim.salt claim.left claim.index.val =
      commitSeed leaves variant encStar claim.salt claim.right claim.index.val)

noncomputable def directExperiment [Fintype Key] [Fintype Block]
    (adversary : Procedure Key Block State) (q : Nat) (initial : State)
    (test : Family Key Block → State → Bool) : PMF Bool := by
  classical
  exact (PMF.uniformOfFintype (Family Key Block)).bind fun family =>
    (runFixed adversary family q initial []).map (test family ∘ Result.state)

noncomputable def directFullExperiment {lambda leaves : Nat}
    (variant : Grinding) (adversary : Procedure (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → SourceClaim lambda leaves) : PMF Bool :=
  directExperiment adversary q initial fun family state =>
    sourceWins variant (fun key input => family key input) (choose state)

noncomputable def directTruncatedExperiment {leaves : Nat}
    (variant : Grinding) (adversary : Procedure (Bits 256) (Bits 256) State)
    (q : Nat) (initial : State) (choose : State → SourceClaim 192 leaves) : PMF Bool :=
  directExperiment adversary q initial fun family state =>
    sourceWins variant (encStarIII (fun key input => family key input)) (choose state)

end SDitH.Spec.SeedVerification
