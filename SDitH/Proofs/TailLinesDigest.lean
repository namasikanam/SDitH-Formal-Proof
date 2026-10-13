import SDitH.Proofs.CommitSplitRun
import SDitH.Proofs.FreshHashUniform

/-! The tail's lines digest. The witness-dependent tail is a single hash
query at the lines input followed by the committed result, whose lines
digest is the query's digest answer. When the lines input is absent from
the table reached by the prefix, that digest is uniform whatever the
witness, so the honest and simulated signers' lines digests have the same
distribution whenever both lines inputs are fresh. -/

namespace SDitH.Proofs.TailLinesDigest

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives
open Spec.HashCipherTrace Spec.RandomOracle
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The lines query input of a witness's tail. -/
def linesInput {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (S : SignerSetting F lambda tau kappa s wit rnd)
    (salt : Bits lambda) (witness : Fin wit → ZMod 2) (data : PrefixData lambda tau kappa s wit rnd) : List Bool :=
  let nodes := data.1
  let auxiliary := data.2.2.2.2.1
  let maskAnswer := data.2.2.2.2.2
  let random := Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough
  let arithmetic := Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow random maskAnswer.2 witness
  Spec.BLCHashChain.linesQuery auxiliary.1
    (S.linesTail arithmetic.plainCheck arithmetic.baseCheck arithmetic.witnessCorrection)

/-- The committed result of a witness's tail given the lines digest. -/
def committedOf {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (S : SignerSetting F lambda tau kappa s wit rnd)
    (salt : Bits lambda) (witness : Fin wit → ZMod 2) (data : PrefixData lambda tau kappa s wit rnd)
    (lines : Out lambda s wit rnd) : Committed F lambda tau kappa s wit rnd :=
  let nodes := data.1
  let commits := data.2.1
  let rowHashes := data.2.2.1
  let outer := data.2.2.2.1
  let auxiliary := data.2.2.2.2.1
  let maskAnswer := data.2.2.2.2.2
  let random := Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough
  let arithmetic := Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow random maskAnswer.2 witness
  ⟨⟨arithmetic.witnessLines, arithmetic.randomnessLines, lines.1, ⟨fun a => nodes a.val, fun e i => commits (e, i)⟩,
    ⟨Spec.BLCCommit.positiveCorrections (Spec.BLC.correction Spec.GrayCode.grayFieldRow random),
      arithmetic.plainCheck, arithmetic.witnessCorrection⟩⟩,
    fun e i => nodes (leafNode e i).val, rowHashes, outer.1, auxiliary.1, maskAnswer.2⟩

theorem commitTail_eq {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (S : SignerSetting F lambda tau kappa s wit rnd)
    (salt : Bits lambda) (witness : Fin wit → ZMod 2) (data : PrefixData lambda tau kappa s wit rnd) :
    commitTail S salt witness data =
      Program.hash (linesInput S salt witness data) fun lines => Program.done (committedOf S salt witness data lines) := rfl

/-- The committed lines digest of a run result. -/
def linesDigestOf {F : Type*} [CommRing F]
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd))) :
    Option (Digest lambda) :=
  match out.state with
  | .done committed => some committed.result.lines
  | _ => none

/-- The tail's lines digest at a fresh lines input is uniform, whatever the
witness. -/
theorem tail_linesDigest_uniform {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd)))
    (data : PrefixData lambda tau kappa s wit rnd) (hstate : out.state = .done data)
    (hfresh : out.hashTable (linesInput S salt witness data) = none) :
    (continueRun family 1 (commitTail S salt witness) out).map linesDigestOf =
      (PMF.uniformOfFintype (Out lambda s wit rnd)).map (fun pair => some pair.1) := by
  have hstep : (procedure : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd))).step
        (.hash (linesInput S salt witness data) fun lines => Program.done (committedOf S salt witness data lines)) =
      PMF.pure (.hash (linesInput S salt witness data) fun lines => Program.done (committedOf S salt witness data lines)) :=
    rfl
  unfold continueRun
  rw [hstate]
  simp only [commitTail_eq, runFixed, hstep, PMF.pure_bind, PMF.map_bind, PMF.map_comp]
  rw [← FreshHashUniform.query_fresh_uniform out.hashTable (linesInput S salt witness data) hfresh, PMF.map_comp]
  congr 1
  · congr
    exact Subsingleton.elim _ _
  · funext result
    simp [PMF.pure_map, mark, linesDigestOf, committedOf]

/-- The two witnesses' tails have the same lines-digest distribution when both
lines inputs are fresh. -/
theorem tail_linesDigest_congr {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness fake : Fin wit → ZMod 2)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd)))
    (data : PrefixData lambda tau kappa s wit rnd) (hstate : out.state = .done data)
    (hfresh : out.hashTable (linesInput S salt witness data) = none)
    (hfresh' : out.hashTable (linesInput S salt fake data) = none) :
    (continueRun family 1 (commitTail S salt witness) out).map linesDigestOf =
      (continueRun family 1 (commitTail S salt fake) out).map linesDigestOf := by
  rw [tail_linesDigest_uniform S salt witness family out data hstate hfresh,
    tail_linesDigest_uniform S salt fake family out data hstate hfresh']

end
end SDitH.Proofs.TailLinesDigest
