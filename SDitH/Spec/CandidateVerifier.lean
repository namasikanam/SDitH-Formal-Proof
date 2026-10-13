import SDitH.Spec.SharedScheme
import SDitH.Spec.BLCSeedLines

/-! A named candidate for Algorithm 12 lines 9–21 as a verifier middle
program. The undeclared `seed` array is bound to the reconstruction's own
revealed seeds (the fold never reads the hidden index), `rshare` starts at
zero, `phi_mu` is the Gray row, the consistency mask is the mask-oracle
answer at the auxiliary digest, and line 21 is read as the binary equation
base = [I|M]·Q - plain ⊗ Gray(hidden). This is an explicitly identified
candidate target, kept separate from the literal prefix in BLCRecompute. -/

namespace SDitH.Spec.CandidateVerifier

open BAVC DomainSeparation BAVCChainInputs BLCRecompute HashCipherProgram ConsistencyMatrix SharedScheme
open Spec.SlopeConsistencyGame (Out)
open scoped Classical
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- Bindings for the literal fold using the reconstruction's revealed seeds. -/
def reconstructionBindings (nodes : NodesBinding lambda tau (2 ^ kappa)) (recon : Reconstructed lambda tau (2 ^ kappa)) :
    Bindings lambda tau kappa (s + (wit + rnd)) :=
  ⟨nodes, some recon.seeds, fun _ => some 0, some (fun _ i j => GrayCode.grayFieldRow i j)⟩

/-- Candidate line 21: the base matrix solving the displayed consistency
equation columnwise in the binary field. -/
def candidateBase (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)) (plain : Fin s → ZMod 2)
    (hidden : Fin tau → Fin (2 ^ kappa)) (Q : Fin (s + (wit + rnd)) → Fin tau → Fin kappa → ZMod 2) :
    Fin s → Fin tau → Fin kappa → ZMod 2 :=
  fun a e j => BLC.consistencyColumns M Q a e j - plain a * GrayCode.grayFieldRow (hidden e) j

/-- The candidate middle: mask query, literal fold with the reconstruction
bindings, candidate line 21, and the suffix's witness/randomness values. -/
def candidateMiddle {F : Type*} [Field F] [Algebra (ZMod 2) F] (xi : F)
    (p : BLCCommit.Primitives lambda tau kappa s wit rnd) (nodes : NodesBinding lambda tau (2 ^ kappa))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount) :
    VerifierMiddle F lambda tau kappa s wit rnd :=
  fun salt aux hidden recon auxiliary => Program.hash (maskInput auxiliary) fun answer =>
    match foldExecutionsThrough p salt (reconstructionBindings nodes recon) aux hidden randomCount enough tau le_rfl with
    | Except.error cause => Program.done (Except.error cause)
    | Except.ok folded =>
      match collectShares folded with
      | Except.error cause => Program.done (Except.error cause)
      | Except.ok shares =>
        let Q := concatenate shares
        let delta := (encode hidden)⁻¹
        Program.done (Except.ok (delta,
          fun j => algebraMap (ZMod 2) F (aux.witnessCorrection j) + delta * BLC.psi xi (Q (BLC.witnessIndex j)),
          fun j => delta * BLC.psi xi (Q (BLC.randomnessIndex j)),
          candidateBase answer.2 aux.plain hidden Q))

end
end SDitH.Spec.CandidateVerifier
