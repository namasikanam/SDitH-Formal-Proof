import SDitH.Spec.SharedSigning
import SDitH.Proofs.SharedSigner
import SDitH.Proofs.HashCipherTrace
import SDitH.Proofs.OracleProgram

/-! Support characterizations of the shared-model signing services: every
prepared signing state comes from an executed commitment that evaluates on
the resulting world's table and cipher history, with the payload and state
read from it; the opening service is deterministic; and every honest
signature with a body carries the salt, auxiliary data, opening and higher
coefficients of such a state, with its digest stored at the typed HashPiop
input in the resulting hash table. -/

namespace SDitH.Proofs.SharedSigning

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.HashCipherEvaluation Spec.SharedScheme
open Spec.SharedSigner Spec.SharedSigning Spec.AbstractSignature Spec.SignatureSecurity
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- A run of a program on the world: the final state is a value evaluating
on the final table and cipher history, and the family is unchanged. -/
theorem runProgram_support {A : Type*} {wit rnd : Nat} (budget : Nat)
    (program : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (hbound : Bounded budget program) (world : World lambda s wit rnd)
    (result : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A × World lambda s wit rnd)
    (hr : result ∈ (runProgram budget program world).support) :
    ∃ value, result.1 = Program.done value ∧
      Evaluates world.family result.2.hashTable result.2.cipherHistory program value ∧
      result.2.family = world.family := by
  obtain ⟨out, hout, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  have hforget : Spec.HashCipherTrace.forget out ∈
      (Spec.HashCipher.runFixed procedure world.family budget program world.hashTable world.hashHistory
        world.cipherHistory).support := by
    rw [← HashCipherTrace.runFixed_forget]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨out, hout, rfl⟩
  obtain ⟨value, hstate, heval⟩ := HashCipherEvaluation.run_evaluates world.family program budget hbound _ _ _ _ hforget
  subst hres
  exact ⟨value, hstate, heval, rfl⟩

theorem prepareSigning_support [NeZero tau] (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (publicKey : List Bool) (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (result : Payload F lambda higherCount ×
      SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount ×
      World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hr : result ∈ (prepareSigning S publicKey witness message world).support) :
    ∃ (salt root : Bits lambda) (committed : Committed F lambda tau kappa s (selectorCount widths * w)
        (lambda * (widths.length - 1))),
      Evaluates world.family result.2.2.hashTable result.2.2.cipherHistory (commitProgram S.signer salt root witness)
        committed ∧
      result.1 = (stateOf S salt committed).1 ∧ result.2.1 = (stateOf S salt committed).2 ∧
      result.2.2.family = world.family := by
  obtain ⟨salt, _, hsalt⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨root, _, hroot⟩ := (PMF.mem_support_bind_iff _ _ _).mp hsalt
  obtain ⟨run, hrun, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hroot
  obtain ⟨committed, hstate, heval, hfam⟩ := runProgram_support (commitBudget tau kappa) _
    (SharedSigner.commit_bounded S.signer salt root witness) world run hrun
  refine ⟨salt, root, committed, ?_, ?_, ?_, ?_⟩
  · rw [← hres, hstate]
    exact heval
  · rw [← hres, hstate]
  · rw [← hres, hstate]
  · rw [← hres, hstate]
    exact hfam

omit [Algebra (ZMod 2) F] in
theorem openSigning_support [DecidableEq F] (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (state : SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)
    (digest : Digest lambda) (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (result : Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount) ×
      World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hr : result ∈ (openSigning S state digest world).support) :
    result.2 = world ∧
      ((∃ counter opening, Spec.BLCRetry.openRandomEvaluation state.key S.Topen (S.expandEvaluation digest) S.encode S.fuel =
          .returned counter opening ∧ result.1 = some (state.salt, state.auxiliary, (counter, opening), state.higher)) ∨
        result.1 = none) := by
  rw [openSigning, PMF.mem_support_pure_iff] at hr
  subst hr
  refine ⟨rfl, ?_⟩
  cases h : Spec.BLCRetry.openRandomEvaluation state.key S.Topen (S.expandEvaluation digest) S.encode S.fuel with
  | pending _ => right; rfl
  | undefined _ => right; rfl
  | returned counter opening => left; exact ⟨counter, opening, rfl, rfl⟩

/-- Every honest signature of the composed scheme with a body comes from a
prepared state of an executed commitment: its salt, auxiliary data and
higher coefficients are the state's, its opening is Algorithm 11's return
on its digest, and the digest is stored at the typed HashPiop input of the
payload in the resulting hash table. The shared world of the output is the
world after the commitment program. -/
theorem sign_support [NeZero tau] [DecidableEq F] (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
    (pk : List Bool) (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (result : Signature (Digest lambda)
        (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (hr : result ∈ ((scheme (components S V verifyBudget publicKey sampleWitness)).sign (pk, witness) message world).support) :
    ∃ (salt root : Bits lambda) (committed : Committed F lambda tau kappa s (selectorCount widths * w)
        (lambda * (widths.length - 1))),
      Evaluates world.other.family result.2.other.hashTable result.2.other.cipherHistory
        (commitProgram S.signer salt root witness) committed ∧
      result.2.other.family = world.other.family ∧
      result.2.hashTable ⟨pk, message, (stateOf S salt committed).1⟩ = some result.1.piop ∧
      (result.1.body = none ∨
        ∃ counter opening, Spec.BLCRetry.openRandomEvaluation (stateOf S salt committed).2.key S.Topen
            (S.expandEvaluation result.1.piop) S.encode S.fuel = .returned counter opening ∧
          result.1.body = some (salt, committed.result.auxiliary, (counter, opening),
            (stateOf S salt committed).2.higher)) := by
  obtain ⟨prepared, hprep, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨hashed, hhash, hopen⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  obtain ⟨opened, hopened, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hopen
  obtain ⟨salt, root, committed, heval, hpayload, hstate, hfam⟩ :=
    prepareSigning_support S pk witness message world.other prepared hprep
  have hstored := OracleProgram.query_stores_answer world.hashTable _ hashed hhash
  obtain ⟨hworld, hbody⟩ := openSigning_support S prepared.2.1 hashed.1 prepared.2.2 opened hopened
  subst hres
  refine ⟨salt, root, committed, ?_, ?_, ?_, ?_⟩
  · show Evaluates world.other.family opened.2.hashTable opened.2.cipherHistory _ committed
    rw [hworld]
    exact heval
  · show opened.2.family = world.other.family
    rw [hworld]
    exact hfam
  · show hashed.2 ⟨pk, message, (stateOf S salt committed).1⟩ = some hashed.1
    rw [← hpayload]
    exact hstored
  · rcases hbody with ⟨counter, opening, hret, hsome⟩ | hnone
    · right
      refine ⟨counter, opening, ?_, ?_⟩
      · rw [← hstate]
        exact hret
      · show opened.1 = _
        rw [hsome, hstate]
        rfl
    · left
      exact hnone

end
end SDitH.Proofs.SharedSigning
