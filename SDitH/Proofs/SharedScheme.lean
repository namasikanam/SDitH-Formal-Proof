import SDitH.Spec.SharedScheme
import SDitH.Proofs.SignatureReplayConsistency
import SDitH.Proofs.HashCipherEvaluation

/-! Glue for the shared-model scheme: the two accepted attempts of a
successful fork share the typed hash input, hence its public key, message,
lines digest and coefficient tuple; and a digest-answered program lifted to
the product-valued oracle evaluates exactly against the digest projection
of the table. These are the first links between the forking step and the
executed verification chain. -/

namespace SDitH.Proofs.SharedScheme

open Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.SharedScheme
open Spec.HashCipherProgram Spec.HashCipherEvaluation Spec.DomainSeparation
open Spec.SlopeConsistencyGame (Out)
open scoped Classical
noncomputable section

/-- The two accepted attempts of a successful fork have the same typed hash
input: public key, message and payload coincide, while the targets differ. -/
theorem fork_attempts_share_input {PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer State : Type*}
    [Fintype Digest] [Nonempty Digest]
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (snapshot : Snapshot PublicKey (PublicKey × SecretKey) Message
      (HashInput PublicKey Message Payload) Digest Other Query State)
    (result : Option (Branch Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query ×
      Branch Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query))
    (hr : result ∈ (forkAt (scheme components) adversary snapshot).support)
    (hw : forkWins snapshot.input result = true) :
    ∃ left right a b, result = some (left, right) ∧
      left.checked.terminal = .attempt a ∧ right.checked.terminal = .attempt b ∧
      a.input.publicKey = b.input.publicKey ∧ a.input.message = b.input.message ∧
      a.input.payload = b.input.payload ∧ a.target ≠ b.target := by
  obtain ⟨left, right, a, b, hres, ha, hb, _, _, hai, hbi, _, _, hne⟩ :=
    SignatureReplayConsistency.successful_fork_attempts components adversary snapshot result hr hw
  have hinput : a.input = b.input := hai.trans hbi.symm
  exact ⟨left, right, a, b, hres, ha, hb, by rw [hinput], by rw [hinput], by rw [hinput], hne⟩

/-- For the typed SDitH payload, shared payload means shared lines digest
and shared restored coefficient tuple. -/
theorem shared_payload_fields {F : Type*} {lambda higherCount : Nat}
    (p q : Spec.BAVC.Digest lambda × (Fin (higherCount + 1) → F)) (h : p = q) :
    p.1 = q.1 ∧ p.2 = q.2 := by
  subst h
  exact ⟨rfl, rfl⟩

variable {lambda s wit rnd : Nat}

/-- A lifted program evaluates against the digest projection of the table. -/
theorem liftFirst_evaluates {A : Type*} (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (program : Program (List Bool) (Spec.BAVC.Digest lambda) (Bits lambda) (Bits lambda) A) (value : A) :
    Evaluates family table ciphers (liftFirst (s := s) (wit := wit) (rnd := rnd) program) value ↔
      Evaluates family (fun x => (table x).map Prod.fst) ciphers program value := by
  induction program with
  | done a =>
    constructor
    · intro h
      cases h
      exact .done _
    · intro h
      cases h
      exact .done _
  | hash input next ih =>
    constructor
    · intro h
      cases h with
      | hash _ _ answer _ stored tail =>
        exact .hash input next answer.1 value (by rw [stored]; rfl) ((ih answer.1).mp tail)
    · intro h
      cases h with
      | hash _ _ answer _ stored tail =>
        obtain ⟨pair, hpair, hd⟩ := Option.map_eq_some_iff.mp stored
        refine .hash input _ pair value hpair ?_
        rw [hd]
        exact (ih answer).mpr tail
  | cipher request next ih =>
    constructor
    · intro h
      cases h with
      | cipher _ _ _ recorded tail =>
        exact .cipher request next value recorded ((ih _).mp tail)
    · intro h
      cases h with
      | cipher _ _ _ recorded tail =>
        exact .cipher request _ value recorded ((ih _).mpr tail)

end
end SDitH.Proofs.SharedScheme
