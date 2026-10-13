import SDitH.Proofs.PruneCompatClosure

/-! Prune compatibility of the fork continuation. After a signing call in
the first branch, the end-resampled event fork continues with the first
branch's run, the resampling of its final world, its finalization, the
second branch from the restored snapshot and the event read at an
end-resampled family. The continuation after the first branch's run is
compatible with pruning at any keys, given the event's compatibility at
the end (read at the second branch's final world) and its insensitivity
to the checked terminals' embedded worlds; the game run then carries the
compatibility through the first branch. -/

namespace SDitH.Proofs.ForkPruneCompat

open Spec.SignatureSecurity Spec.SignatureReplay
open Spec.IdealCipher (Family)
open Spec.RandomOracleTrap (indicator)
open Spec.DomainSeparation (Bits)
open GameResample ChargeExpect ChargeCutExpect CipherResample SharedPrune HiddenEntries RunWorld GamePrune GamePruneReverse
open GamePruneGen PruneCompatClosure ForkRestore ForkRestoreLemmas ForkRestoreEnd HiddenSlice
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat} (K : List (Bits lambda))
  (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (sn : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
  (E : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State →
    Option (Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) → Bool)
  (a : Digest)

omit [Fintype Digest] [Nonempty Digest] in
/-- Compatibility transfers along pointwise equal evaluations. -/
theorem pruneCompat_congr
    (Φ Φ' T T' : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞) (hΦ : ∀ r, Φ r = Φ' r) (hT : ∀ r, T r = T' r)
    (hc : PruneCompat K Φ T) : PruneCompat K Φ' T' := by
  have e1 : Φ = Φ' := funext hΦ
  have e2 : T = T' := funext hT
  subst e1 e2
  exact hc

/-- The event read at the end-resampled family of the second branch's final
world, for the two checked results and the second branch's answer. -/
def rightEval (c c' : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) (a' : Digest)
    (w'' : GW HashInput Digest lambda s wit rnd) : ℝ≥0∞ :=
  mean (resampleW resample w'') fun w''' =>
    indicator (E { sn with world := setFamily sn.world w'''.other.family } (some (⟨a, c⟩, ⟨a', c'⟩)))

/-- The second branch from the restored world, followed by the event. -/
def leftEval (c : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (w' : GW HashInput Digest lambda s wit rnd) : ℝ≥0∞ :=
  mean (freshBranchW sch adversary { sn with world := restore sn.world w' }) fun rw =>
    mean (resampleW resample rw.2) fun w'' =>
      indicator (E { sn with world := setFamily sn.world w''.other.family } (some (⟨a, c⟩, rw.1)))

/-- The fork continuation after the first branch's run. -/
def forkCont (r : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
    GW HashInput Digest lambda s wit rnd) : ℝ≥0∞ :=
  mean (resampleW resample r.2) fun w' => mean (finalize (withWorld r.1 w')) fun c => leftEval sch adversary sn E a c w'

variable (TE : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query →
  Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query → Digest →
  GW HashInput Digest lambda s wit rnd → ℝ≥0∞)

/-- The second branch's touching functional from the restored world. -/
def leftTouch (c : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (w' : GW HashInput Digest lambda s wit rnd) : ℝ≥0∞ :=
  mean (freshBranchW sch adversary { sn with world := restore sn.world w' }) fun rw => TE c rw.1.checked rw.1.answer rw.2

/-- The fork continuation's touching functional. -/
def forkTouch (r : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
    GW HashInput Digest lambda s wit rnd) : ℝ≥0∞ :=
  mean (resampleW resample r.2) fun w' => mean (finalize (withWorld r.1 w')) fun c => leftTouch sch adversary sn TE c w'

variable (hsignLaw : ∀ sk m, PostLaw resample (sch.sign sk m))
  (hpubLaw : ∀ q, PostLaw resample (sch.publicOracle q))
  (hprepLaw : ∀ pk m sig, PostLaw resample (sch.prepareVerification pk m sig))
  (hsignP : ∀ sk m, PruneLaw K (sch.sign sk m))
  (hpubP : ∀ q, PruneLaw K (sch.publicOracle q))
  (hprepP : ∀ pk m sig, PruneLaw K (sch.prepareVerification pk m sig))
  (hsignG : ∀ sk m, Grows (sch.sign sk m)) (hpubG : ∀ q, Grows (sch.publicOracle q))
  (hprepG : ∀ pk m sig, Grows (sch.prepareVerification pk m sig))
  (hsignK : ∀ sk m, Keeps (sch.sign sk m)) (hpubK : ∀ q, Keeps (sch.publicOracle q))
  (hprepK : ∀ pk m sig, Keeps (sch.prepareVerification pk m sig))

include hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK hprepK in
/-- The fork continuation is compatible with pruning, given the event's
compatibility at the end and its insensitivity to the checked terminals'
embedded worlds. -/
theorem forkCont_pruneCompat
    (hEleftW : ∀ sn' t w₀ f H b₁ b₂ right,
      E sn' (some (⟨a, ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩, right)) = E sn' (some (⟨a, ⟨withWorld t w₀, b₁, b₂⟩⟩, right)))
    (hErightW : ∀ sn' left t w₀ f H b₁ b₂ a',
      E sn' (some (left, ⟨a', ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩)) = E sn' (some (left, ⟨a', ⟨withWorld t w₀, b₁, b₂⟩⟩)))
    (hTEleft : ∀ t w₀ f H b₁ b₂ c' a' w, TE ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩ c' a' w = TE ⟨withWorld t w₀, b₁, b₂⟩ c' a' w)
    (hTEright : ∀ c t w₀ f H b₁ b₂ a' w, TE c ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩ a' w = TE c ⟨withWorld t w₀, b₁, b₂⟩ a' w)
    (hE : ∀ c c' a', PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
      (fun r => rightEval sn E a c c' a' r.2) (fun r => TE c c' a' r.2)) :
    PruneCompat K (forkCont sch adversary sn E a) (forkTouch sch adversary sn TE) := by
  set tr := { sn.trace with hashRequests := sn.input :: sn.trace.hashRequests } with htr
  -- the second branch's run continuation: finalization then the event
  have hΦ₂ : ∀ c a', PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
      (fun r => mean (finalize r.1) fun c' => rightEval sn E a c c' a' r.2)
      (fun r => mean (finalize r.1) fun c' => TE c c' a' r.2) := fun c a' =>
    pruneCompat_finalize K (fun c' w'' => rightEval sn E a c c' a' w'') (fun c' w'' => TE c c' a' w'')
      (fun t w₀ f H b₁ b₂ w'' => by simp only [rightEval, hErightW]) (fun t w₀ f H b₁ b₂ w'' => hTEright c t w₀ f H b₁ b₂ a' w'')
      (fun c' => hE c c' a')
  -- the second branch's run
  have hG : ∀ c a', PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
      (fun r => mean (runW sch adversary sn.remaining sn.publicKey sn.secretKey (sn.next a') r.2 tr) fun r' =>
        mean (finalize r'.1) fun c' => rightEval sn E a c c' a' r'.2)
      (fun r => mean (runW sch adversary sn.remaining sn.publicKey sn.secretKey (sn.next a') r.2 tr) fun r' =>
        mean (finalize r'.1) fun c' => TE c c' a' r'.2) := fun c a' =>
    runW_pruneCompat K sch adversary hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK hprepK _ _
      (hΦ₂ c a') sn.remaining sn.publicKey sn.secretKey (fun _ => sn.next a') (fun _ _ => rfl) (fun _ => tr) (fun _ _ => rfl)
  -- the hash update of the snapshot's input and the restoration
  have hR : ∀ c a', PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
      (fun r => mean (runW sch adversary sn.remaining sn.publicKey sn.secretKey (sn.next a')
          { restore sn.world r.2 with hashTable := Function.update (restore sn.world r.2).hashTable sn.input (some a') } tr)
        fun r' => mean (finalize r'.1) fun c' => rightEval sn E a c c' a' r'.2)
      (fun r => mean (runW sch adversary sn.remaining sn.publicKey sn.secretKey (sn.next a')
          { restore sn.world r.2 with hashTable := Function.update (restore sn.world r.2).hashTable sn.input (some a') } tr)
        fun r' => mean (finalize r'.1) fun c' => TE c c' a' r'.2) := fun c a' =>
    pruneCompat_restore K sn.world
      (fun y => mean (runW sch adversary sn.remaining sn.publicKey sn.secretKey (sn.next a')
        { y with hashTable := Function.update y.hashTable sn.input (some a') } tr)
        fun r' => mean (finalize r'.1) fun c' => rightEval sn E a c c' a' r'.2)
      (fun y => mean (runW sch adversary sn.remaining sn.publicKey sn.secretKey (sn.next a')
        { y with hashTable := Function.update y.hashTable sn.input (some a') } tr)
        fun r' => mean (finalize r'.1) fun c' => TE c c' a' r'.2)
      (pruneCompat_update K (fun tbl => Function.update tbl sn.input (some a'))
        (fun y => mean (runW sch adversary sn.remaining sn.publicKey sn.secretKey (sn.next a') y tr)
          fun r' => mean (finalize r'.1) fun c' => rightEval sn E a c c' a' r'.2)
        (fun y => mean (runW sch adversary sn.remaining sn.publicKey sn.secretKey (sn.next a') y tr)
          fun r' => mean (finalize r'.1) fun c' => TE c c' a' r'.2)
        (hG c a'))
  -- the second branch with its uniform answer
  have hΨ₁ : ∀ c, PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
      (fun r => leftEval sch adversary sn E a c r.2) (fun r => leftTouch sch adversary sn TE c r.2) := fun c => by
    refine pruneCompat_congr K _ _ _ _ ?_ ?_ (pruneCompat_sample K (PMF.uniformOfFintype Digest) _ _ (hR c))
    · intro r
      simp only [leftEval, freshBranchW, mean_bind, mean_map, rightEval, htr]
    · intro r
      simp only [leftTouch, freshBranchW, mean_bind, mean_map, htr]
  -- the first branch's finalization
  have hΦ₁ : PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
      (fun r => mean (finalize r.1) fun c => leftEval sch adversary sn E a c r.2)
      (fun r => mean (finalize r.1) fun c => leftTouch sch adversary sn TE c r.2) :=
    pruneCompat_finalize K (leftEval sch adversary sn E a) (leftTouch sch adversary sn TE)
      (fun t w₀ f H b₁ b₂ w' => by simp only [leftEval, hEleftW])
      (fun t w₀ f H b₁ b₂ w' => by simp only [leftTouch, hTEleft]) hΨ₁
  exact pruneCompat_resample K _ _ hΦ₁

end
end SDitH.Proofs.ForkPruneCompat
