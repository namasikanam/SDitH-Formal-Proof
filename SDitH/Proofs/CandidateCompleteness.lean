import SDitH.Proofs.CandidateSchemeChain
import SDitH.Proofs.CandidateVerifier
import SDitH.Proofs.HonestCandidate

/-! Executed completeness of the candidate target. An honest commitment
run leaves every chain query stored and every leaf commitment recorded;
the candidate opening of the committed key reveals every other leaf seed,
so the candidate reconstruction evaluates to the committed root and the
revealed seeds, the candidate middle folds the committed seeds to the
honest shares, its base is the honest base check, and the lines query is
the signer's when the signer uses the verifier's Hashlines tail. Hence
the candidate verification of an honest signature evaluates on the
signer's own world to the committed lines digest. The constructive
evaluation lemmas for the collector, the fold loop and the share
collection are proved here. -/

namespace SDitH.Proofs.CandidateCompleteness

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.HashCipherEvaluation Spec.SeedPrimitives
open Spec.SharedSigner Spec.CandidateBAVC Spec.CandidateScheme Spec.SharedScheme Spec.CandidateVerifier Spec.BLCRecompute
open Spec.SlopeConsistencyGame (Out)
open SharedSigner (digestAt expandEntries)
open CandidateBAVC (leafValue induced)
open scoped Classical
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}
variable (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
  (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))

section Constructive

theorem expandCall_evaluates_of (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (address : Nat) (seed : Bits lambda)
    (h : expandEntries family ciphers layout variant salt address seed) :
    Evaluates family table ciphers (expandCall (s := s) (wit := wit) (rnd := rnd) layout variant salt address seed)
      (expandSeed variant (Spec.BAVCCipherProgram.encStar layout family) salt address seed) :=
  .cipher _ _ _ (h false) (.cipher _ _ _ (h true) (.done _))

theorem commitCall_evaluates_of (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (leafCount : Nat) (variant : Grinding) (salt seed : Bits lambda) (index : Nat)
    (h : expandEntries family ciphers layout variant salt (leafCount + index) seed) :
    Evaluates family table ciphers (commitCall (s := s) (wit := wit) (rnd := rnd) layout leafCount variant salt seed index)
      (commitSeed leafCount variant (Spec.BAVCCipherProgram.encStar layout family) salt seed index) :=
  (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mpr
    ⟨_, expandCall_evaluates_of family table ciphers layout variant salt _ seed h, .done _⟩

theorem hashCall_evaluates_of (input : List Bool) (pair : Out lambda s wit rnd) (h : table input = some pair) :
    Evaluates family table ciphers (hashCall (s := s) (wit := wit) (rnd := rnd) input) pair.1 :=
  .hash _ _ pair _ h (.done _)

theorem collect_evaluates_of {ι B : Type*} [DecidableEq ι] (call : ι → SignerProgram lambda s wit rnd B) (f : ι → B)
    (hcall : ∀ k, Evaluates family table ciphers (call k) (f k)) :
    ∀ (l : List ι) (acc : ι → B),
      Evaluates family table ciphers (collect call l acc) (fun k => if k ∈ l then f k else acc k) := by
  intro l
  induction l with
  | nil =>
    intro acc
    have : (fun k => if k ∈ ([] : List ι) then f k else acc k) = acc := by
      funext k
      simp
    rw [this]
    exact .done acc
  | cons k rest ih =>
    intro acc
    refine (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mpr ⟨f k, hcall k, ?_⟩
    have := ih (Function.update acc k (f k))
    have heq : (fun k' => if k' ∈ rest then f k' else Function.update acc k (f k) k') =
        fun k' => if k' ∈ k :: rest then f k' else acc k' := by
      funext k'
      by_cases h1 : k' ∈ rest
      · simp [h1]
      · by_cases h2 : k' = k
        · subst h2
          simp
        · simp [h1, h2]
    rw [heq] at this
    exact this

theorem foldExecutionsThrough_ok (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (bindings : Bindings lambda tau kappa (s + (wit + rnd))) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (hidden : Fin tau → Fin (2 ^ kappa)) (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (f : Fin tau → FoldedExecution (s + (wit + rnd)) kappa)
    (hf : ∀ e, foldExecution p salt bindings aux hidden randomCount enough e = .ok (f e)) :
    ∀ (count : Nat) (hc : count ≤ tau), ∃ rows : Vector (FoldedExecution (s + (wit + rnd)) kappa) count,
      foldExecutionsThrough p salt bindings aux hidden randomCount enough count hc = .ok rows ∧
      ∀ (i : Nat) (hi : i < count), rows[i] = f ⟨i, by omega⟩ := by
  intro count
  induction count with
  | zero =>
    intro hc
    exact ⟨#v[], rfl, fun i hi => absurd hi (by omega)⟩
  | succ count ih =>
    intro hc
    obtain ⟨rows, hrows, hcoord⟩ := ih (by omega)
    refine ⟨rows.push (f ⟨count, by omega⟩), ?_, ?_⟩
    · simp only [foldExecutionsThrough, hrows, hf, Bind.bind, Except.bind]
    · intro i hi
      by_cases hlt : i < count
      · rw [Vector.getElem_push_lt hlt]
        exact hcoord i hlt
      · have heq : i = count := by omega
        subst heq
        rw [Vector.getElem_push_eq]

theorem collectShares_ok {ell kappa : Nat} :
    ∀ {count : Nat} (rows : Vector (FoldedExecution ell kappa) count) (g : Fin count → Share ell kappa),
      (∀ (i : Nat) (hi : i < count), (rows[i]).share = some (g ⟨i, hi⟩)) →
      ∃ shares : Vector (Share ell kappa) count, collectShares rows = .ok shares := by
  intro count
  induction count with
  | zero =>
    intro rows g _
    exact ⟨#v[], rfl⟩
  | succ count ih =>
    intro rows g hg
    obtain ⟨previous, hprev⟩ := ih rows.pop (fun i => g (Fin.castSucc i)) (by
      intro i hi
      rw [Vector.getElem_pop' (by omega)]
      exact hg i (by omega))
    refine ⟨previous.push (g ⟨count, by omega⟩), ?_⟩
    simp only [collectShares, hprev, hg count (by omega), Bind.bind, Except.bind]

end Constructive

/-- The candidate middle evaluates on the stored mask with any complete
seed vector agreeing with the reconstruction off the hidden indices. -/
theorem candidateMiddle_evaluates_of {F : Type*} [Field F] [Algebra (ZMod 2) F] (xi : F)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (nodes : NodesBinding lambda tau (2 ^ kappa))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (salt : Bits lambda) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa))
    (recon : Reconstructed lambda tau (2 ^ kappa)) (auxiliary : Digest lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda)
    (hagree : ∀ e i, i ≠ hidden e → recon.seeds e i = some (full e i))
    (pm : Out lambda s wit rnd) (hpm : table (Spec.BAVCChainInputs.maskInput auxiliary) = some pm) :
    ∃ value, Evaluates family table ciphers
      (candidateMiddle xi p nodes encode randomCount enough salt aux hidden recon auxiliary) (Except.ok value) := by
  obtain ⟨rows, hfold, hcoord⟩ := foldExecutionsThrough_ok p salt (reconstructionBindings nodes recon) aux hidden
    randomCount enough
    (fun e => ⟨0, some fun c j => Spec.BLCSeedFold.affine p salt full randomCount enough aux e (hidden e) c j⟩)
    (fun e => CandidateVerifier.foldExecution_reconstruction p salt nodes recon full aux hidden randomCount enough e
      (hagree e)) tau le_rfl
  obtain ⟨shares, hshares⟩ := collectShares_ok rows
    (fun e => fun c j => Spec.BLCSeedFold.affine p salt full randomCount enough aux e (hidden e) c j) (by
      intro i hi
      rw [hcoord i hi])
  refine ⟨((encode hidden)⁻¹,
    fun j => algebraMap (ZMod 2) F (aux.witnessCorrection j) +
      (encode hidden)⁻¹ * Spec.BLC.psi xi (concatenate shares (Spec.BLC.witnessIndex j)),
    fun j => (encode hidden)⁻¹ * Spec.BLC.psi xi (concatenate shares (Spec.BLC.randomnessIndex j)),
    candidateBase pm.2 aux.plain hidden (concatenate shares)), .hash _ _ pm _ hpm ?_⟩
  simp only [hfold, hshares]
  exact .done _

/-- One leaf's commitment program evaluates to its value when the revealed
seeds' calls are recorded. -/
theorem leafCommit_evaluates_of (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Opening lambda tau (2 ^ kappa))
    (pair : Fin tau × Fin (2 ^ kappa))
    (hrev : ∀ seed, pair.2 ≠ hidden pair.1 → opening.revealed pair.1 pair.2 = some seed →
      expandEntries family ciphers layout variant salt (tau * 2 ^ kappa + Spec.SeedTree.leafOffset pair.1 pair.2) seed) :
    Evaluates family table ciphers (leafCommit (s := s) (wit := wit) (rnd := rnd) layout variant salt hidden opening pair)
      (leafValue family layout variant salt hidden opening pair) := by
  unfold leafCommit leafValue
  split
  · exact .done _
  · rename_i hne
    cases hrev' : opening.revealed pair.1 pair.2 with
    | none => exact .done _
    | some seed =>
      simp only [Option.map_some]
      exact (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mpr
        ⟨_, commitCall_evaluates_of family table ciphers layout _ variant salt seed _ (hrev seed hne hrev'), .done _⟩

/-- The candidate reconstruction evaluates when every revealed seed's calls
are recorded, every off-hidden seed is revealed, and the row and outer
queries of the recomputed commitments are stored. -/
theorem reconstruct_evaluates_of (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Opening lambda tau (2 ^ kappa))
    (hrev : ∀ e i, i ≠ hidden e → ∃ seed, opening.revealed e i = some seed ∧
      expandEntries family ciphers layout variant salt (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) seed)
    (hrows : ∀ e, ∃ pair, table (Spec.BAVCBinding.rowQuery (commitsOf (leafValue family layout variant salt hidden opening)) e) =
      some pair)
    (pairO : Out lambda s wit rnd)
    (hO : table (Spec.BAVCBinding.outerQuery (induced (tau := tau) (kappa := kappa) family table layout variant) salt
      (commitsOf (leafValue family layout variant salt hidden opening))) = some pairO) :
    Evaluates family table ciphers (Spec.CandidateBAVC.reconstruct (s := s) (wit := wit) (rnd := rnd) layout variant salt hidden opening)
      (Except.ok ⟨pairO.1, opening.revealed⟩) := by
  set C := commitsOf (leafValue family layout variant salt hidden opening) with hC
  unfold Spec.CandidateBAVC.reconstruct
  refine (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mpr
    ⟨_, collect_evaluates_of family table ciphers _ (leafValue family layout variant salt hidden opening)
      (fun pair => leafCommit_evaluates_of family table ciphers layout variant salt hidden opening pair (by
        intro seed hne hseed
        obtain ⟨seed', hseed', hent⟩ := hrev pair.1 pair.2 hne
        rw [hseed] at hseed'
        rw [Option.some.inj hseed']
        exact hent)) _ _, ?_⟩
  have hmem : ∀ pair : Fin tau × Fin (2 ^ kappa), pair ∈ Spec.SharedSlopeExec.allPairs tau kappa :=
    fun pair => SharedSlopeExec.mem_allPairs pair.1 pair.2
  simp only [hmem, ↓reduceIte]
  have hall : ∀ pair, (leafValue family layout variant salt hidden opening pair).isSome := by
    intro pair
    unfold leafValue
    split
    · rfl
    · rename_i hne
      obtain ⟨seed, hseed, _⟩ := hrev pair.1 pair.2 hne
      rw [hseed]
      rfl
  rw [if_pos hall]
  refine (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mpr
    ⟨_, collect_evaluates_of family table ciphers _ (fun e => digestAt table (Spec.BAVCBinding.rowQuery C e))
      (fun e => by
        obtain ⟨pair, hpair⟩ := hrows e
        have := hashCall_evaluates_of family table ciphers _ pair hpair
        show Evaluates family table ciphers (hashCall (Spec.BAVCBinding.rowQuery C e)) (digestAt table (Spec.BAVCBinding.rowQuery C e))
        rw [SharedSigner.digestAt_of_stored table _ pair hpair]
        exact this) _ _, ?_⟩
  simp only [List.mem_finRange, ↓reduceIte]
  exact .hash _ _ pairO _ hO (.done _)

section Honest

open Spec.SharedSigner (SignerSetting Committed commitProgram verifierLinesTail)

/-- An honest candidate signature verifies on the signer's world: the
candidate verification evaluates to the committed lines digest. -/
theorem honest_verifies {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (V : VerifierSetting F lambda tau kappa s wit rnd)
    (xi : F) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hlayout : V.layout = S.layout) (hvariant : V.variant = S.variant) (hencoding : V.encoding = S.encoding)
    (hmid : V.middle = candidateMiddle xi S.p V.nodes encode S.randomCount S.enough)
    (htail : S.linesTail = verifierLinesTail S.encoding)
    (salt root : Bits lambda) (witness : Fin wit → ZMod 2) (committed : Committed F lambda tau kappa s wit rnd)
    (h : Evaluates family table ciphers (commitProgram S salt root witness) committed)
    (piop : Digest lambda) (ctr : Spec.BLCRetry.Counter) :
    ∃ (delta : F) (witnessVals : Fin wit → F) (randomnessVals : Fin rnd → F),
      Evaluates family table ciphers
        (Spec.CandidateScheme.verifyProgram V salt committed.result.auxiliary piop
          (ctr, openKey committed.result.key (V.expand piop ctr)))
        (Except.ok ⟨delta, witnessVals, randomnessVals, committed.result.lines⟩) := by
  obtain ⟨hseeds, hkey, hhcom, hrows, houter, haux, hmask, hlines, _, _, hauxf, hentries⟩ :=
    SharedSigner.commit_evaluates family table ciphers S salt root witness committed h
  set bavc := Spec.BAVC.commit (SharedSigner.inducedPrimitives (tau := tau) (kappa := kappa) family table S.layout S.variant)
    salt root with hbavc
  set hidden := V.expand piop ctr with hhidden
  -- The candidate opening of the committed key reveals the committed seeds off the hidden indices.
  have hrev : ∀ e i, i ≠ hidden e → ∃ seed, (openKey committed.result.key hidden).revealed e i = some seed ∧
      expandEntries family ciphers S.layout S.variant salt (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) seed := by
    intro e i hi
    refine ⟨bavc.seeds e i, ?_, hentries e i⟩
    simp only [openKey, hi, ↓reduceIte, hkey]
    rfl
  -- The recomputed commitments are the key's.
  have hC : commitsOf (leafValue family S.layout S.variant salt hidden (openKey committed.result.key hidden)) =
      bavc.key.commitments := by
    rw [hkey]
    exact CandidateBAVC.commits_openKey family S.layout S.variant (digestAt table) salt root hidden
  have hP : induced (tau := tau) (kappa := kappa) family table S.layout S.variant =
      SharedSigner.inducedPrimitives (tau := tau) (kappa := kappa) family table S.layout S.variant := rfl
  obtain ⟨pairO, hO, hO1⟩ := houter
  -- The reconstruction.
  have hrecon : Evaluates family table ciphers
      (Spec.CandidateBAVC.reconstruct S.layout S.variant salt hidden (openKey committed.result.key hidden))
      (Except.ok ⟨pairO.1, (openKey committed.result.key hidden).revealed⟩) := by
    refine reconstruct_evaluates_of family table ciphers S.layout S.variant salt hidden _ hrev ?_ pairO ?_
    · intro e
      rw [hC]
      obtain ⟨pair, hpair, _⟩ := hrows e
      exact ⟨pair, hpair⟩
    · rw [hC, hP]
      have hrowfun : committed.rowHashes = fun e =>
          (SharedSigner.inducedPrimitives (tau := tau) (kappa := kappa) family table S.layout S.variant).hash
            (Spec.BAVCBinding.rowQuery bavc.key.commitments e) := by
        funext e
        obtain ⟨pair, hpair, hpair1⟩ := hrows e
        rw [← hpair1]
        exact (SharedSigner.digestAt_of_stored table _ pair hpair).symm
      rw [hrowfun] at hO
      exact hO
  -- The middle on the committed seeds.
  obtain ⟨pa, hpa, hpa1⟩ := haux
  obtain ⟨pm, hpm, hpm2⟩ := hmask
  have hagree : ∀ e i, i ≠ hidden e →
      (⟨pairO.1, (openKey committed.result.key hidden).revealed⟩ : Reconstructed lambda tau (2 ^ kappa)).seeds e i =
        some (bavc.seeds e i) := by
    intro e i hi
    simp only [openKey, hi, ↓reduceIte, hkey]
    rfl
  obtain ⟨value, hvalue⟩ := candidateMiddle_evaluates_of family table ciphers xi S.p V.nodes encode S.randomCount S.enough
    salt committed.result.auxiliary hidden _ pa.1 bavc.seeds hagree pm (by rw [hpa1]; exact hpm)
  obtain ⟨pm', hpm', hv1, hv2, hv3, hbase⟩ := CandidateVerifier.candidateMiddle_evaluates xi S.p V.nodes encode S.randomCount
    S.enough salt committed.result.auxiliary hidden _ pa.1 bavc.seeds hagree family table ciphers value hvalue
  have hpmeq : pm' = pm := by
    rw [hpa1] at hpm'
    exact Option.some.inj (hpm'.symm.trans hpm)
  -- The base is the honest base check, so the lines query is the signer's.
  have hbase' : value.2.2.2 = (Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow
      (Spec.BLCCommit.randomTable S.p salt bavc.seeds S.randomCount S.enough) pm.2 witness).baseCheck := by
    rw [hbase, hpmeq, hauxf]
    show candidateBase pm.2 _ hidden (Spec.BLCSeedLines.shareMatrix S.p salt bavc.seeds S.randomCount S.enough
      (HonestCandidate.honestAux S.p salt bavc.seeds S.randomCount S.enough _ _) hidden) = _
    rw [hpm2]
    exact HonestCandidate.candidateBase_honest S.xi S.p salt bavc.seeds S.randomCount S.enough committed.mask witness hidden
  obtain ⟨pl, hpl, hpl1⟩ := hlines
  refine ⟨value.1, value.2.1, value.2.2.1, ?_⟩
  unfold Spec.CandidateScheme.verifyProgram
  rw [hlayout, hvariant, hencoding]
  refine (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mpr ⟨_, hrecon, ?_⟩
  show Evaluates family table ciphers (Program.hash (Spec.BLCHashChain.auxQuery pairO.1 _) _) _
  have hroot : pairO.1 = committed.hcom := hO1
  rw [hroot]
  have hpa' : table (Spec.BLCHashChain.auxQuery committed.hcom
      (Spec.BLCHashChain.sourceTail S.encoding committed.result.auxiliary.corrections)) = some pa := by
    rw [hauxf]
    exact hpa
  refine .hash _ _ pa _ hpa' ?_
  rw [hmid]
  refine (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mpr ⟨_, hvalue, ?_⟩
  show Evaluates family table ciphers (Program.hash _ _) _
  have hinput : Spec.BLCHashChain.linesQuery pa.1 (S.encoding.vector committed.result.auxiliary.plain ++
      S.encoding.base value.2.2.2) =
      Spec.BLCHashChain.linesQuery committed.auxiliary (S.linesTail
        (Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow
          (Spec.BLCCommit.randomTable S.p salt bavc.seeds S.randomCount S.enough) committed.mask witness).plainCheck
        (Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow
          (Spec.BLCCommit.randomTable S.p salt bavc.seeds S.randomCount S.enough) committed.mask witness).baseCheck
        (Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow
          (Spec.BLCCommit.randomTable S.p salt bavc.seeds S.randomCount S.enough) committed.mask witness).witnessCorrection) := by
    rw [hpa1, htail, hbase', hpm2, hauxf]
    rfl
  rw [hinput]
  refine .hash _ _ pl _ hpl ?_
  rw [hpl1]
  exact .done _

end Honest

end
end SDitH.Proofs.CandidateCompleteness
