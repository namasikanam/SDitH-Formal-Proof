import SDitH.Spec.SharedSlopeGame
import SDitH.Proofs.SlopeConsistencyGame
import SDitH.Proofs.HashCipherTrace
import SDitH.Proofs.HashCipherHash
import SDitH.Proofs.SeedPairing
import SDitH.Proofs.BAVCBindingReconstruction

/-! Coverage for the shared-model slope game: a winning run raised a mask
trap, the mention event, the digest-collision event, a witnessed pair
collision among queried seeds, or an unqueried seed matching a named
seed's commitment. The uniqueness step now needs only that no other seed
shares a named seed's commitment, which the last two events negate. -/

namespace SDitH.Proofs.SharedSlopeGame

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.SlopeConsistency
open Spec.SlopeConsistencyGame (Out)
open Spec.SharedSlopeGame Spec.SeedPrimitives Spec.SeedPairing Spec.IdealCipher Spec.IdealCipherPairCollision
open Spec.RandomOracleMention Spec.ProductOracle Spec.ConsistencyMatrix Spec.OracleChain
open Spec.RandomOracleTrace (Traced Extends traceBad)
open scoped Classical ENNReal
noncomputable section

variable {lambda tau kappa s wit rnd : Nat} {State : Type*}

/-- Uniqueness with injectivity only at the named claim's own seeds. -/
theorem chain_unique_local (S : Setting lambda tau kappa s wit rnd) (family : CipherFamily lambda)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail S.encoding corrections))
    (table : List Bool → Option (Out lambda s wit rnd)) (hfree : DigestCollisionFree table)
    (c c' : Claim lambda tau kappa s wit rnd) (hlocal : NoCollisionAt S family c)
    (hc : ChainIn' S family table c) (hc' : ChainIn' S family table c') (haux : c.auxiliary = c'.auxiliary) :
    c.salt = c'.salt ∧ c.full = c'.full ∧ c.rowHashes = c'.rowHashes ∧ c.root = c'.root ∧
      c.aux.corrections = c'.aux.corrections := by
  obtain ⟨hrows, ⟨po, hpo, hpo1⟩, ⟨pa, hpa, hpa1⟩⟩ := hc
  obtain ⟨hrows', ⟨po', hpo', hpo1'⟩, ⟨pa', hpa', hpa1'⟩⟩ := hc'
  have hauxEq : auxString c.root (tail S.encoding c) = auxString c'.root (tail S.encoding c') :=
    hfree _ _ pa pa' hpa hpa' (by rw [hpa1, hpa1', haux])
  obtain ⟨hroot, htail⟩ := SlopeConsistency.auxString_inj _ _ _ _ hauxEq
  have hcorr : c.aux.corrections = c'.aux.corrections := hencoding htail
  have houterEq : outerString c.salt c.rowHashes = outerString c'.salt c'.rowHashes :=
    hfree _ _ po po' hpo hpo' (by rw [hpo1, hpo1', hroot])
  obtain ⟨hsalt, hrowHashes⟩ := SlopeConsistency.outerString_inj _ _ _ _ houterEq
  have hfull : c.full = c'.full := by
    funext e i
    obtain ⟨pr, hpr, hpr1⟩ := hrows e
    obtain ⟨pr', hpr', hpr1'⟩ := hrows' e
    have hrowEq : rowString (rows (commitOf S.variant family c.salt) c e) =
        rowString (rows (commitOf S.variant family c'.salt) c' e) :=
      hfree _ _ pr pr' hpr hpr' (by rw [hpr1, hpr1', hrowHashes])
    have hrow := SlopeConsistency.rowString_inj _ _ hrowEq
    have hi := congrFun hrow i
    simp only [rows] at hi
    rw [← hsalt] at hi
    exact (hlocal e i (c'.full e i) hi.symm).symm
  exact ⟨hsalt, hfull, hrowHashes, hroot, hcorr⟩

theorem vectorOf_eq (S : Setting lambda tau kappa s wit rnd) (family : CipherFamily lambda)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail S.encoding corrections))
    (table : List Bool → Option (Out lambda s wit rnd)) (hfree : DigestCollisionFree table)
    (c : Claim lambda tau kappa s wit rnd) (hlocal : NoCollisionAt S family c)
    (hc : ChainIn' S family table c) (e e' : Fin tau) :
    vectorOf S family e e' table (maskInput c.auxiliary) = slopeOf S c e - slopeOf S c e' := by
  have h : ∃ c' : Claim lambda tau kappa s wit rnd, ChainIn' S family table c' ∧ maskInput c'.auxiliary = maskInput c.auxiliary :=
    ⟨c, hc, rfl⟩
  rw [vectorOf, dif_pos h]
  obtain ⟨hc', hmask⟩ := Classical.choose_spec h
  have haux : c.auxiliary = (Classical.choose h).auxiliary :=
    (SlopeConsistencyGame.maskInput_injective _ _ hmask).symm
  obtain ⟨hsalt, hfull, _, _, hcorr⟩ := chain_unique_local S family hencoding table hfree c (Classical.choose h) hlocal hc hc' haux
  funext col
  simp only [Pi.sub_apply, slopeOf]
  rw [SlopeConsistency.slope_congr S.p _ _ S.randomCount S.enough _ c.aux hcorr.symm e col,
    SlopeConsistency.slope_congr S.p _ _ S.randomCount S.enough _ c.aux hcorr.symm e' col, ← hsalt, ← hfull]

theorem chainIn_before (S : Setting lambda tau kappa s wit rnd) (family : CipherFamily lambda)
    (before table : List Bool → Option (Out lambda s wit rnd)) (hext : Extends before table)
    (c : Claim lambda tau kappa s wit rnd) (hc : ChainIn' S family table c)
    (hpresent : (∀ e, (before (rowString (rows (commitOf S.variant family c.salt) c e))).isSome) ∧
      (before (outerString c.salt c.rowHashes)).isSome ∧ (before (auxString c.root (tail S.encoding c))).isSome) :
    ChainIn' S family before c :=
  SlopeConsistencyGame.chainIn_before ⟨S.p, S.randomCount, S.enough, commitOf S.variant family c.salt, S.encoding⟩
    before table hext c hc hpresent

/-- Chain presence from the log invariants alone, without the single-oracle experiment. -/
theorem chain_present_or_mention_of_invariants {M : Type*} (hlambda : 0 < lambda) (htau : 0 < tau)
    (hN : 0 < 2 ^ kappa) (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Digest lambda × M)))
    (table : List Bool → Option (Digest lambda × M)) (hord : Ordered log) (hfresh : Fresh log)
    (htraced : Traced table log)
    (salt : Seed lambda) (rows : Fin tau → Fin (2 ^ kappa) → Digest lambda) (rowHashes : Fin tau → Digest lambda)
    (root : Digest lambda) (tail : List Bool) (auxiliary : Digest lambda)
    (hrows : ∀ e, ∃ pair, table (rowString (rows e)) = some pair ∧ pair.1 = rowHashes e)
    (houter : ∃ pair, table (outerString salt rowHashes) = some pair ∧ pair.1 = root)
    (haux : ∃ pair, table (auxString root tail) = some pair ∧ pair.1 = auxiliary)
    (em : Spec.RandomOracleTrace.Entry (List Bool) (Digest lambda × M)) (hem : em ∈ log) (hemi : em.input = maskInput auxiliary) :
    ((∀ e, (em.before (rowString (rows e))).isSome) ∧ (em.before (outerString salt rowHashes)).isSome ∧
        (em.before (auxString root tail)).isSome) ∨
      prefixBad (digestMention (mentions lambda tau)) log = true := by
  by_cases hbad : prefixBad (digestMention (mentions lambda tau)) log = true
  · exact Or.inr hbad
  left
  have hall : ∀ e : Fin tau, Present em.before (chain salt rows rowHashes root tail auxiliary e) := by
    intro e
    obtain ⟨hto, hlinked⟩ := BAVCChainInputs.chain_linked salt rows rowHashes root tail auxiliary e
    obtain ⟨hne, hpair⟩ := BAVCChainInputs.chain_distinct hlambda htau hN salt rows rowHashes root tail auxiliary e
    have hstored : Stored table (chain salt rows rowHashes root tail auxiliary e) := by
      intro p hp
      simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact haux
      · exact houter
      · exact hrows e
    rcases OracleChain.chain_present_or_mention (mentions lambda tau) log table hord hfresh htraced
      (chain salt rows rowHashes root tail auxiliary e) (maskInput auxiliary) hto hlinked hne hpair hstored
      em hem hemi with hpresent | hbad'
    · exact hpresent
    · exact absurd hbad' hbad
  obtain ⟨e0, _⟩ : ∃ e : Fin tau, True := ⟨⟨0, htau⟩, trivial⟩
  refine ⟨fun e => hall e (rowString (rows e), rowHashes e) (by simp [chain]),
    hall e0 (outerString salt rowHashes, root) (by simp [chain]),
    hall e0 (auxString root tail, auxiliary) (by simp [chain])⟩

theorem leafOffset_bound (e : Fin tau) (i : Fin (2 ^ kappa)) :
    leafCount tau kappa + Spec.SeedTree.leafOffset e i < 2 * leafCount tau kappa := by
  have := SeedTree.leafOffset_lt e i
  simp only [leafCount]
  omega

/-- A colliding seed is queried, giving a witnessed pair, or unqueried at
both inputs, giving the unseen double match. -/
theorem collision_split (S : Setting lambda tau kappa s wit rnd) (hlambda : 26 ≤ lambda)
    (hcount : 4 * leafCount tau kappa ≤ 2 ^ 24) (family : CipherFamily lambda) (history : History lambda)
    (hmatches : Matches family history) (c : Claim lambda tau kappa s wit rnd)
    (hqueried : Queried S family history c) (hcoll : ¬ NoCollisionAt S family c) :
    Witnessed id companion family history ∨
      ∃ (e : Fin tau) (i : Fin (2 ^ kappa)) (seed : Bits lambda), seed ≠ c.full e i ∧
        Unseen history seed (input0 S.variant c.salt e i) ∧
        Unseen history seed (companion (input0 S.variant c.salt e i)) ∧
        family seed (input0 S.variant c.salt e i) = family (c.full e i) (input0 S.variant c.salt e i) ∧
        family seed (companion (input0 S.variant c.salt e i)) = family (c.full e i) (companion (input0 S.variant c.salt e i)) := by
  simp only [NoCollisionAt, not_forall] at hcoll
  obtain ⟨e, i, seed, hcommit, hne⟩ := hcoll
  have he := (BAVCBindingReconstruction.commitSeed_eq_iff (leafCount tau kappa) S.variant
    (fun key input => family key input) c.salt seed (c.full e i) (Spec.SeedTree.leafOffset e i)).mp hcommit
  have hcomp : cipherInput S.variant c.salt (leafCount tau kappa + Spec.SeedTree.leafOffset e i) true =
      companion (input0 S.variant c.salt e i) :=
    SeedPairing.cipherInput_companion hlambda hcount (leafOffset_bound e i) S.variant c.salt
  have h0 : family seed (input0 S.variant c.salt e i) = family (c.full e i) (input0 S.variant c.salt e i) := he false
  have h1 : family seed (companion (input0 S.variant c.salt e i)) =
      family (c.full e i) (companion (input0 S.variant c.salt e i)) := by
    have := he true
    rwa [hcomp] at this
  obtain ⟨hq0, hq1⟩ := hqueried e i
  by_cases hu0 : Unseen history seed (input0 S.variant c.salt e i)
  · by_cases hu1 : Unseen history seed (companion (input0 S.variant c.salt e i))
    · exact Or.inr ⟨e, i, seed, hne, hu0, hu1, h0, h1⟩
    · left
      simp only [Unseen, not_forall, not_not] at hu1
      obtain ⟨entry, hmem, hkey, hinput⟩ := hu1
      have hout : entry.output = family seed (companion (input0 S.variant c.salt e i)) := by
        rw [← hmatches entry hmem, hkey, hinput]
      refine ⟨seedEntry family (c.full e i) (companion (input0 S.variant c.salt e i)), hq1, entry, hmem, ?_⟩
      refine ⟨by simp only [seedEntry]; rw [hkey]; exact Ne.symm hne, by simp only [seedEntry]; rw [hinput], ?_, ?_⟩
      · simp only [seedEntry, id, hout]
        exact h1.symm
      · simp only [seedEntry, id, hkey, SeedPairing.companion_involutive _]
        exact h0.symm
  · left
    simp only [Unseen, not_forall, not_not] at hu0
    obtain ⟨entry, hmem, hkey, hinput⟩ := hu0
    have hout : entry.output = family seed (input0 S.variant c.salt e i) := by
      rw [← hmatches entry hmem, hkey, hinput]
    refine ⟨seedEntry family (c.full e i) (input0 S.variant c.salt e i), hq0, entry, hmem, ?_⟩
    refine ⟨by simp only [seedEntry]; rw [hkey]; exact Ne.symm hne, by simp only [seedEntry]; rw [hinput], ?_, ?_⟩
    · simp only [seedEntry, id, hout]
      exact h0.symm
    · simp only [seedEntry, id, hkey]
      exact h1.symm

theorem joint_matches (procedure : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (budget : Nat) (initial : State) (joint : CipherFamily lambda × Res lambda s wit rnd State)
    (hout : joint ∈ (Spec.HashCipherTrace.jointExperiment procedure budget initial).support) :
    Matches joint.1 joint.2.cipherHistory := by
  have hmem : (joint.1, Spec.HashCipherTrace.forget joint.2) ∈ (Spec.HashCipher.jointExperiment procedure budget initial).support := by
    rw [← HashCipherTrace.joint_forget]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨joint, hout, rfl⟩
  exact (HashCipherHash.joint_invariants procedure budget initial _ hmem).2.1

/-- A winning run raised a trap, the mention event, the collision event, a
witnessed pair collision, or an unseen double match. -/
theorem wins_covered (S : Setting lambda tau kappa s wit rnd)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail S.encoding corrections))
    (hlambda : 26 ≤ lambda) (htau : 0 < tau) (hcount : 4 * leafCount tau kappa ≤ 2 ^ 24)
    (procedure : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (budget : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd)
    (joint : CipherFamily lambda × Res lambda s wit rnd State)
    (hout : joint ∈ (Spec.HashCipherTrace.jointExperiment procedure budget initial).support)
    (hwin : wins S choose joint = true) :
    trapAny S joint = true ∨ prefixBad (digestMention (mentions lambda tau)) joint.2.trace = true ∨
      prefixBad digestCollision joint.2.trace = true ∨ witnessed joint = true ∨ unseenMatch S choose joint = true := by
  by_cases hmention : prefixBad (digestMention (mentions lambda tau)) joint.2.trace = true
  · exact Or.inr (Or.inl hmention)
  by_cases hcoll : prefixBad digestCollision joint.2.trace = true
  · exact Or.inr (Or.inr (Or.inl hcoll))
  obtain ⟨hchain, hqueried, pair, hpair, e, e', hne, hmask⟩ := of_decide_eq_true hwin
  set c := choose joint.2.state with hc
  obtain ⟨htraced, hord, hfresh, hextall, _⟩ := HashCipherTrace.joint_invariants procedure budget initial joint hout
  have hmatches := joint_matches procedure budget initial joint hout
  by_cases hlocal : NoCollisionAt S joint.1 c
  · left
    obtain ⟨em, hem, hemi, hema, _, hemext⟩ := htraced.1 _ pair hpair
    have hfree : DigestCollisionFree joint.2.hashTable :=
      SlopeConsistency.collision_free_of_not_prefix joint.2.trace joint.2.hashTable htraced hcoll
    have hN : 0 < 2 ^ kappa := Nat.two_pow_pos kappa
    rcases chain_present_or_mention_of_invariants (by omega) htau hN joint.2.trace joint.2.hashTable hord hfresh htraced
      c.salt (rows (commitOf S.variant joint.1 c.salt) c) c.rowHashes c.root (tail S.encoding c) c.auxiliary
      hchain.1 hchain.2.1 hchain.2.2 em hem hemi with hpresent | hbad
    · have hcin := chainIn_before S joint.1 em.before joint.2.hashTable hemext c hchain hpresent
      have hfreeB := SlopeConsistency.collision_free_mono em.before joint.2.hashTable hemext hfree
      have hvec := vectorOf_eq S joint.1 hencoding em.before hfreeB c hlocal hcin e e'
      rw [trapAny]
      refine SlopeConsistencyGame.decide_true_of ⟨e, e', List.any_eq_true.mpr ⟨em, hem, ?_⟩⟩
      rw [hemi, hema]
      show tableMaskTrap (vectorOf S joint.1 e e') em.before (maskInput c.auxiliary) pair = true
      rw [tableMaskTrap, Spec.RandomOracleTrap.kernelTrap]
      refine SlopeConsistencyGame.decide_true_of ?_
      rw [hvec]
      refine ⟨sub_ne_zero.mpr hne, fun a => ?_⟩
      rw [ConsistencyMatrix.masked_sub, hmask a, sub_self]
    · exact absurd hbad hmention
  · rcases collision_split S hlambda hcount joint.1 joint.2.cipherHistory hmatches c hqueried hlocal with hw | hu
    · exact Or.inr (Or.inr (Or.inr (Or.inl (SlopeConsistencyGame.decide_true_of hw))))
    · obtain ⟨e, i, seed, hne', hu0, hu1, h0, h1⟩ := hu
      obtain ⟨hq0, hq1⟩ := hqueried e i
      exact Or.inr (Or.inr (Or.inr (Or.inr (SlopeConsistencyGame.decide_true_of
        ⟨e, i, seed, _, _, hne', hu0, hu1, hq0, hq1, h0, h1⟩))))

end
end SDitH.Proofs.SharedSlopeGame
