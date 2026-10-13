import SDitH.Spec.BAVCBinding
import SDitH.Proofs.BAVCReconstruction
import SDitH.Proofs.BAVC

namespace SDitH.Proofs.BAVCBinding

open Spec.BAVC Spec.BAVCBinding

/-- Fixed-width array concatenation is injective, including zero-width arrays. -/
theorem serializeArray_injective {n bits : Nat} :
    Function.Injective (serializeArray : (Fin n → Spec.DomainSeparation.Bits bits) → List Bool) := by
  induction n with
  | zero =>
    intro left right _
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro left right h
    have hs (v : Fin (n + 1) → Spec.DomainSeparation.Bits bits) :
        serializeArray v = List.ofFn (v 0) ++ serializeArray (fun i => v i.succ) := by
      simp only [serializeArray, List.ofFn_succ, List.flatMap_cons]
    rw [hs, hs] at h
    obtain ⟨hhead, htail⟩ := List.append_inj h (by simp)
    have hzero := List.ofFn_injective hhead
    have hsucc := ih htail
    funext i
    exact Fin.cases hzero (fun j => congrFun hsucc j) i

theorem rowQuery_injective {lambda tau N : Nat} (left right : Commitments lambda tau N)
    (e : Fin tau) (h : rowQuery left e = rowQuery right e) : left e = right e := by
  exact serializeArray_injective (List.append_cancel_left h)

theorem outerQuery_eq {lambda tau N : Nat} (p : Primitives lambda)
    (leftSalt rightSalt : Seed lambda) (left right : Commitments lambda tau N)
    (h : outerQuery p leftSalt left = outerQuery p rightSalt right) :
    leftSalt = rightSalt ∧ (fun e => p.hash (rowQuery left e)) = (fun e => p.hash (rowQuery right e)) := by
  have he := List.append_cancel_left h
  obtain ⟨hsalt, hrows⟩ := List.append_inj he (by simp)
  exact ⟨List.ofFn_injective hsalt, serializeArray_injective hrows⟩

theorem rootHash_commit {lambda tau N : Nat} (p : Primitives lambda)
    (salt : Seed lambda) (tree : Tree lambda tau N) :
    rootHash p salt (commitFromTree p salt tree).key.commitments = (commitFromTree p salt tree).hcom := rfl

theorem rootHash_reconstruction {lambda tau N : Nat} (p : Primitives lambda)
    (salt : Seed lambda) (rows : Vector (Vector (ReconstructedLeaf lambda) N) tau) :
    rootHash p salt (rowCommitments rows) = (reconstructionHashes p salt rows).hcom := rfl

theorem hashQueries_length {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (commits : Commitments lambda tau N) : (hashQueries p salt commits).length = tau + 1 := by
  simp [hashQueries]

theorem rowQuery_mem {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (commits : Commitments lambda tau N) (e : Fin tau) : rowQuery commits e ∈ hashQueries p salt commits := by
  apply List.mem_append_left
  exact List.mem_ofFn.mpr ⟨e, rfl⟩

theorem outerQuery_mem {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (commits : Commitments lambda tau N) : outerQuery p salt commits ∈ hashQueries p salt commits := by
  simp [hashQueries]

theorem find_none_implies_equal {lambda tau N : Nat} (p : Primitives lambda)
    (leftSalt rightSalt : Seed lambda) (left right : Commitments lambda tau N)
    (h : findHashCollision p leftSalt rightSalt left right = none) :
    leftSalt = rightSalt ∧ left = right := by
  unfold findHashCollision at h
  split at h
  · rename_i houter
    have hfind := Option.map_eq_none_iff.mp h
    refine ⟨(outerQuery_eq p leftSalt rightSalt left right houter).1, ?_⟩
    funext e
    apply rowQuery_injective
    have he := List.find?_eq_none.mp hfind e (List.mem_finRange e)
    simpa using he
  · contradiction

/-- A returned pair is made of actual queries, one from each commitment.
If their final roots agree, it is a genuine collision of the supplied hash. -/
theorem find_some_collision {lambda tau N : Nat} (p : Primitives lambda)
    (leftSalt rightSalt : Seed lambda) (left right : Commitments lambda tau N)
    (hroot : rootHash p leftSalt left = rootHash p rightSalt right)
    (pair : QueryPair) (h : findHashCollision p leftSalt rightSalt left right = some pair) :
    IsHashCollision p pair ∧ pair.1 ∈ hashQueries p leftSalt left ∧ pair.2 ∈ hashQueries p rightSalt right := by
  unfold findHashCollision at h
  split at h
  · rename_i houter
    obtain ⟨e, he, hpair⟩ := Option.map_eq_some_iff.mp h
    subst pair
    have hne : rowQuery left e ≠ rowQuery right e := by
      simpa using List.find?_some he
    have heq := congrFun (outerQuery_eq p leftSalt rightSalt left right houter).2 e
    exact ⟨⟨hne, heq⟩, rowQuery_mem p leftSalt left e, rowQuery_mem p rightSalt right e⟩
  · rename_i houter
    have he := Option.some.inj h
    subst pair
    exact ⟨⟨houter, hroot⟩, outerQuery_mem p leftSalt left, outerQuery_mem p rightSalt right⟩

end SDitH.Proofs.BAVCBinding
