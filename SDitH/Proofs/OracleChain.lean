import SDitH.Spec.OracleChain
import SDitH.Proofs.ProductOracle

/-! The instrumented run keeps its log ordered and fresh. A dependency
chain whose links are all stored is either entirely present in the table
before its sink was queried, or some fresh digest equals a value an earlier
input mentioned. The sink is any stored query, for example the mask query. -/

namespace SDitH.Proofs.OracleChain

open Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open scoped Classical
noncomputable section

variable {Input Output State : Type*} [Fintype Output] [Nonempty Output]

omit [Fintype Output] [Nonempty Output] in
theorem ordered_cons (table : Input → Option Output) (input : Input) (answer : Output)
    (log : List (Entry Input Output)) (hord : Ordered log)
    (hext : ∀ entry ∈ log, Extends entry.before table)
    (hstored : ∀ entry ∈ log, table entry.input = some entry.answer) :
    Ordered (⟨table, input, answer⟩ :: log) := by
  intro i j hi hj hij
  cases i with
  | zero =>
    cases j with
    | zero => omega
    | succ j =>
      have hj' : j < log.length := by simpa using hj
      simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      have hmem : log[j] ∈ log := List.getElem_mem hj'
      exact ⟨hext _ hmem, hstored _ hmem⟩
  | succ i =>
    cases j with
    | zero => omega
    | succ j =>
      simp only [List.getElem_cons_succ]
      exact hord i j (by simpa using hi) (by simpa using hj) (by omega)

theorem query_ordered (table : Input → Option Output) (log : List (Entry Input Output))
    (input : Input) (result : Output × (Input → Option Output))
    (hr : result ∈ (Spec.RandomOracle.query table input).support)
    (hord : Ordered log) (hfresh : Fresh log)
    (hext : ∀ entry ∈ log, Extends entry.before table)
    (hstored : ∀ entry ∈ log, table entry.input = some entry.answer) :
    Ordered (record table input result.1 log) ∧ Fresh (record table input result.1 log) ∧
      (∀ entry ∈ record table input result.1 log, Extends entry.before result.2) ∧
      ∀ entry ∈ record table input result.1 log, result.2 entry.input = some entry.answer := by
  have hgrow := RandomOracleTrace.query_extends table input result hr
  cases he : table input with
  | some old =>
    simp only [record, he]
    exact ⟨hord, hfresh, fun entry hmem => RandomOracleTrace.extends_trans (hext entry hmem) hgrow,
      fun entry hmem => hgrow _ _ (hstored entry hmem)⟩
  | none =>
    unfold Spec.RandomOracle.query at hr
    rw [he] at hr
    obtain ⟨fresh, _, hresult⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst result
    simp only [record, he]
    refine ⟨ordered_cons table input fresh log hord hext hstored, ?_, ?_, ?_⟩
    · intro entry hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact he
      · exact hfresh entry hmem
    · intro entry hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hgrow
      · exact RandomOracleTrace.extends_trans (hext entry hmem) hgrow
    · intro entry hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp
      · exact hgrow _ _ (hstored entry hmem)

theorem run_ordered (procedure : Spec.RandomOracleCollision.Procedure Input Output State) (fuel : Nat)
    (state : State) (table : Input → Option Output) (log : List (Entry Input Output))
    (out : Result Input Output State) (hout : out ∈ (run procedure fuel state table log).support)
    (hord : Ordered log) (hfresh : Fresh log)
    (hext : ∀ entry ∈ log, Extends entry.before table)
    (hstored : ∀ entry ∈ log, table entry.input = some entry.answer) :
    Ordered out.trace ∧ Fresh out.trace ∧ (∀ entry ∈ out.trace, Extends entry.before out.table) ∧
      ∀ entry ∈ out.trace, out.table entry.input = some entry.answer := by
  induction fuel generalizing state table log out with
  | zero =>
    simp only [run, PMF.mem_support_pure_iff] at hout
    subst out
    exact ⟨hord, hfresh, hext, hstored⟩
  | succ fuel ih =>
    simp only [run] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst out
      exact ⟨hord, hfresh, hext, hstored⟩
    | query input next =>
      obtain ⟨result, hr, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨h1, h2, h3, h4⟩ := query_ordered table log input result hr hord hfresh hext hstored
      exact ih (next result.1) result.2 (record table input result.1 log) out hrun h1 h2 h3 h4

theorem experiment_ordered (procedure : Spec.RandomOracleCollision.Procedure Input Output State)
    (budget : Nat) (initial : State) (out : Result Input Output State)
    (hout : out ∈ (experiment procedure budget initial).support) :
    Ordered out.trace ∧ Fresh out.trace ∧ (∀ entry ∈ out.trace, Extends entry.before out.table) ∧
      ∀ entry ∈ out.trace, out.table entry.input = some entry.answer :=
  run_ordered procedure budget initial (fun _ => none) [] out hout (by intro i j hi; simp at hi)
    (by simp [Fresh]) (by simp) (by simp)

omit [Fintype Output] [Nonempty Output] in
theorem prefixBad_of_index (bad : List (Entry Input Output) → Input → Output → Bool)
    (log : List (Entry Input Output)) (i : Nat) (hi : i < log.length)
    (h : bad (log.drop (i + 1)) (log[i]).input (log[i]).answer = true) : prefixBad bad log = true := by
  induction log generalizing i with
  | nil => simp at hi
  | cons entry rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero] at h
      simp [prefixBad, h]
    | succ i =>
      simp only [List.getElem_cons_succ, List.drop_succ_cons] at h
      simp [prefixBad, ih i (by simpa using hi) h]

omit [Fintype Output] [Nonempty Output] in
theorem getElem_mem_drop (log : List (Entry Input Output)) (a b : Nat) (hb : b < log.length) (hab : a < b) :
    log[b] ∈ log.drop (a + 1) := by
  have hb' : b - (a + 1) < (log.drop (a + 1)).length := by
    rw [List.length_drop]
    omega
  have h := List.getElem_mem hb'
  have heq : (log.drop (a + 1))[b - (a + 1)] = log[b] := by
    rw [List.getElem_drop]
    congr 1
    omega
  rw [heq] at h
  exact h

omit [Fintype Output] [Nonempty Output] in
/-- An entry whose input is already stored in another entry's earlier table
is the older one, so its own earlier table is extended by that table. -/
theorem older_extends (log : List (Entry Input Output)) (hord : Ordered log) (hfresh : Fresh log)
    (ex : Entry Input Output) (hex : ex ∈ log) (ey : Entry Input Output) (hey : ey ∈ log)
    (h : (ey.before ex.input).isSome) : Extends ex.before ey.before := by
  obtain ⟨a, ha, hxa⟩ := List.mem_iff_getElem.mp hex
  obtain ⟨b, hb, hyb⟩ := List.mem_iff_getElem.mp hey
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · exfalso
    have hext := (hord a b ha hb hlt).1
    rw [hxa, hyb] at hext
    obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp h
    have := hext _ _ hvalue
    rw [hfresh ex hex] at this
    cases this
  · exfalso
    subst heq
    rw [hxa] at hyb
    subst hyb
    rw [hfresh ex hex] at h
    cases h
  · have hext := (hord b a hb ha hgt).1
    rw [hxa, hyb] at hext
    exact hext

omit [Fintype Output] [Nonempty Output] in
/-- Two stored inputs: if the newer link's earlier table lacks the older
link's input, then the older link was answered after the newer one and its
fresh digest hit a value the newer input mentions. -/
theorem link_present_or_mention {D M : Type*} (mentions : Input → Finset D)
    (log : List (Entry Input (D × M))) (hord : Ordered log)
    (x y : Input) (d : D) (hxy : x ≠ y) (hmention : d ∈ mentions y)
    (ex : Entry Input (D × M)) (hex : ex ∈ log) (hexi : ex.input = x) (hexd : ex.answer.1 = d)
    (ey : Entry Input (D × M)) (hey : ey ∈ log) (heyi : ey.input = y) :
    (ey.before x).isSome ∨ prefixBad (digestMention mentions) log = true := by
  by_cases hpresent : (ey.before x).isSome
  · exact Or.inl hpresent
  right
  obtain ⟨a, ha, hxa⟩ := List.mem_iff_getElem.mp hex
  obtain ⟨b, hb, hyb⟩ := List.mem_iff_getElem.mp hey
  have hab : a ≠ b := by
    intro h
    subst h
    rw [hxa] at hyb
    subst hyb
    exact hxy (hexi.symm.trans heyi)
  rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
  · apply prefixBad_of_index _ log a ha
    rw [hxa]
    refine List.any_eq_true.mpr ⟨ey, ?_, ?_⟩
    · rw [← hyb]
      exact getElem_mem_drop log a b hb hlt
    · rw [heyi, hexd]
      exact decide_eq_true hmention
  · exfalso
    have hpair := (hord b a hb ha hgt).2
    rw [hyb, hxa, hexi] at hpair
    exact hpresent (by rw [hpair]; rfl)

omit [Fintype Output] [Nonempty Output] in
theorem linked_tail {D : Type*} (mentions : Input → Finset D) (p : Input × D) (rest : List (Input × D))
    (h : Linked mentions (p :: rest)) : LinkedTo mentions p.1 rest ∧ Linked mentions rest := by
  cases rest with
  | nil => exact ⟨trivial, trivial⟩
  | cons q rest => exact ⟨h.1, h.2⟩

omit [Fintype Output] [Nonempty Output] in
/-- A stored sink-first chain is entirely present in the sink's earlier
table, or a fresh digest hit a mentioned value. -/
theorem chain_present_or_mention {D M : Type*} (mentions : Input → Finset D)
    (log : List (Entry Input (D × M))) (table : Input → Option (D × M))
    (hord : Ordered log) (hfresh : Fresh log) (htraced : Traced table log) :
    ∀ (links : List (Input × D)) (sink : Input),
      LinkedTo mentions sink links → Linked mentions links →
      (∀ p ∈ links, p.1 ≠ sink) → links.Pairwise (fun p q => p.1 ≠ q.1) →
      Stored table links →
      ∀ ey ∈ log, ey.input = sink →
        Present ey.before links ∨ prefixBad (digestMention mentions) log = true := by
  intro links
  induction links with
  | nil =>
    intro sink _ _ _ _ _ ey _ _
    left
    intro p hp
    simp at hp
  | cons p rest ih =>
    intro sink hto hlinked hne hpairwise hstored ey hey heyi
    obtain ⟨pair, hp, hpd⟩ := hstored p List.mem_cons_self
    obtain ⟨ex, hex, hexi, hexa, _, _⟩ := htraced.1 p.1 pair hp
    have hpmention : p.2 ∈ mentions sink := hto
    rcases link_present_or_mention mentions log hord p.1 sink p.2 (hne p List.mem_cons_self) hpmention
      ex hex hexi (by rw [hexa, hpd]) ey hey heyi with hpres | hbad
    · obtain ⟨hto', hlinked'⟩ := linked_tail mentions p rest hlinked
      have hne' : ∀ q ∈ rest, q.1 ≠ p.1 := fun q hq => (List.pairwise_cons.mp hpairwise).1 q hq |>.symm
      have hstored' : Stored table rest := fun q hq => hstored q (List.mem_cons_of_mem _ hq)
      rcases ih p.1 hto' hlinked' hne' (List.pairwise_cons.mp hpairwise).2 hstored' ex hex hexi with hpres' | hbad'
      · left
        have hold := older_extends log hord hfresh ex hex ey hey (by rw [hexi]; exact hpres)
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hpres
        · obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp (hpres' q hq)
          rw [hold _ _ hvalue]
          rfl
      · exact Or.inr hbad'
    · exact Or.inr hbad

end
end SDitH.Proofs.OracleChain
