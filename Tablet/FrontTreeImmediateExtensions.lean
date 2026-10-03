import Tablet.Front
import Tablet.PrefixTree
import Tablet.ProperInitialSegment

-- [TABLET NODE: FrontTreeImmediateExtensions]
theorem FrontTreeImmediateExtensions (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (s : Finset Nat) (hs : s ∈ PrefixTree F)
    (hsF : s ∉ F) :
    Nonempty {n : Nat // ProperInitialSegment s (insert n s) ∧
      insert n s ∈ PrefixTree F} ∧
      Countable {n : Nat // ProperInitialSegment s (insert n s) ∧
        insert n s ∈ PrefixTree F} := by
-- BODY
  classical
  have _ := hF
  rcases hs with ⟨t, htF, hst⟩
  have hne : s ≠ t := by
    intro hst'
    apply hsF
    rw [hst']
    exact htF
  rcases hst with hst_eq | ⟨m, hmt, hsm⟩
  · exact (hne hst_eq).elim
  have hm_not_s : m ∉ s := by
    intro hms
    rw [hsm] at hms
    exact Nat.lt_irrefl m (Finset.mem_filter.mp hms).2
  let d : Finset Nat := t.filter (fun k => k ∉ s)
  have hd_nonempty : d.Nonempty := by
    refine ⟨m, ?_⟩
    exact Finset.mem_filter.mpr ⟨hmt, hm_not_s⟩
  let n : Nat := d.min' hd_nonempty
  have hn_d : n ∈ d := by
    exact Finset.min'_mem d hd_nonempty
  have hn_t : n ∈ t := (Finset.mem_filter.mp hn_d).1
  have hn_not_s : n ∉ s := (Finset.mem_filter.mp hn_d).2
  have hn_le_m : n ≤ m := by
    exact Finset.min'_le d m (Finset.mem_filter.mpr ⟨hmt, hm_not_s⟩)
  have hm_le_n : m ≤ n := by
    by_contra hmn
    have hnm : n < m := Nat.lt_of_not_ge hmn
    have hns : n ∈ s := by
      rw [hsm]
      exact Finset.mem_filter.mpr ⟨hn_t, hnm⟩
    exact hn_not_s hns
  have hnm : n = m := Nat.le_antisymm hn_le_m hm_le_n
  have hs_filter : s = t.filter (fun k => k < n) := by
    rw [hnm]
    exact hsm
  have hinsert_sub : insert n s ⊆ t := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hks
    · exact hn_t
    · have hks' : k ∈ t.filter (fun z => z < n) := hs_filter ▸ hks
      exact (Finset.mem_filter.mp hks').1
  have hinit_insert : InitialSegment (insert n s) t := by
    by_cases hu : (t.filter (fun k => n < k)).Nonempty
    · let q : Nat := (t.filter (fun k => n < k)).min' hu
      have hq_t : q ∈ t :=
        (Finset.mem_filter.mp (Finset.min'_mem (t.filter (fun k => n < k)) hu)).1
      have hnq : n < q :=
        (Finset.mem_filter.mp (Finset.min'_mem (t.filter (fun k => n < k)) hu)).2
      refine Or.inr ⟨q, hq_t, ?_⟩
      ext k
      constructor
      · intro hk
        rcases Finset.mem_insert.mp hk with rfl | hks
        · exact Finset.mem_filter.mpr ⟨hn_t, hnq⟩
        · have hks' : k ∈ t.filter (fun z => z < n) := hs_filter ▸ hks
          have hkt : k ∈ t := (Finset.mem_filter.mp hks').1
          have hkn : k < n := (Finset.mem_filter.mp hks').2
          exact Finset.mem_filter.mpr ⟨hkt, hkn.trans hnq⟩
      · intro hk
        have hkt : k ∈ t := (Finset.mem_filter.mp hk).1
        have hkq : k < q := (Finset.mem_filter.mp hk).2
        by_cases hkn : k < n
        · have hks : k ∈ s := by
            rw [hs_filter]
            exact Finset.mem_filter.mpr ⟨hkt, hkn⟩
          exact Finset.mem_insert.mpr (Or.inr hks)
        · have hnk : n ≤ k := Nat.le_of_not_gt hkn
          by_cases hnk' : n < k
          · have hkU : k ∈ t.filter (fun z => n < z) :=
              Finset.mem_filter.mpr ⟨hkt, hnk'⟩
            have hqk : q ≤ k :=
              Finset.min'_le (t.filter (fun z => n < z)) k hkU
            exact False.elim ((Nat.not_lt_of_ge hqk) hkq)
          · have hkn' : k = n := Nat.le_antisymm (Nat.le_of_not_gt hnk') hnk
            exact Finset.mem_insert.mpr (Or.inl hkn')
    · have hu_empty : t.filter (fun k => n < k) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hu
      left
      apply Finset.Subset.antisymm
      · exact hinsert_sub
      · intro k hk
        by_cases hkn : k < n
        · have hks : k ∈ s := by
            rw [hs_filter]
            exact Finset.mem_filter.mpr ⟨hk, hkn⟩
          exact Finset.mem_insert.mpr (Or.inr hks)
        · have hnk : n ≤ k := Nat.le_of_not_gt hkn
          by_cases hnk' : n < k
          · have hkU : k ∈ t.filter (fun z => n < z) :=
              Finset.mem_filter.mpr ⟨hk, hnk'⟩
            rw [hu_empty] at hkU
            have : False := by simp at hkU
            exact this.elim
          · exact Finset.mem_insert.mpr
              (Or.inl (Nat.le_antisymm (Nat.le_of_not_gt hnk') hnk))
  constructor
  · refine ⟨⟨n, ?_, ?_⟩⟩
    · have hs_cut : s = (insert n s).filter (fun k => k < n) := by
        ext k
        constructor
        · intro hks
          have hks' : k ∈ t.filter (fun z => z < n) := hs_filter ▸ hks
          have hkt : k ∈ t := (Finset.mem_filter.mp hks').1
          have hkn : k < n := (Finset.mem_filter.mp hks').2
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_insert.mpr (Or.inr hks), hkn⟩
        · intro hk
          have hk' := Finset.mem_filter.mp hk
          rcases Finset.mem_insert.mp hk'.1 with hkn | hks
          · exact (Nat.lt_irrefl n (hkn ▸ hk'.2)).elim
          · exact hks
      have hs_init : InitialSegment s (insert n s) :=
        Or.inr ⟨n, Finset.mem_insert_self n s, hs_cut⟩
      refine ⟨hs_init, ?_⟩
      intro heq
      apply hn_not_s
      rw [heq]
      exact Finset.mem_insert_self n s
    · exact ⟨t, htF, hinit_insert⟩
  · infer_instance
