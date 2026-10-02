import Tablet.FrontTreeWellFounded

-- [TABLET NODE: FrontTreeOrderedExtension]
theorem FrontTreeOrderedExtension (F : Set (Finset Nat))
    (hF : Front F Set.univ) (s : Finset Nat)
    (hs : s ∈ PrefixTree F) (hsF : s ∉ F) (n : Nat)
    (hn : ProperInitialSegment s (insert n s)) :
    insert n s ∈ PrefixTree F := by
-- BODY
  classical
  rcases hs with ⟨t, htF, hst⟩
  have hst_ne : s ≠ t := by
    intro hst_eq
    exact hsF (hst_eq ▸ htF)
  rcases hst with hst_eq | ⟨r, hr, hst_filter⟩
  · exact (hst_ne hst_eq).elim
  have hst_init : InitialSegment s t := Or.inr ⟨r, hr, hst_filter⟩
  rcases hn with ⟨hn_init, hn_ne⟩
  rcases hn_init with hn_eq | ⟨c, hc, hcut⟩
  · exact (hn_ne hn_eq).elim
  have hc_not_s : c ∉ s := by
    intro hcs
    have hcf : c ∈ (insert n s).filter (fun k => k < c) := by
      rw [← hcut]
      exact hcs
    exact (Nat.lt_irrefl c) (Finset.mem_filter.mp hcf).2
  have hc_n : c = n := by
    rcases Finset.mem_insert.mp hc with hcn | hcs
    · exact hcn
    · exact (hc_not_s hcs).elim
  subst c
  have hs_lt : ∀ ⦃k⦄, k ∈ s → k < n := by
    intro k hk
    have hkf : k ∈ (insert n s).filter (fun j => j < n) := by
      rw [← hcut]
      exact hk
    exact (Finset.mem_filter.mp hkf).2
  let Y : Set Nat := (↑(insert n s) : Set Nat) ∪ {k | n < k}
  have hYsub : Y ⊆ (Set.univ : Set Nat) := by
    intro k hk
    trivial
  have hYinf : Y.Infinite := by
    have hrange : (Set.range (fun k : Nat => n + 1 + k)).Infinite :=
      Set.infinite_range_of_injective (by
        intro a b hab
        exact Nat.add_left_cancel hab)
    apply Set.Infinite.mono ?_ hrange
    intro k hk
    rcases Set.mem_range.mp hk with ⟨m, rfl⟩
    right
    dsimp
    omega
  obtain ⟨w, hwF, hwY⟩ := hF.dense Y hYsub hYinf
  rcases hwY with ⟨p, hpY, hwp⟩
  have hs_cutY : ∀ k, k ∈ s ↔ k ∈ Y ∧ k < n := by
    intro k
    constructor
    · intro hks
      refine ⟨?_, hs_lt hks⟩
      left
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem hks)
    · rintro ⟨hkY, hkn⟩
      rcases hkY with hk_ins | hk_gt
      · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hk_ins) with hkn_eq | hks
        · omega
        · exact hks
      · exact False.elim (Nat.lt_asymm hk_gt hkn)
  have htrans : ∀ {a b c : Finset Nat},
      InitialSegment a b → InitialSegment b c → InitialSegment a c := by
    intro a b c hab hbc
    rcases hab with rfl | ⟨m, hm, rfl⟩
    · exact hbc
    · rcases hbc with rfl | ⟨q, hq, rfl⟩
      · exact Or.inr ⟨m, hm, rfl⟩
      · right
        refine ⟨m, ?_, ?_⟩
        · exact (Finset.mem_filter.mp hm).1
        · apply Finset.ext
          intro k
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨hk, hkm⟩, hkn⟩
            exact ⟨hk, hkn⟩
          · rintro ⟨hk, hkn⟩
            exact ⟨⟨hk, lt_trans hkn (Finset.mem_filter.mp hm).2⟩, hkn⟩
  have hp_gt_n : n < p := by
    by_contra hp_not
    have hp_le : p ≤ n := Nat.le_of_not_gt hp_not
    rcases lt_or_eq_of_le hp_le with hp_lt | hp_eq
    · have hp_s : p ∈ s := by
        rcases hpY with hp_ins | hp_gt
        · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hp_ins) with hpn | hps
          · omega
          · exact hps
        · exact False.elim (Nat.lt_asymm hp_gt hp_lt)
      have hw_filter : w = s.filter (fun k => k < p) := by
        apply Finset.ext
        intro k
        constructor
        · intro hkw
          have hkw' := (hwp k).mp hkw
          exact Finset.mem_filter.mpr
            ⟨(hs_cutY k).mpr ⟨hkw'.1, lt_trans hkw'.2 hp_lt⟩, hkw'.2⟩
        · intro hks
          have hks' := Finset.mem_filter.mp hks
          exact (hwp k).mpr ⟨((hs_cutY k).mp hks'.1).1, hks'.2⟩
      have hw_init_s : InitialSegment w s := Or.inr ⟨p, hp_s, hw_filter⟩
      have hw_init_t : InitialSegment w t := htrans hw_init_s hst_init
      have hwt : w = t := hF.prefix_free hwF htF hw_init_t
      have hw_sub_s : ∀ ⦃k⦄, k ∈ w → k ∈ s := by
        intro k hkw
        have hkw' := (hwp k).mp hkw
        exact (hs_cutY k).mpr ⟨hkw'.1, lt_trans hkw'.2 hp_lt⟩
      have hr_s : r ∉ s := by
        intro hrs
        have hrf : r ∈ t.filter (fun k => k < r) := by
          rw [← hst_filter]
          exact hrs
        exact (Nat.lt_irrefl r) (Finset.mem_filter.mp hrf).2
      have hr_w : r ∈ w := by
        rw [hwt]
        exact hr
      exact hr_s (hw_sub_s hr_w)
    · subst p
      have hw_eq_s : w = s := by
        apply Finset.ext
        intro k
        exact (hwp k).trans (hs_cutY k).symm
      exact hsF (hw_eq_s ▸ hwF)
  have hv_sub_w : insert n s ⊆ w := by
    intro k hk
    rcases Finset.mem_insert.mp hk with hkn | hks
    · subst k
      exact (hwp n).mpr ⟨by left; exact Finset.mem_coe.mpr (Finset.mem_insert_self n s), hp_gt_n⟩
    · have hks' := (hs_cutY k).mp hks
      exact (hwp k).mpr ⟨hks'.1, lt_trans hks'.2 hp_gt_n⟩
  by_cases hw_eq_v : w = insert n s
  · exact ⟨w, hwF, Or.inl hw_eq_v.symm⟩
  have hp_succ : n + 1 < p := by
    have hp_le_succ : n + 1 ≤ p := Nat.succ_le_iff.mpr hp_gt_n
    rcases lt_or_eq_of_le hp_le_succ with hlt | heq
    · exact hlt
    · subst p
      exfalso
      apply hw_eq_v
      apply Finset.ext
      intro k
      constructor
      · intro hkw
        have hkw' := (hwp k).mp hkw
        have hklt := hkw'.2
        rcases hkw'.1 with hk_ins | hk_gt
        · exact Finset.mem_coe.mp hk_ins
        · have hk_le_n : k ≤ n := Nat.le_of_lt_succ hklt
          exact False.elim ((Nat.not_lt_of_ge hk_le_n) hk_gt)
      · intro hkv
        have hkv' := Finset.mem_insert.mp hkv
        rcases hkv' with hkn | hks
        · subst k
          exact (hwp n).mpr ⟨by left; exact Finset.mem_coe.mpr (Finset.mem_insert_self n s), hp_gt_n⟩
        · exact (hwp k).mpr ⟨((hs_cutY k).mp hks).1, lt_trans (hs_lt hks) hp_gt_n⟩
  have hv_filter : insert n s = w.filter (fun k => k < n + 1) := by
    apply Finset.ext
    intro k
    constructor
    · intro hkv
      exact Finset.mem_filter.mpr ⟨hv_sub_w hkv, by
        rcases Finset.mem_insert.mp hkv with hkn | hks
        · subst k
          exact Nat.lt_succ_self n
        · exact Nat.lt_succ_of_lt (hs_lt hks)⟩
    · intro hkw
      have hkw' := Finset.mem_filter.mp hkw
      have hkwY := (hwp k).mp hkw'.1
      rcases hkwY.1 with hk_ins | hk_gt
      · exact Finset.mem_coe.mp hk_ins
      · have hk_le_n : k ≤ n := Nat.le_of_lt_succ hkw'.2
        exact False.elim ((Nat.not_lt_of_ge hk_le_n) hk_gt)
  have hp1Y : n + 1 ∈ Y := by
    right
    dsimp
    omega
  exact ⟨w, hwF, Or.inr ⟨n + 1, (hwp (n + 1)).mpr ⟨hp1Y, hp_succ⟩, hv_filter⟩⟩
