import Tablet.FrontBridge
import Tablet.FiniteShift
import Tablet.InfiniteSetEnumeration

-- [TABLET NODE: FrontBridgeTerminal]
theorem FrontBridgeTerminal (F : Set (Finset Nat))
    {s t u : Finset Nat} (hb : FrontBridge F s t u)
    (hs : s ∈ F) (ht : t ∈ F) :
    FiniteShift s t := by
-- BODY
  classical
  rw [FrontBridge] at hb
  rcases hb with ⟨hs_tree, ht_tree, ht_ne, hu_ne, hs_init, hs_ext,
    ht_init, ht_tail⟩
  have hsu : InitialSegment s u := hs_init hs
  have htu : InitialSegment t (FrontBridgeTail u) := ht_init ht
  let m : Nat := u.max' hu_ne
  let X : Set Nat := (↑u : Set Nat) ∪ {k : Nat | m < k}
  have hm_mem : m ∈ u := by
    exact Finset.max'_mem u hu_ne
  have hle_max : ∀ k ∈ u, k ≤ m := by
    intro k hk
    exact Finset.le_max' u k hk
  have hXinf : X.Infinite := by
    have hrange : (Set.range (fun n : Nat => m + 1 + n)).Infinite :=
      Set.infinite_range_of_injective (by
        intro a b hab
        exact Nat.add_left_cancel hab)
    apply Set.Infinite.mono ?_ hrange
    intro k hk
    rcases Set.mem_range.mp hk with ⟨n, rfl⟩
    right
    dsimp
    omega
  obtain ⟨x, hx⟩ := InfiniteSetEnumeration X hXinf
  have hx_mem : ∀ k : Nat, x k ∈ X := by
    intro k
    rw [← hx]
    exact ⟨k, rfl⟩
  have hx0_le : ∀ {k : Nat}, k ∈ X → x 0 ≤ k := by
    intro k hk
    rw [← hx] at hk
    rcases Set.mem_range.mp hk with ⟨n, hn⟩
    rw [← hn]
    exact x.monotone (Nat.zero_le n)
  have hx0_mem : x 0 ∈ u := by
    rcases hx_mem 0 with hx0 | hx0
    · exact Finset.mem_coe.mp hx0
    · have hxm : x 0 ≤ m := hx0_le (Or.inl (Finset.mem_coe.mpr hm_mem))
      change m < x 0 at hx0
      exact False.elim ((Nat.not_lt_of_ge hxm) hx0)
  have hprefix_u : ∀ (a : Finset Nat), InitialSegment a u →
      ProperPrefixSet a (Set.range (x : Nat → Nat)) := by
    intro a ha
    rcases ha with rfl | ⟨q, hq, ha⟩
    · refine ⟨m + 1, ?_, ?_⟩
      rw [hx]
      right
      exact Nat.lt_succ_self m
      intro k
      rw [hx]
      constructor
      · intro hk
        exact ⟨Or.inl (Finset.mem_coe.mpr hk),
          Nat.lt_succ_of_le (hle_max k hk)⟩
      · rintro ⟨hk | hk, hkm⟩
        · exact Finset.mem_coe.mp hk
        · change m < k at hk
          exact False.elim ((Nat.not_lt_of_ge (Nat.succ_le_of_lt hk)) hkm)
    · have hq_max : q ≤ m := hle_max q hq
      refine ⟨q, ?_, ?_⟩
      · rw [hx]
        exact Or.inl (Finset.mem_coe.mpr hq)
      · intro k
        rw [ha]
        rw [hx]
        rw [Finset.mem_filter]
        constructor
        · intro hk
          exact ⟨Or.inl (Finset.mem_coe.mpr hk.1), hk.2⟩
        · rintro ⟨hk | hk, hkq⟩
          · exact ⟨Finset.mem_coe.mp hk, hkq⟩
          · change m < k at hk
            exact False.elim ((Nat.not_lt_of_ge
              (Nat.le_trans hq_max (Nat.le_of_lt hk))) hkq)
  have htail_range :
      Set.range (ShiftMap x : Nat → Nat) =
        (↑(FrontBridgeTail u) : Set Nat) ∪ {k : Nat | m < k} := by
    apply Set.ext
    intro k
    constructor
    · rintro ⟨n, rfl⟩
      change x (n + 1) ∈ _
      rcases hx_mem (n + 1) with hxu | hgt
      · left
        apply Finset.mem_coe.mpr
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_coe.mp hxu, ?_⟩
        refine ⟨x 0, Finset.mem_coe.mp hx0_mem, ?_⟩
        exact x.strictMono (Nat.zero_lt_succ n)
      · right
        exact hgt
    · intro hk
      rcases hk with hk | hk
      · obtain ⟨n, hn⟩ := (show k ∈ Set.range (x : Nat → Nat) by
          rw [hx]
          left
          exact Finset.mem_coe.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).1)
        have hn0 : n ≠ 0 := by
          intro hn0
          subst n
          obtain ⟨ha_u, htail⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hk)
          obtain ⟨a, ha, hak⟩ := htail
          have hle : x 0 ≤ a := hx0_le (Or.inl (Finset.mem_coe.mpr ha))
          have hle' : k ≤ a := by simpa [hn] using hle
          exact (Nat.not_lt_of_ge hle') hak
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        refine ⟨j, ?_⟩
        change x (j + 1) = k
        simpa [hj, Nat.succ_eq_add_one] using hn
      · obtain ⟨n, hn⟩ := (show k ∈ Set.range (x : Nat → Nat) by
          rw [hx]
          right
          exact hk)
        have hn0 : n ≠ 0 := by
          intro hn0
          subst n
          have hle : x 0 ≤ m := hx0_le (Or.inl (Finset.mem_coe.mpr hm_mem))
          change m < k at hk
          have hmk : m < x 0 := by simpa [hn] using hk
          exact (Nat.not_lt_of_ge hle) hmk
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        refine ⟨j, ?_⟩
        change x (j + 1) = k
        simpa [hj, Nat.succ_eq_add_one] using hn
  have hprefix_tail :
      ProperPrefixSet t (Set.range (ShiftMap x : Nat → Nat)) := by
    rcases htu with rfl | ⟨q, hq, hcut⟩
    · refine ⟨m + 1, ?_, ?_⟩
      rw [htail_range]
      right
      exact Nat.lt_succ_self m
      intro k
      rw [htail_range]
      constructor
      · intro hk
        have hk_u : k ∈ u :=
          (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).1
        exact ⟨Or.inl hk, Nat.lt_succ_of_le (hle_max k hk_u)⟩
      · rintro ⟨hk | hk, hkm⟩
        · exact Finset.mem_coe.mpr hk
        · change m < k at hk
          exact False.elim ((Nat.not_lt_of_ge (Nat.succ_le_of_lt hk)) hkm)
    · have hq_max : q ≤ m := by
        exact hle_max q (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).1
      refine ⟨q, ?_, ?_⟩
      · rw [htail_range]
        exact Or.inl hq
      · intro k
        rw [hcut]
        rw [htail_range]
        rw [Finset.mem_filter]
        constructor
        · intro hk
          exact ⟨Or.inl (Finset.mem_coe.mpr hk.1), hk.2⟩
        · rintro ⟨hk | hk, hkq⟩
          · exact ⟨Finset.mem_coe.mp hk, hkq⟩
          · change m < k at hk
            exact False.elim ((Nat.not_lt_of_ge
              (Nat.le_trans hq_max (Nat.le_of_lt hk))) hkq)
  exact ⟨x, hprefix_u s hsu, hprefix_tail⟩
