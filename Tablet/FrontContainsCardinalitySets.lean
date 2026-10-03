import Tablet.Front
import Tablet.TailSet

-- [TABLET NODE: FrontContainsCardinalitySets]
theorem FrontContainsCardinalitySets (k : Nat) (F : Set (Finset Nat)) (Y : Set Nat)
    (hF : Front F Y) (hcard : ∀ t ∈ F, t.card = k) (hk : 0 < k) :
    ∀ s : Finset Nat, s.card = k → (↑s : Set Nat) ⊆ Y → s ∈ F := by
-- BODY
  classical
  intro s hs hsy
  have hsne : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hs0
    subst s
    simp at hs
    omega
  let m : Nat := s.max' hsne
  have htail : (TailSet Y m).Infinite := by
    apply Set.Infinite.mono (s := Y \ Set.Iic m) (t := TailSet Y m)
    · intro q hq
      exact ⟨hq.1, Nat.lt_of_not_ge hq.2⟩
    · exact hF.infinite_base.sdiff (Set.finite_Iic m)
  let Z : Set Nat := (↑s : Set Nat) ∪ TailSet Y m
  have hZY : Z ⊆ Y := by
    intro q hq
    change q ∈ (s : Set Nat) ∨ q ∈ TailSet Y m at hq
    rcases hq with hqS | hqT
    · exact hsy hqS
    · exact hqT.1
  have hZinf : Z.Infinite := by
    apply Set.Infinite.mono (s := TailSet Y m) (t := Z)
    · intro q hq
      change q ∈ (s : Set Nat) ∨ q ∈ TailSet Y m
      exact Or.inr hq
    · exact htail
  obtain ⟨t, htF, htP⟩ := hF.dense Z hZY hZinf
  rcases htP with ⟨n, hnZ, htn⟩
  have htcard : t.card = k := hcard t htF
  have hteq : t = s := by
    change n ∈ (s : Set Nat) ∨ n ∈ TailSet Y m at hnZ
    rcases hnZ with hnS | hnT
    · have hnm : n ≤ m := Finset.le_max' s n hnS
      have htsub : t ⊆ s.erase n := by
        intro q hqt
        have hq := (htn q).mp hqt
        rcases hq.1 with hqS | hqT
        · exact Finset.mem_erase.mpr ⟨Nat.ne_of_lt hq.2, hqS⟩
        · change q ∈ Y ∧ m < q at hqT
          exact (False.elim (by omega : False))
      have hcardle := Finset.card_le_card htsub
      have herase : (s.erase n).card = k - 1 := by
        rw [Finset.card_erase_of_mem hnS, hs]
      rw [herase] at hcardle
      omega
    · have hnT : n ∈ Y ∧ m < n := hnT
      have hsub : s ⊆ t := by
        intro q hq
        apply (htn q).mpr
        refine ⟨?_, ?_⟩
        · exact Or.inl hq
        · exact lt_of_le_of_lt (Finset.le_max' s q hq) hnT.2
      apply Finset.Subset.antisymm
      · intro q hqt
        have hq := (htn q).mp hqt
        rcases hq.1 with hqS | hqT
        · exact hqS
        · have hqn : q ∈ t := by
            apply (htn q).mpr
            exact ⟨Or.inr hqT, hq.2⟩
          by_cases hqs : q ∈ s
          · exact hqs
          · have hins : insert q s ⊆ t := by
              intro r hr
              rcases Finset.mem_insert.mp hr with rfl | hr
              · exact hqn
              · exact hsub hr
            have hcardle := Finset.card_le_card hins
            rw [Finset.card_insert_of_notMem hqs, hs] at hcardle
            omega
      · exact hsub
  rw [← hteq]
  exact htF
