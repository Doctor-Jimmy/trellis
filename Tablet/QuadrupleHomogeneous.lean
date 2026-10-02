import Tablet.CardinalityFrontIsFront
import Tablet.NashWilliams

-- [TABLET NODE: QuadrupleHomogeneous]
theorem QuadrupleHomogeneous (X : Set Nat) (hX : X.Infinite)
    (c : Finset Nat → Bool) :
    ∃ Y : Set Nat, Y ⊆ X ∧ Y.Infinite ∧
      ∃ b : Bool, ∀ s : Finset Nat,
        s.card = 4 → (↑s : Set Nat) ⊆ Y → c s = b := by
-- BODY
  classical
  let F : Set (Finset Nat) := CardinalityFront 4 X
  have hF : Front F X := CardinalityFrontIsFront 4 X hX
  let S : Set (Finset Nat) := {s | s ∈ F ∧ c s = true}
  have hS : S ⊆ F := by
    intro s hs
    exact hs.1
  obtain ⟨F', Y, hF', hFsub, hdec⟩ := NashWilliams F X hF S hS
  have htriv : F' ≠ ({∅} : Set (Finset Nat)) := by
    intro heq
    obtain ⟨t, htF', _⟩ := hF'.dense Y (by intro n hn; exact hn)
      hF'.infinite_base
    have htF := hFsub htF'
    have htcard : t.card = 4 := htF.1
    have htne : t ≠ (∅ : Finset Nat) := by
      intro ht0
      subst t
      simp at htcard
    have ht0 : t = (∅ : Finset Nat) := by
      simpa [heq] using htF'
    exact htne ht0
  have hbase : FrontBase F' = Y :=
    (FrontNontrivialBase F' Y hF' htriv).2
  have hYX : Y ⊆ X := by
    intro y hy
    have hybase : y ∈ FrontBase F' := by
      rw [hbase]
      exact hy
    rcases hybase with ⟨s, hsF', hys⟩
    exact (hFsub hsF').2 hys
  have hquad : ∀ s : Finset Nat, s.card = 4 →
      (↑s : Set Nat) ⊆ Y → s ∈ F' := by
    intro s hs hsy
    have hsne : s.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hs0
      subst s
      simp at hs
    let m : Nat := s.max' hsne
    have hm : m ∈ s := Finset.max'_mem s hsne
    have htail : (TailSet Y m).Infinite := by
      apply Set.Infinite.mono (s := Y \ Set.Iic m) (t := TailSet Y m)
      · intro k hk
        exact ⟨hk.1, Nat.lt_of_not_ge hk.2⟩
      · exact hF'.infinite_base.sdiff (Set.finite_Iic m)
    let Z : Set Nat := (↑s : Set Nat) ∪ TailSet Y m
    have hZY : Z ⊆ Y := by
      intro k hk
      change k ∈ (s : Set Nat) ∨ k ∈ TailSet Y m at hk
      rcases hk with hkS | hkT
      · exact hsy hkS
      · exact hkT.1
    have hZinf : Z.Infinite := by
      apply Set.Infinite.mono (s := TailSet Y m) (t := Z)
      · intro k hk
        change k ∈ (s : Set Nat) ∨ k ∈ TailSet Y m
        exact Or.inr hk
      · exact htail
    obtain ⟨t, htF', htP⟩ := hF'.dense Z hZY hZinf
    rcases htP with ⟨n, hnZ, htn⟩
    have htcard : t.card = 4 := (hFsub htF').1
    have hteq : t = s := by
      change n ∈ (s : Set Nat) ∨ n ∈ TailSet Y m at hnZ
      rcases hnZ with hnS | hnT
      · have hnm : n ≤ m := Finset.le_max' s n hnS
        have htsub : t ⊆ s.erase n := by
          intro k hkt
          have hk := (htn k).mp hkt
          rcases hk.1 with hkS | hkT
          · exact Finset.mem_erase.mpr ⟨Nat.ne_of_lt hk.2, hkS⟩
          · change k ∈ Y ∧ m < k at hkT
            exact (False.elim (by omega : False))
        have hcardle := Finset.card_le_card htsub
        have herase : (s.erase n).card = 3 := by
          rw [Finset.card_erase_of_mem hnS, hs]
        rw [herase] at hcardle
        omega
      · have hnT : n ∈ Y ∧ m < n := hnT
        have hsub : s ⊆ t := by
          intro k hk
          apply (htn k).mpr
          refine ⟨?_, ?_⟩
          · exact Or.inl hk
          · exact lt_of_le_of_lt (Finset.le_max' s k hk) hnT.2
        apply Finset.Subset.antisymm
        · intro k hkt
          have hk := (htn k).mp hkt
          rcases hk.1 with hkS | hkT
          · exact hkS
          · have hkn : k ∈ t := by
              apply (htn k).mpr
              exact ⟨Or.inr hkT, hk.2⟩
            by_cases hks : k ∈ s
            · exact hks
            · have hins : insert k s ⊆ t := by
                intro q hq
                rcases Finset.mem_insert.mp hq with rfl | hq
                · exact hkn
                · exact hsub hq
              have hcardle := Finset.card_le_card hins
              rw [Finset.card_insert_of_notMem hks, hs] at hcardle
              omega
        · exact hsub
    rw [← hteq]
    exact htF'
  refine ⟨Y, hYX, hF'.infinite_base, ?_⟩
  rcases hdec with hdec | hdec
  · refine ⟨true, ?_⟩
    intro s hs hsy
    have hsF' := hquad s hs hsy
    exact (hdec hsF').2
  · refine ⟨false, ?_⟩
    intro s hs hsy
    have hsF' := hquad s hs hsy
    have hsF := hFsub hsF'
    have hsnot : s ∉ S := by
      intro hsS
      have hmem : s ∈ F' ∩ S := ⟨hsF', hsS⟩
      rw [hdec] at hmem
      simpa using hmem
    have hcne : c s ≠ true := by
      intro hc
      exact hsnot ⟨hsF, hc⟩
    have hc0 : c s = false := by
      cases hcs : c s with
      | false => rfl
      | true => exact (hcne (by simpa [hcs])).elim
    simpa using hc0
