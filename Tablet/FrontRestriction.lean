import Tablet.Front
import Tablet.FrontRestrict

-- [TABLET NODE: FrontRestriction]
theorem FrontRestriction (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (Y : Set Nat) (hY : Y ⊆ X) (hYinf : Y.Infinite) :
    Front (FrontRestrict F Y) Y := by
-- BODY
  classical
  refine
    { infinite_base := hYinf
      base_condition := ?_
      prefix_free := ?_
      dense := ?_ }
  · by_cases htriv : FrontRestrict F Y = {∅}
    · exact Or.inl htriv
    · right
      have hempty_not : (∅ : Finset Nat) ∉ FrontRestrict F Y := by
        intro hempty
        apply htriv
        ext t
        constructor
        · intro ht
          have hempty_init : InitialSegment (∅ : Finset Nat) t := by
            rcases t.eq_empty_or_nonempty with ht0 | ht0
            · exact Or.inl ht0.symm
            · right
              let m := t.min' ht0
              refine ⟨m, Finset.min'_mem t ht0, ?_⟩
              ext k
              constructor
              · intro hk
                simp at hk
              · intro hk
                have hkT : k ∈ t := (Finset.mem_filter.mp hk).1
                have hkm : k < m := (Finset.mem_filter.mp hk).2
                exact (Nat.not_lt_of_ge (Finset.min'_le t k hkT) hkm).elim
          have heq : (∅ : Finset Nat) = t :=
            hF.prefix_free hempty.1 ht.1 hempty_init
          have ht0 : t = ∅ := heq.symm
          simpa [ht0]
        · intro ht
          have ht0 : t = ∅ := by simpa using ht
          simpa [ht0] using hempty
      apply Set.Subset.antisymm
      · intro n hn
        rcases hn with ⟨s, hs, hns⟩
        exact hs.2 n hns
      · intro n hnY
        have htail : (Y \ Set.Iio n).Infinite :=
          hYinf.sdiff (Set.finite_Iio n)
        have htail_sub : Y \ Set.Iio n ⊆ Y := by
          intro k hk
          exact hk.1
        obtain ⟨s, hsF, hsP⟩ :=
          hF.dense (Y \ Set.Iio n) (htail_sub.trans hY) htail
        rcases hsP with ⟨m, hmY, hsm⟩
        have hsne : s.Nonempty := by
          by_contra hsne
          have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
          apply hempty_not
          refine ⟨?_, ?_⟩
          · simpa [hs0] using hsF
          · simp
        have hnm : n < m := by
          have hmn : n ≤ m := by
            exact Nat.le_of_not_gt (fun hmn => hmY.2 hmn)
          by_contra hnm'
          have hmn' : m = n := Nat.le_antisymm (Nat.le_of_not_gt hnm') hmn
          have hs0 : s = ∅ := by
            apply Finset.not_nonempty_iff_eq_empty.mp
            intro hsne0
            obtain ⟨k, hk⟩ := hsne0
            have hks : k ∈ Y \ Set.Iio n ∧ k < m := (hsm k).mp hk
            exact hks.1.2 (by simpa [hmn'] using hks.2)
          simpa [hs0] using hsne
        have hns : n ∈ s :=
          (hsm n).mpr ⟨⟨hnY, by exact Nat.not_lt.mpr (Nat.le_refl n)⟩, hnm⟩
        have hsY : ∀ k, k ∈ s → k ∈ Y := by
          intro k hk
          exact (hsm k).mp hk |>.1.1
        exact ⟨s, ⟨hsF, hsY⟩, hns⟩
  · intro s t hs ht hst
    exact hF.prefix_free hs.1 ht.1 hst
  · intro Z hZY hZinf
    obtain ⟨s, hsF, hsP⟩ := hF.dense Z (hZY.trans hY) hZinf
    rcases hsP with ⟨n, hnZ, hsn⟩
    refine ⟨s, ?_, ?_⟩
    · refine ⟨hsF, ?_⟩
      intro k hk
      exact hZY ((hsn k).mp hk).1
    · exact ⟨n, hnZ, hsn⟩
