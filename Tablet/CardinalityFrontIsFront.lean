import Tablet.CardinalityFront
import Tablet.Front
import Tablet.InfiniteSetEnumeration

-- [TABLET NODE: CardinalityFrontIsFront]
theorem CardinalityFrontIsFront (k : Nat) (X : Set Nat) (hX : X.Infinite) :
    Front (CardinalityFront k X) X := by
-- BODY
  classical
  refine {
    infinite_base := hX
    base_condition := ?_
    prefix_free := ?_
    dense := ?_ }
  · by_cases hk : k = 0
    · left
      ext s
      constructor
      · intro hs
        have hs_card : s.card = 0 := by simpa [hk] using hs.1
        have hs0 : s = ∅ := Finset.card_eq_zero.mp hs_card
        simp [hs0]
      · intro hs
        have hs0 : s = ∅ := by simpa using hs
        subst s
        constructor <;> simp [hk]
    · right
      apply Set.Subset.antisymm
      · intro n hn
        rcases hn with ⟨s, hs, hns⟩
        exact hs.2 hns
      · intro n hn
        have hXn : (X \ {n}).Infinite := hX.sdiff (Set.finite_singleton n)
        obtain ⟨t, htX, htcard⟩ := hXn.exists_subset_card_eq (k - 1)
        have hnt : n ∉ t := by
          intro hnt
          have hdiff := htX hnt
          exact hdiff.2 (by simp)
        refine ⟨insert n t, ?_, Finset.mem_insert_self n t⟩
        constructor
        · rw [Finset.card_insert_of_notMem hnt, htcard]
          omega
        · intro m hm
          rcases Finset.mem_insert.mp hm with rfl | hmt
          · exact hn
          · exact (htX hmt).1
  · intro s t hs ht hst
    rcases hst with hst | ⟨n, hnt, hfilter⟩
    · exact hst
    · have hsub : s ⊆ t := by
        intro m hm
        rw [hfilter] at hm
        exact (Finset.mem_filter.mp hm).1
      have hnots : n ∉ s := by
        intro hns
        rw [hfilter] at hns
        exact (Nat.lt_irrefl n) (Finset.mem_filter.mp hns).2
      have hne : s ≠ t := by
        intro heq
        apply hnots
        rw [heq]
        exact hnt
      have hcardlt : s.card < t.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      exfalso
      rw [hs.1, ht.1] at hcardlt
      exact (Nat.lt_irrefl k) hcardlt
  · intro Y hYX hYinf
    obtain ⟨x, hxrange⟩ := InfiniteSetEnumeration Y hYinf
    by_cases hk : k = 0
    · refine ⟨∅, ?_, ?_⟩
      · constructor <;> simp [CardinalityFront, hk]
      · refine ⟨(x : Nat → Nat) 0, ?_, ?_⟩
        · rw [← hxrange]
          exact Set.mem_range_self 0
        · intro m
          constructor
          · intro hm
            have : False := by simpa using hm
            exact this.elim
          · intro hm
            have hmrange : m ∈ Set.range (x : Nat → Nat) := hxrange.symm ▸ hm.1
            obtain ⟨j, hjm⟩ := Set.mem_range.mp hmrange
            have hxlt : (x : Nat → Nat) j < x 0 := by
              simpa [hjm] using hm.2
            have hjlt : j < 0 := x.lt_iff_lt.mp hxlt
            exact (Nat.not_lt_zero j hjlt).elim
    · refine ⟨Finset.image (x : Nat → Nat) (Finset.range k), ?_, ?_⟩
      · constructor
        · rw [Finset.card_image_of_injective _ x.injective, Finset.card_range]
        · intro m hm
          rcases Finset.mem_image.mp hm with ⟨i, hi, rfl⟩
          apply hYX
          rw [← hxrange]
          exact Set.mem_range_self i
      · refine ⟨(x : Nat → Nat) k, ?_, ?_⟩
        · rw [← hxrange]
          exact Set.mem_range_self k
        · intro m
          constructor
          · intro hm
            rcases Finset.mem_image.mp hm with ⟨i, hi, him⟩
            refine ⟨?_, ?_⟩
            · rw [← hxrange]
              exact ⟨i, him⟩
            · have hilk : (x : Nat → Nat) i < x k :=
                x.lt_iff_lt.mpr (Finset.mem_range.mp hi)
              simpa [him] using hilk
          · rintro ⟨hmY, hmk⟩
            have hmrange : m ∈ Set.range (x : Nat → Nat) := hxrange.symm ▸ hmY
            obtain ⟨j, hjm⟩ := Set.mem_range.mp hmrange
            have hjlt : j < k := x.lt_iff_lt.mp (by simpa [hjm] using hmk)
            exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjlt, hjm⟩
