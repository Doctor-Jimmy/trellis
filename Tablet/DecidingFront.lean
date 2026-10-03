import Tablet.DecidingFrontSet
import Tablet.DecidingFrontAgreement
import Tablet.DecidingFrontMinimal
import Tablet.Front
import Tablet.InfiniteSetEnumeration

universe u

-- [TABLET NODE: DecidingFront]
theorem DecidingFront {E : Type u} (h : MultiSequence E)
    (hlc : LocallyConstant h) :
    Front (DecidingFrontSet h) Set.univ := by
-- BODY
  classical
  let F : Set (Finset Nat) := DecidingFrontSet h
  have hproper : ∀ (x : IncSeq) (n : Nat),
      ProperPrefixSet (Finset.image x (Finset.range n))
        (Set.range (x : Nat → Nat)) := by
    intro x n
    refine ⟨x n, ⟨n, rfl⟩, ?_⟩
    intro k
    constructor
    · intro hk
      rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, x.lt_iff_lt.mpr (Finset.mem_range.mp hi)⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (x.lt_iff_lt.mp hi), rfl⟩
  have hdecide : ∀ x : IncSeq, ∃ s : Finset Nat,
      DecidingPrefix h s ∧ ProperPrefixSet s (Set.range (x : Nat → Nat)) := by
    intro x
    obtain ⟨n, hn⟩ := hlc x
    refine ⟨Finset.image x (Finset.range n), ?_, hproper x n⟩
    intro y z hy hz
    exact (hn y (DecidingFrontAgreement hy)).trans
      (hn z (DecidingFrontAgreement hz)).symm
  have hprefix_initial : ∀ {t s : Finset Nat} {Y : Set Nat},
      InitialSegment t s → ProperPrefixSet s Y → ProperPrefixSet t Y := by
    intro t s Y hts hs
    rcases hts with rfl | ⟨b, hb, ht⟩
    · exact hs
    rcases hs with ⟨a, ha, hsa⟩
    have hba : b < a := (hsa b).mp hb |>.2
    have hbY : b ∈ Y := (hsa b).mp hb |>.1
    refine ⟨b, hbY, ?_⟩
    intro k
    constructor
    · intro hkt
      have hkt' : k ∈ s.filter (fun z => z < b) := by
        rw [← ht]
        exact hkt
      have hks : k ∈ s := (Finset.mem_filter.mp hkt').1
      exact ⟨(hsa k).mp hks |>.1, (Finset.mem_filter.mp hkt').2⟩
    · rintro ⟨hkY, hkb⟩
      have hks : k ∈ s := (hsa k).mpr ⟨hkY, lt_trans hkb hba⟩
      rw [ht]
      exact Finset.mem_filter.mpr ⟨hks, hkb⟩
  have hdensity : ∀ Y : Set Nat, Y.Infinite →
      ∃ s : Finset Nat, s ∈ F ∧ ProperPrefixSet s Y := by
    intro Y hY
    obtain ⟨x, hx⟩ := InfiniteSetEnumeration Y hY
    obtain ⟨s, hs, hsx⟩ := hdecide x
    obtain ⟨t, htF, ht⟩ := DecidingFrontMinimal hs
    have hsY : ProperPrefixSet s Y := by
      rcases hsx with ⟨a, ha, hsa⟩
      refine ⟨a, ?_, ?_⟩
      rw [← hx]
      exact ha
      simpa [hx] using hsa
    exact ⟨t, htF, hprefix_initial ht hsY⟩
  have hbase : F = {∅} ∨ FrontBase F = Set.univ := by
    by_cases hc : ∀ x y : IncSeq, h x = h y
    · have hempty : DecidingPrefix h ∅ := by
        intro x y hx hy
        exact hc x y
      have hemptyF : (∅ : Finset Nat) ∈ F := by
        refine ⟨hempty, ?_⟩
        intro t ht htd
        rcases ht.1 with hteq | ⟨n, hn, htn⟩
        · exact ht.2 hteq
        · simp at hn
      left
      ext s
      constructor
      · intro hs
        by_contra hsne
        have hsnonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hsne
        let a := s.min' hsnonempty
        have ha : a ∈ s := Finset.min'_mem s hsnonempty
        have hproper : ProperInitialSegment (∅ : Finset Nat) s := by
          refine ⟨Or.inr ⟨a, ha, ?_⟩, ?_⟩
          · symm
            apply Finset.filter_eq_empty_iff.mpr
            intro k hk hka
            exact (Nat.not_lt_of_ge (Finset.min'_le s k hk)) hka
          · exact fun heq => hsne heq.symm
        exact hs.2 ∅ hproper hempty
      · intro hs
        have hs' : s = ∅ := by simpa using hs
        simpa [hs'] using hemptyF
    · have hempty_prefix : ∀ x : IncSeq,
          ProperPrefixSet (∅ : Finset Nat) (Set.range (x : Nat → Nat)) := by
        intro x
        refine ⟨x 0, ⟨0, rfl⟩, ?_⟩
        intro k
        constructor
        · intro hk
          simp at hk
        · rintro ⟨⟨i, rfl⟩, hi⟩
          exact False.elim ((Nat.not_lt_of_ge (x.monotone (Nat.zero_le i))) hi)
      have hempty_not : ¬ DecidingPrefix h ∅ := by
        intro hempty
        apply hc
        intro x y
        exact hempty x y (hempty_prefix x) (hempty_prefix y)
      right
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      · intro n hn
        let Y : Set Nat := {m | n ≤ m}
        have hY : Y.Infinite := by
          apply Set.Infinite.mono (s := Set.range (fun k : Nat => n + k)) (t := Y)
          · intro k hk
            rcases hk with ⟨r, rfl⟩
            exact Nat.le_add_right n r
          · apply Set.infinite_range_of_injective
            intro a b hab
            exact Nat.add_left_cancel hab
        obtain ⟨s, hsF, hsY⟩ := hdensity Y hY
        have hsne : s ≠ ∅ := by
          intro hs0
          apply hempty_not
          rw [← hs0]
          exact hsF.1
        obtain ⟨k, hks⟩ := Finset.nonempty_iff_ne_empty.mpr hsne
        rcases hsY with ⟨a, ha, hsa⟩
        have hka := (hsa k).mp hks
        have hna : n < a := lt_of_le_of_lt hka.1 hka.2
        exact ⟨s, hsF, (hsa n).mpr ⟨by exact Nat.le_refl _, hna⟩⟩
  refine ⟨Set.infinite_univ, hbase, ?_, ?_⟩
  · intro s t hs ht hst
    by_contra hne
    exact ht.2 s ⟨hst, hne⟩ hs.1
  · intro Y hYsub hY
    exact hdensity Y hY
