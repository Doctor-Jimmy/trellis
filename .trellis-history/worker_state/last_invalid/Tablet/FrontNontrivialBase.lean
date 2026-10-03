import Tablet.Front

-- [TABLET NODE: FrontNontrivialBase]
theorem FrontNontrivialBase (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (htriv : F ≠ {∅}) :
    (∀ s ∈ F, s.Nonempty) ∧ FrontBase F = X := by
-- BODY
  classical
  have hnonempty : ∀ s ∈ F, s.Nonempty := by
    intro s hs
    by_contra hsne
    have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
    have hempty : (∅ : Finset Nat) ∈ F := by simpa [hs0] using hs
    have hall : ∀ t ∈ F, t = ∅ := by
      intro t ht
      by_contra htne
      have htpos : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr htne
      let m := t.min' htpos
      have hm : m ∈ t := Finset.min'_mem t htpos
      have hinit : InitialSegment (∅ : Finset Nat) t := by
        right
        refine ⟨m, hm, ?_⟩
        ext k
        simp only [Finset.mem_filter]
        constructor
        · intro hk
          simp at hk
        · intro hk
          exact False.elim ((Nat.not_lt_of_ge (Finset.min'_le t k hk.1)) hk.2)
      exact htne (hF.prefix_free (s := (∅ : Finset Nat)) (t := t)
        hempty ht hinit).symm
    apply htriv
    ext t
    constructor
    · intro ht
      have ht0 := hall t ht
      simpa [ht0]
    · intro ht
      have ht0 : t = ∅ := by simpa using ht
      simpa [ht0] using hempty
  have hbase : FrontBase F = X := by
    rcases hF.base_condition with htrivF | hbase
    · exact False.elim (htriv htrivF)
    · exact hbase
  exact ⟨hnonempty, hbase⟩
