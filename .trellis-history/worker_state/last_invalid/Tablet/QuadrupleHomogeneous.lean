import Tablet.CardinalityFrontIsFront
import Tablet.FrontContainsCardinalitySets
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
  have hquad := FrontContainsCardinalitySets 4 F' Y hF'
    (by
      intro t ht
      exact (hFsub ht).1)
    (by omega)
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
