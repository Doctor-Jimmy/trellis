import Tablet.NashWilliams
import Tablet.SuperSequence

-- [TABLET NODE: SuperNW]
theorem SuperNW (E : Type) [Fintype E] (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (f : SuperSequence F X E) :
    ∃ F' : Set (Finset Nat), ∃ Y : Set Nat,
      ∃ hF' : Front F' Y, ∃ hsub : F' ⊆ F,
        ∃ c : E, ∀ s : F', f.value ⟨s.1, hsub s.2⟩ = c := by
-- BODY
  classical
  let P : ∀ E : Type, [Fintype E] → Prop := fun E _ =>
    ∀ (F : Set (Finset Nat)) (X : Set Nat),
      (hF : Front F X) → (f : SuperSequence F X E) →
      ∃ F' : Set (Finset Nat), ∃ Y : Set Nat,
        ∃ hF' : Front F' Y, ∃ hsub : F' ⊆ F,
          ∃ c : E, ∀ s : F',
            (f.value ⟨s.1, hsub s.2⟩ = c)
  have hP : @P E _ := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ E
    · intro α β _ e ih F X hF f
      obtain ⟨F', Y, hF', hsub, c, hc⟩ :=
        ih F X hF
          { front := f.front
            value := fun s => e.symm (f.value s) }
      refine ⟨F', Y, hF', hsub, e c, ?_⟩
      intro s
      have h := congrArg e (hc s)
      simpa using h
    · intro F X hF f
      obtain ⟨s, hs, _⟩ := hF.dense X (by rfl) hF.infinite_base
      exact (f.value ⟨s, hs⟩).elim
    · intro α _ ih F X hF f
      let S : Set (Finset Nat) :=
        {s | ∃ hs : s ∈ F, f.value ⟨s, hs⟩ = none}
      have hS : S ⊆ F := by
        intro s hs
        exact hs.choose
      obtain ⟨F0, Y0, hF0, hF0sub, hcase⟩ :=
        NashWilliams F X hF S hS
      rcases hcase with hselected | hcomplement
      · refine ⟨F0, Y0, hF0, hF0sub, none, ?_⟩
        intro s
        obtain ⟨hsF, hsnone⟩ := hselected s.2
        simpa using hsnone
      · have hne : ∀ s : F0,
            f.value ⟨s.1, hF0sub s.2⟩ ≠ none := by
          intro s hsnone
          have hbad : s.1 ∈ (∅ : Set (Finset Nat)) := by
            rw [← hcomplement]
            exact ⟨s.2, ⟨hF0sub s.2, hsnone⟩⟩
          simpa using hbad
        let gval : F0 → α := fun s =>
          Option.get (f.value ⟨s.1, hF0sub s.2⟩)
            ((Option.ne_none_iff_isSome).1 (hne s))
        let g : SuperSequence F0 Y0 α :=
          { front := hF0
            value := gval }
        obtain ⟨F1, Y1, hF1, hF1sub, c, hc⟩ :=
          ih F0 Y0 hF0 g
        refine ⟨F1, Y1, hF1, hF1sub.trans hF0sub, some c, ?_⟩
        intro s
        have hval : f.value ⟨s.1, hF0sub (hF1sub s.2)⟩ =
            some (g.value ⟨s.1, hF1sub s.2⟩) := by
          symm
          exact Option.coe_get _
        rw [hc s] at hval
        simpa using hval
  exact hP F X hF f
