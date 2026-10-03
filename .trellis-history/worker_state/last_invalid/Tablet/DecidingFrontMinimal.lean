import Tablet.DecidingFrontInitialTrans
import Tablet.DecidingFrontSet

universe u

-- [TABLET NODE: DecidingFrontMinimal]
theorem DecidingFrontMinimal {E : Type u} {h : MultiSequence E} {s : Finset Nat}
    (hs : DecidingPrefix h s) :
    ∃ t, t ∈ DecidingFrontSet h ∧ InitialSegment t s := by
-- BODY
  classical
  let P : Nat → Prop := fun n =>
    ∃ t : Finset Nat, InitialSegment t s ∧ DecidingPrefix h t ∧ t.card = n
  have hP : ∃ n, P n := ⟨s.card, s, Or.inl rfl, hs, rfl⟩
  obtain ⟨t, htInit, htDec, htcard⟩ := Nat.find_spec hP
  refine ⟨t, ?_, htInit⟩
  change DecidingPrefix h t ∧ ∀ q, ProperInitialSegment q t → ¬ DecidingPrefix h q
  refine ⟨htDec, ?_⟩
  intro q hq hqDec
  have hqsub : q ⊆ t := by
    rcases hq.1 with rfl | ⟨a, ha, hqa⟩
    · intro z hz
      exact hz
    · rw [hqa]
      exact Finset.filter_subset _ _
  have hqss : q ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨hqsub, hq.2⟩
  have hlt : q.card < t.card := Finset.card_lt_card hqss
  have hqP : P q.card :=
    ⟨q, DecidingFrontInitialTrans hq.1 htInit, hqDec, rfl⟩
  have hnle : Nat.find hP ≤ q.card := Nat.find_min' hP hqP
  rw [← htcard] at hnle
  exact (Nat.not_lt_of_ge hnle) hlt
