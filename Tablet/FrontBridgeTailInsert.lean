import Tablet.FrontBridgeTail

-- [TABLET NODE: FrontBridgeTailInsert]
theorem FrontBridgeTailInsert (u : Finset Nat) (hu : u.Nonempty) (q : Nat)
    (hqu : ∀ j ∈ u, j < q) :
    FrontBridgeTail (insert q u) = insert q (FrontBridgeTail u) := by
-- BODY
  classical
  apply Finset.ext
  intro k
  rw [FrontBridgeTail, FrontBridgeTail]
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hk, ⟨n, hn, hnk⟩⟩
    rcases hk with hkq | hk
    · exact Or.inl hkq
    · right
      refine ⟨hk, ?_⟩
      rcases hn with hnq | hn
      · subst n
        exact False.elim ((Nat.lt_irrefl q) (hnk.trans (hqu k hk)))
      · exact ⟨n, hn, hnk⟩
  · intro hk
    rcases hk with hkq | ⟨hk, ⟨n, hn, hnk⟩⟩
    · subst k
      rcases hu with ⟨j, hj⟩
      exact ⟨Or.inl rfl, ⟨j, Or.inr hj, hqu j hj⟩⟩
    · exact ⟨Or.inr hk, ⟨n, Or.inr hn, hnk⟩⟩
