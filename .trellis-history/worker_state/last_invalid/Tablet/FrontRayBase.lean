import Tablet.Front
import Tablet.FrontNontrivialBase
import Tablet.FrontRayDense
import Tablet.FrontRayPrefixFree
import Tablet.Ray
import Tablet.TailSet

-- [TABLET NODE: FrontRayBase]
theorem FrontRayBase (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (htriv : F ≠ {∅}) (n : Nat) (hn : n ∈ X)
    (hRayTriv : Ray F n ≠ {∅}) :
    FrontBase (Ray F n) = TailSet X n := by
-- BODY
  classical
  have hnonempty := (FrontNontrivialBase F X hF htriv).1
  have hbase := (FrontNontrivialBase F X hF htriv).2
  apply Set.Subset.antisymm
  · intro k hk
    rcases hk with ⟨s, hs, hks⟩
    have hkX : k ∈ FrontBase F :=
      ⟨insert n s, hs.2, Finset.mem_insert_of_mem hks⟩
    exact ⟨hbase ▸ hkX, hs.1 k hks⟩
  · intro k hk
    have htail : (TailSet X k).Infinite := by
      apply Set.Infinite.mono (s := X \ Set.Iic k) (t := TailSet X k)
      · intro m hm
        exact ⟨hm.1, Nat.lt_of_not_ge hm.2⟩
      · exact hF.infinite_base.sdiff (Set.finite_Iic k)
    let Y := insert k (TailSet X k)
    have hYinf : Y.Infinite := by
      apply Set.Infinite.mono (s := TailSet X k) (t := Y)
      intro m hm
      exact Set.mem_insert_iff.mpr (Or.inr hm)
      exact htail
    have hYsub : Y ⊆ TailSet X n := by
      intro m hm
      rcases hm with rfl | hm
      · exact hk
      · exact ⟨hm.1, lt_trans hk.2 hm.2⟩
    obtain ⟨s, hs, hsP⟩ := FrontRayDense F X hF htriv n hn Y hYsub hYinf
    have hsne : s.Nonempty := by
      by_contra hsne
      have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
      have hemptyR : (∅ : Finset Nat) ∈ Ray F n := by simpa [hs0] using hs
      apply hRayTriv
      ext t
      constructor
      · intro ht
        have hinit : InitialSegment (∅ : Finset Nat) t := by
          rcases t.eq_empty_or_nonempty with ht0 | htpos
          · exact Or.inl ht0.symm
          · right
            let m := t.min' htpos
            refine ⟨m, Finset.min'_mem t htpos, ?_⟩
            ext j
            simp only [Finset.mem_filter]
            constructor
            · intro hj
              simp at hj
            · intro hj
              exact False.elim ((Nat.not_lt_of_ge (Finset.min'_le t j hj.1)) hj.2)
        have hst : (∅ : Finset Nat) = t :=
          FrontRayPrefixFree F X hF n (s := (∅ : Finset Nat)) (t := t)
            hemptyR ht hinit
        simpa [hst]
      · intro ht
        have ht0 : t = ∅ := by simpa using ht
        simpa [ht0] using hemptyR
    rcases hsP with ⟨m, hm, hsm⟩
    obtain ⟨q, hqs⟩ := hsne
    have hqY := (hsm q).mp hqs
    have hqk : k ≤ q := by
      change q ∈ insert k (TailSet X k) ∧ q < m at hqY
      have hqY' : q = k ∨ q ∈ TailSet X k := by
        simpa only [Set.mem_insert_iff] using hqY.1
      rcases hqY' with hqk | hqtail
      · exact hqk ▸ Nat.le_refl k
      · exact Nat.le_of_lt hqtail.2
    have hkm : k < m := lt_of_le_of_lt hqk hqY.2
    have hks : k ∈ s := (hsm k).mpr ⟨Set.mem_insert k (TailSet X k), hkm⟩
    exact ⟨s, hs, hks⟩
