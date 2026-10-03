import Tablet.FrontNontrivialBase
import Tablet.Ray
import Tablet.TailSet

-- [TABLET NODE: FrontRayDense]
theorem FrontRayDense (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (htriv : F ≠ {∅}) (n : Nat) (hn : n ∈ X) :
    ∀ Y : Set Nat, Y ⊆ TailSet X n → Y.Infinite →
      ∃ s : Finset Nat, s ∈ Ray F n ∧ ProperPrefixSet s Y := by
-- BODY
  classical
  have hnonempty := (FrontNontrivialBase F X hF htriv).1
  intro Y hYsub hYinf
  have hinsert_inf : (insert n Y : Set Nat).Infinite := by
    apply Set.Infinite.mono (s := Y) (t := insert n Y)
    intro k hk
    exact Set.mem_insert_iff.mpr (Or.inr hk)
    exact hYinf
  have hinsert_sub : (insert n Y : Set Nat) ⊆ X := by
    intro k hk
    rcases hk with rfl | hkY
    · exact hn
    · exact (hYsub hkY).1
  obtain ⟨u, huF, huP⟩ := hF.dense (insert n Y) hinsert_sub hinsert_inf
  rcases huP with ⟨m, hm, hum⟩
  have hm' : m = n ∨ m ∈ Y := by
    simpa only [Set.mem_insert_iff] using hm
  have hmY : m ∈ Y := by
    rcases hm' with hmn | hmY
    · obtain ⟨k, hku⟩ := hnonempty u huF
      have hku' := (hum k).mp hku
      rcases hku'.1 with hkn | hkY
      · have hnn : n < n := by simpa [hkn, hmn] using hku'.2
        exact False.elim ((Nat.lt_irrefl n) hnn)
      · have hkn' : k < n := by simpa [hmn] using hku'.2
        exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt (hYsub hkY).2)) hkn')
    · exact hmY
  have hnm : n < m := (hYsub hmY).2
  have hnu : n ∈ u := by
    exact (hum n).mpr ⟨Set.mem_insert n Y, hnm⟩
  let s := u.erase n
  have hsu : insert n s = u := by
    exact Finset.insert_erase hnu
  have hsray : s ∈ Ray F n := by
    refine ⟨?_, ?_⟩
    · intro k hk
      have hku : k ∈ u := Finset.mem_of_mem_erase hk
      have hks : k ≠ n := by
        intro hkn
        subst k
        exact (Finset.mem_erase.mp hk).1 rfl
      have hku' := (hum k).mp hku
      rcases hku'.1 with rfl | hkY
      · exact False.elim (hks rfl)
      · exact (hYsub hkY).2
    · exact hsu ▸ huF
  have hsP : ProperPrefixSet s Y := by
    refine ⟨m, hmY, ?_⟩
    intro k
    constructor
    · intro hk
      have hku : k ∈ u := Finset.mem_of_mem_erase hk
      have hku' := (hum k).mp hku
      rcases hku'.1 with rfl | hkY
      · exact False.elim ((Finset.mem_erase.mp hk).1 rfl)
      · exact ⟨hkY, hku'.2⟩
    · rintro ⟨hkY, hkm⟩
      have hku : k ∈ u :=
        (hum k).mpr ⟨Set.mem_insert_iff.mpr (Or.inr hkY), hkm⟩
      have hkn : k ≠ n := by
        intro hkn
        subst k
        exact Nat.not_lt_of_ge (Nat.le_refl n) (hYsub hkY).2
      exact Finset.mem_erase.mpr ⟨hkn, hku⟩
  exact ⟨s, hsray, hsP⟩
