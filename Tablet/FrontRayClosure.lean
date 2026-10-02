import Tablet.Front
import Tablet.FrontNontrivialBase
import Tablet.FrontRayBase
import Tablet.FrontRayDense
import Tablet.FrontRayPrefixFree
import Tablet.Ray
import Tablet.TailSet

-- [TABLET NODE: FrontRayClosure]
theorem FrontRayClosure (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (htriv : F ≠ {∅}) :
    (∀ n ∈ X, Front (Ray F n) (TailSet X n)) ∧
      F = {s | ∃ n ∈ X, ∃ t ∈ Ray F n, s = insert n t} := by
-- BODY
  classical
  rcases FrontNontrivialBase F X hF htriv with ⟨hnonempty, hbase⟩
  constructor
  · intro n hn
    have htail : (TailSet X n).Infinite := by
      apply Set.Infinite.mono (s := X \ Set.Iic n) (t := TailSet X n)
      · intro k hk
        exact ⟨hk.1, Nat.lt_of_not_ge hk.2⟩
      · exact hF.infinite_base.sdiff (Set.finite_Iic n)
    refine ⟨htail, ?_, ?_, ?_⟩
    · by_cases hRayTriv : Ray F n = {∅}
      · exact Or.inl hRayTriv
      · exact Or.inr (FrontRayBase F X hF htriv n hn hRayTriv)
    · intro s t hs ht hst
      exact FrontRayPrefixFree F X hF n hs ht hst
    · intro Y hYsub hYinf
      exact FrontRayDense F X hF htriv n hn Y hYsub hYinf
  · apply Set.ext
    intro u
    constructor
    · intro hu
      have hu_nonempty := hnonempty u hu
      let n := u.min' hu_nonempty
      have hnmem : n ∈ u := Finset.min'_mem u hu_nonempty
      have hnX : n ∈ X := by
        exact hbase ▸ (show n ∈ FrontBase F from ⟨u, hu, hnmem⟩)
      let t := u.erase n
      have htu : insert n t = u := Finset.insert_erase hnmem
      have htRay : t ∈ Ray F n := by
        refine ⟨?_, ?_⟩
        · intro k hk
          have hku : k ∈ u := Finset.mem_of_mem_erase hk
          have hkn : k ≠ n := (Finset.mem_erase.mp hk).1
          exact lt_of_le_of_ne (Finset.min'_le u k hku) (Ne.symm hkn)
        · exact htu ▸ hu
      exact ⟨n, hnX, t, htRay, htu.symm⟩
    · rintro ⟨n, hn, t, ht, rfl⟩
      exact ht.2
