import Tablet.FrontPrefix

-- [TABLET NODE: FrontPrefixUnique]
theorem FrontPrefixUnique (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (x : IncSeq) {s t : Finset Nat}
    (hs : FrontPrefix F s x) (ht : FrontPrefix F t x) : s = t := by
-- BODY
  rcases hs with ⟨hsF, hsP⟩
  rcases ht with ⟨htF, htP⟩
  rcases hsP with ⟨a, haR, ha⟩
  rcases htP with ⟨b, hbR, hb⟩
  by_cases hab : a = b
  · have hst : s = t := by
      subst b
      ext k
      exact (ha k).trans (hb k).symm
    exact hst
  · by_cases hlt : a < b
    · have haT : a ∈ t := (hb a).2 ⟨haR, hlt⟩
      have hst : s = t.filter (fun k => k < a) := by
        ext k
        rw [ha k, Finset.mem_filter, hb k]
        constructor
        · rintro ⟨hkR, hkA⟩
          exact ⟨⟨hkR, Nat.lt_trans hkA hlt⟩, hkA⟩
        · rintro ⟨⟨hkR, hkB⟩, hkA⟩
          exact ⟨hkR, hkA⟩
      apply hF.prefix_free hsF htF
      exact Or.inr ⟨a, haT, hst⟩
    · have hba : b < a := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hab)
      have hbS : b ∈ s := (ha b).2 ⟨hbR, hba⟩
      have hts : t = s.filter (fun k => k < b) := by
        ext k
        rw [hb k, Finset.mem_filter, ha k]
        constructor
        · rintro ⟨hkR, hkB⟩
          exact ⟨⟨hkR, Nat.lt_trans hkB hba⟩, hkB⟩
        · rintro ⟨⟨hkR, hkA⟩, hkB⟩
          exact ⟨hkR, hkB⟩
      have hts' : InitialSegment t s := Or.inr ⟨b, hbS, hts⟩
      exact (hF.prefix_free htF hsF hts').symm
