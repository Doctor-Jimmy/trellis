import Tablet.BadSuperSequence
import Tablet.BaseShift
import Tablet.FrontPrefixExists
import Tablet.PerfectSuperSequence
import Tablet.InfiniteSetEnumeration

-- [TABLET NODE: NoBadPerfectSuper]
theorem NoBadPerfectSuper {Q : Type} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat} (f : SuperSequence F X Q) :
    PerfectSuperSequence r f → BadSuperSequence r f → False := by
-- BODY
  intro hP hB
  obtain ⟨x, hx⟩ := InfiniteSetEnumeration X f.front.infinite_base
  have hxX : Set.range (x : Nat → Nat) ⊆ X := by
    rw [hx]
  obtain ⟨s, hs⟩ := FrontPrefixExists F X f.front x hxX
  let bx : BaseIncSeq X := ⟨x, hxX⟩
  obtain ⟨t, ht⟩ := FrontPrefixExists F X f.front
    (BaseShift X bx).1 (BaseShift X bx).2
  have hshift : FiniteShift s t := by
    refine ⟨x, hs.2, ?_⟩
    simpa [bx, BaseShift] using ht.2
  exact (hB s t hs.1 ht.1 hshift) (hP s t hs.1 ht.1 hshift)
