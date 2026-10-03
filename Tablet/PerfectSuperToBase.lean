import Tablet.BaseLocallyConstant
import Tablet.BasePerfect
import Tablet.BaseShift
import Tablet.FiniteShift
import Tablet.FrontPrefix
import Tablet.FrontPrefixExists
import Tablet.ProperPrefixSet
import Tablet.PerfectSuperSequence
import Tablet.ShiftMap
import Tablet.SuperSequenceExtension

-- [TABLET NODE: PerfectSuperToBase]
theorem PerfectSuperToBase {Q : Type} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat} (f : SuperSequence F X Q) :
    PerfectSuperSequence r f →
      ∃ h : BaseMultiSequence X Q,
        BaseLocallyConstant h ∧
          (∀ x : BaseIncSeq X, ∃ s : Finset Nat, ∃ hs : FrontPrefix F s x.1,
            h x = f.value ⟨s, hs.1⟩) ∧
          BasePerfect r h := by
-- BODY
  intro hf
  obtain ⟨h, hlc, hext⟩ := SuperSequenceExtension F X f.front f
  refine ⟨h, hlc, hext, ?_⟩
  intro x
  obtain ⟨s₀, hs₀⟩ := FrontPrefixExists F X f.front x.1 x.2
  obtain ⟨t₀, ht₀⟩ :=
    FrontPrefixExists F X f.front (BaseShift X x).1 (BaseShift X x).2
  obtain ⟨s, hs, hxs⟩ := hext x
  obtain ⟨t, ht, hxt⟩ := hext (BaseShift X x)
  have hss : s = s₀ := FrontPrefixUnique F X f.front x.1 hs hs₀
  have htt : t = t₀ :=
    FrontPrefixUnique F X f.front (BaseShift X x).1 ht ht₀
  have hxs' : h x = f.value ⟨s₀, hs₀.1⟩ := by
    simpa [hss] using hxs
  have hxt' : h (BaseShift X x) = f.value ⟨t₀, ht₀.1⟩ := by
    simpa [htt] using hxt
  have hshift : ProperPrefixSet t₀ (Set.range (ShiftMap x.1 : Nat → Nat)) := by
    exact ht₀.2
  have hfinite : FiniteShift s₀ t₀ := by
    exact ⟨x.1, hs₀.2, hshift⟩
  have hperf := hf s₀ t₀ hs₀.1 ht₀.1 hfinite
  rw [hxs', hxt']
  exact hperf
