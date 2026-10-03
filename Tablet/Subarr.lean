import Tablet.BadMultiRestrict
import Tablet.BadMultiToSuper
import Tablet.BadSuperRestrict
import Tablet.BaseBqoRestriction
import Tablet.DecidingFront
import Tablet.DecidingValue
import Tablet.NoBadPerfectSuper
import Tablet.PerfectBaseToSuper
import Tablet.PerfectSuperToMulti
import Tablet.RestrictionLocallyConstant
import Tablet.ShiftDichotomy
import Tablet.SuperSequenceExtension

-- [TABLET NODE: Subarr]
theorem Subarr {Q : Type} (r : Q → Q → Prop) [IsPreorder Q r] :
    Bqo r ↔
      (∀ (X : Set Nat), X.Infinite →
        ∀ h : BaseMultiSequence X Q, BaseLocallyConstant h →
          ∃ z : BaseIncSeq X,
            PerfectMultiSequence r (BaseRestrict h z)) ∧
      (∀ (F : Set (Finset Nat)) (X : Set Nat)
          (f : SuperSequence F X Q),
        ∃ F' : Set (Finset Nat), ∃ Y : Set Nat,
          ∃ hF' : Front F' Y, ∃ hsub : F' ⊆ F,
            PerfectSuperSequence r (SuperSequenceRestrict f F' Y hF' hsub)) := by
-- BODY
  constructor
  · intro hb
    constructor
    · intro X hX h hlc
      exact BaseBqoRestriction r hb X hX h hlc
    · intro F X f
      obtain ⟨h, hlc, hext⟩ := SuperSequenceExtension F X f.front f
      obtain ⟨z, hp⟩ := BaseBqoRestriction r hb X f.front.infinite_base h hlc
      have hext' : ∀ (x : BaseIncSeq X) (s : Finset Nat)
          (hs : FrontPrefix F s x.1), h x = f.value ⟨s, hs.1⟩ := by
        intro x s hs
        obtain ⟨t, ht, hval⟩ := hext x
        have hst : s = t := FrontPrefixUnique F X f.front x.1 hs ht
        simpa [hst] using hval
      obtain ⟨F', hF', hsub, hp'⟩ := PerfectBaseToSuper r f h hext' z hp
      exact ⟨F', Set.range (z.1 : Nat → Nat), hF', hsub, hp'⟩
  · rintro ⟨hbase, hsuper⟩ h hlc hbad
    obtain ⟨v, hv⟩ := DecidingValue h hlc
    let f : SuperSequence (DecidingFrontSet h) Set.univ Q :=
      ⟨DecidingFront h hlc, v⟩
    have hf : ∀ (s : DecidingFrontSet h) (x : IncSeq),
        ProperPrefixSet s.1 (Set.range (x : Nat → Nat)) → f.value s = h x := by
      intro s x hs
      exact hv s x hs
    have hbad' : BadSuperSequence r f :=
      BadMultiToSuper r h f hf hbad
    obtain ⟨F', Y, hF', hsub, hp⟩ := hsuper (DecidingFrontSet h) Set.univ f
    have hbad'' :
        BadSuperSequence r (SuperSequenceRestrict f F' Y hF' hsub) :=
      BadSuperRestrict r f F' Y hF' hsub hbad'
    exact NoBadPerfectSuper r (SuperSequenceRestrict f F' Y hF' hsub) hp hbad''
