import Tablet.BaseLocallyConstant
import Tablet.FrontPrefixExists
import Tablet.FrontPrefixUnique
import Tablet.SuperSequence

-- [TABLET NODE: SuperSequenceExtension]
theorem SuperSequenceExtension {E : Type} (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (f : SuperSequence F X E) :
    ∃ h : BaseMultiSequence X E,
      BaseLocallyConstant h ∧
      ∀ x : BaseIncSeq X, ∃ s : Finset Nat, ∃ hs : FrontPrefix F s x.1,
        h x = f.value ⟨s, hs.1⟩ := by
-- BODY
  classical
  have hex : ∀ x : BaseIncSeq X, ∃ s : Finset Nat, FrontPrefix F s x.1 := by
    intro x
    exact FrontPrefixExists F X hF x.1 x.2
  choose s hs using hex
  let h : BaseMultiSequence X E := fun x =>
    f.value ⟨s x, (hs x).1⟩
  refine ⟨h, ?_, ?_⟩
  · intro x
    obtain ⟨q, hq, hsq⟩ := (hs x).2
    obtain ⟨j, hj⟩ := hq
    refine ⟨j + 1, ?_⟩
    intro y hy
    have hyj : x.1 j = y.1 j := hy j (Nat.lt_succ_self j)
    have hq_y : y.1 j = q := by
      rw [← hyj, hj]
    have hprefix : FrontPrefix F (s x) y.1 := by
      refine ⟨(hs x).1, ?_⟩
      refine ⟨q, ⟨j, hq_y⟩, ?_⟩
      intro k
      constructor
      · intro hk
        have hkx := (hsq k).mp hk
        obtain ⟨i, hi⟩ := hkx.1
        have hij : i < j := x.1.lt_iff_lt.mp (by
          calc
            x.1 i = k := hi
            _ < q := hkx.2
            _ = x.1 j := hj.symm)
        have hiy : x.1 i = y.1 i := hy i (lt_trans hij (Nat.lt_succ_self j))
        exact ⟨⟨i, hiy.symm.trans hi⟩, hkx.2⟩
      · intro hky
        obtain ⟨i, hi⟩ := hky.1
        have hij : i < j := y.1.lt_iff_lt.mp (by
          calc
            y.1 i = k := hi
            _ < q := hky.2
            _ = y.1 j := hq_y.symm)
        have hiy : x.1 i = y.1 i := hy i (lt_trans hij (Nat.lt_succ_self j))
        apply (hsq k).mpr
        exact ⟨⟨i, hiy.trans hi⟩, hky.2⟩
    have heq : s y = s x :=
      FrontPrefixUnique F X hF y.1 (hs y) hprefix
    dsimp [h]
    apply congrArg f.value
    exact Subtype.ext heq
  · intro x
    exact ⟨s x, hs x, rfl⟩
