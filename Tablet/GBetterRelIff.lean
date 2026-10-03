import Tablet.BetterRel
import Tablet.GBetterRel
import Tablet.Bqo
import Tablet.MainProp
import Tablet.IncSeqId
import Tablet.IncSeq
import Tablet.PrefixAgree
import Tablet.LocallyConstant
import Tablet.ContinuousRelHom
import Tablet.Front
import Tablet.ProperPrefixSet
import Tablet.DecidingFront
import Tablet.DecidingValue
import Tablet.NashWilliams
import Tablet.InfiniteSetEnumeration
import Tablet.RestrictionLocallyConstant
import Tablet.MultiSequenceRestrict
import Tablet.IncSeqComp
import Tablet.RightComp

-- [TABLET NODE: GBetterRelIff]
theorem GBetterRelIff (g : IncSeq) (hg : g ≠ IncSeqId) :
    (∀ {A : Type} (r : A → A → Prop),
      GBetterRel g r ↔ BetterRel r) ∧
    (∀ {Q : Type} (r : Q → Q → Prop), IsPreorder Q r →
      (GBetterRel g r ↔ Bqo r)) := by
-- BODY
  classical
  have hm : ContMorEq (RightComp g) ShiftMap := MainProp g hg
  obtain ⟨hk⟩ := hm.1
  obtain ⟨hl⟩ := hm.2
  have transport : ∀ {A : Type} {r : A → A → Prop}
      (s t : IncSeq → IncSeq) (C : ContinuousHom s t)
      (H : ContinuousRelHom t (fun a b => ¬ r a b)),
      Nonempty (ContinuousRelHom s (fun a b => ¬ r a b)) := by
    intro A r s t C H
    refine ⟨{ toFun := fun x => H.toFun (C.toFun x),
              locallyConstant := ?_,
              hom := ?_ }⟩
    · intro x
      obtain ⟨n, hn⟩ := H.locallyConstant (C.toFun x)
      obtain ⟨k, hk⟩ := C.continuous x n
      refine ⟨k, ?_⟩
      intro y hy
      apply hn
      exact hk y hy
    · intro x
      have hh := H.hom (C.toFun x)
      rw [C.commutes x]
      exact hh
  have hfirst : ∀ {A : Type} (r : A → A → Prop),
      (¬ Nonempty (ContinuousRelHom (RightComp g)
        (fun a b => ¬ r a b))) →
      ∀ (phi : IncSeq → A), LocallyConstant phi →
        ∃ f : IncSeq, ∃ H : ContinuousRelHom (RightComp g) r,
          ∀ x, H.toFun x = phi (IncSeqComp f x) := by
    intro A r hno phi hphi
    let c : IncSeq → Bool := fun x =>
      if r (phi x) (phi (RightComp g x)) then true else false
    have hc : LocallyConstant c := by
      intro x
      obtain ⟨n, hn⟩ := hphi x
      obtain ⟨m, hm⟩ := hphi (RightComp g x)
      refine ⟨max n (g m), ?_⟩
      intro y hy
      have hxy : phi y = phi x := hn y (fun i hi =>
        hy i (lt_of_lt_of_le hi (Nat.le_max_left _ _)))
      have hcomp : phi (RightComp g y) = phi (RightComp g x) := by
        apply hm
        intro i hi
        simpa [RightComp, IncSeqComp] using
          hy (g i) (lt_of_lt_of_le (g.lt_iff_lt.mpr hi)
            (Nat.le_max_right _ _))
      simp [c, hxy, hcomp]
    obtain ⟨v, hv⟩ := DecidingValue c hc
    let F : Set (Finset Nat) := DecidingFrontSet c
    have hF : Front F Set.univ := by
      simpa [F] using DecidingFront c hc
    let S : Set (Finset Nat) :=
      {s | ∃ hs : s ∈ F, v ⟨s, hs⟩ = true}
    have hS : S ⊆ F := by
      intro s hs
      exact hs.1
    obtain ⟨F', Y, hF', hsub, hhom⟩ := NashWilliams F Set.univ hF S hS
    obtain ⟨z, hz⟩ := InfiniteSetEnumeration Y hF'.infinite_base
    have hrange : ∀ x : IncSeq, (Set.range (IncSeqComp z x)).Infinite := by
      intro x
      apply Set.infinite_range_of_injective
      intro i j hij
      apply z.injective
      simpa [IncSeqComp] using hij
    have hsubrange : ∀ x : IncSeq, Set.range (IncSeqComp z x) ⊆ Y := by
      intro x y hy
      rcases hy with ⟨i, rfl⟩
      rw [← hz]
      exact ⟨x i, by simp [IncSeqComp]⟩
    have hcolor : (∀ x : IncSeq, c (IncSeqComp z x) = true) ∨
        (∀ x : IncSeq, c (IncSeqComp z x) = false) := by
      rcases hhom with hhom | hhom
      · left
        intro x
        obtain ⟨s, hsF, hsP⟩ := hF'.dense (Set.range (IncSeqComp z x))
          (hsubrange x) (hrange x)
        obtain ⟨hsF0, hvtrue⟩ := hhom hsF
        have hvalue := hv ⟨s, hsF0⟩ (IncSeqComp z x) hsP
        exact hvalue.symm ▸ hvtrue
      · right
        intro x
        obtain ⟨s, hsF, hsP⟩ := hF'.dense (Set.range (IncSeqComp z x))
          (hsubrange x) (hrange x)
        have hnotS : s ∉ S := by
          intro hs
          have : s ∈ F' ∩ S := ⟨hsF, hs⟩
          simpa [hhom] using this
        by_cases hct : c (IncSeqComp z x) = true
        · have hvtrue : v ⟨s, hsub hsF⟩ = true := by
            simpa [hct] using
              (hv ⟨s, hsub hsF⟩ (IncSeqComp z x) hsP)
          exact False.elim (hnotS ⟨hsub hsF, hvtrue⟩)
        · exact Bool.eq_false_of_not_eq_true hct
    rcases hcolor with hpos | hneg
    · refine ⟨z, { toFun := MultiSequenceRestrict phi z,
                    locallyConstant := RestrictionLocallyConstant phi z hphi,
                    hom := ?_ }, ?_⟩
      · intro x
        change r (phi (IncSeqComp z x))
          (phi (RightComp g (IncSeqComp z x)))
        have hx := hpos x
        simp only [c] at hx
        split at hx
        · assumption
        · contradiction
      · intro x
        rfl
    · apply False.elim
      apply hno
      refine ⟨{ toFun := MultiSequenceRestrict phi z,
                locallyConstant := RestrictionLocallyConstant phi z hphi,
                hom := ?_ }⟩
      intro x
      change ¬ r (phi (IncSeqComp z x))
        (phi (RightComp g (IncSeqComp z x)))
      have hx := hneg x
      simp only [c] at hx
      split at hx
      · contradiction
      · assumption
  have hrel : ∀ {A : Type} (r : A → A → Prop),
      GBetterRel g r ↔ BetterRel r := by
    intro A r
    constructor
    · intro hg
      unfold BetterRel
      intro hs
      apply hg.2
      rcases hs with ⟨H⟩
      exact transport (RightComp g) ShiftMap hk H
    · intro hb
      unfold GBetterRel
      refine ⟨?_, ?_⟩
      · apply hfirst r
        intro hg
        apply hb
        rcases hg with ⟨H⟩
        exact transport ShiftMap (RightComp g) hl H
      · intro hg
        apply hb
        rcases hg with ⟨H⟩
        exact transport ShiftMap (RightComp g) hl H
  refine ⟨hrel, ?_⟩
  intro Q r hpre
  constructor
  · intro hg
    have hb : BetterRel r := (hrel r).mp hg
    unfold Bqo
    intro h hlc hbad
    apply hb
    refine ⟨{ toFun := h, locallyConstant := hlc, hom := ?_ }⟩
    intro x
    exact hbad x
  · intro hbqo
    apply (hrel r).mpr
    unfold BetterRel
    intro hs
    rcases hs with ⟨H⟩
    have hbad : BadMultiSequence r H.toFun := by
      intro x
      exact H.hom x
    exact (hbqo H.toFun H.locallyConstant) hbad
