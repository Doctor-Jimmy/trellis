import Tablet.BaseRestrict
import Tablet.BaseIncSeq
import Tablet.Front
import Tablet.FrontPrefix
import Tablet.FrontRestrict
import Tablet.FrontRestriction
import Tablet.FiniteShift
import Tablet.IncSeq
import Tablet.IncSeqComp
import Tablet.InitialSegment
import Tablet.InfiniteSetEnumeration
import Tablet.PerfectMultiSequence
import Tablet.PerfectSuperSequence
import Tablet.ProperPrefixSet
import Tablet.RestrictionShift
import Tablet.ShiftMap
import Tablet.SuperSequence
import Tablet.SuperSequenceExtension
import Tablet.SuperSequenceRestrict

-- [TABLET NODE: PerfectBaseToSuper]
theorem PerfectBaseToSuper {Q : Type} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat} (f : SuperSequence F X Q)
    (h : BaseMultiSequence X Q)
    (hext : ∀ (x : BaseIncSeq X) (s : Finset Nat)
      (hs : FrontPrefix F s x.1), h x = f.value ⟨s, hs.1⟩)
    (z : BaseIncSeq X) (hp : PerfectMultiSequence r (BaseRestrict h z)) :
    ∃ F' : Set (Finset Nat),
      ∃ hF' : Front F' (Set.range (z.1 : Nat → Nat)),
        ∃ hsub : F' ⊆ F,
          PerfectSuperSequence r
            (SuperSequenceRestrict f F' (Set.range (z.1 : Nat → Nat)) hF' hsub) := by
-- BODY
  let Y : Set Nat := Set.range (z.1 : Nat → Nat)
  have hYsub : Y ⊆ X := by
    intro n hn
    exact z.2 hn
  have hYinf : Y.Infinite := by
    dsimp [Y]
    exact Set.infinite_range_of_injective z.1.injective
  let F' : Set (Finset Nat) := FrontRestrict F Y
  have hF' : Front F' Y := by
    exact FrontRestriction F X f.front Y hYsub hYinf
  have hsub : F' ⊆ F := by
    intro s hs
    exact hs.1
  refine ⟨F', ?_, hsub, ?_⟩
  · simpa [Y] using hF'
  · intro s t hs ht hst
    classical
    have empty_initial : ∀ u : Finset Nat, u.Nonempty → InitialSegment ∅ u := by
      intro u hu
      right
      let m := u.min' hu
      refine ⟨m, Finset.min'_mem u hu, ?_⟩
      ext k
      constructor
      · intro hk
        simp at hk
      · intro hk
        have hku : k ∈ u := (Finset.mem_filter.mp hk).1
        have hkm : k < m := (Finset.mem_filter.mp hk).2
        exact (Nat.not_lt_of_ge (Finset.min'_le u k hku) hkm).elim
    have construct : ∀ (s t : Finset Nat), s ∈ F' → t ∈ F' →
        FiniteShift s t →
        ∃ y : IncSeq, Set.range (y : Nat → Nat) ⊆ Y ∧
          ProperPrefixSet s (Set.range (y : Nat → Nat)) ∧
          ProperPrefixSet t (Set.range (ShiftMap y : Nat → Nat)) := by
      intro s t hs ht hst
      rcases hst with ⟨x, hsP, htP⟩
      rcases hsP with ⟨a, haR, ha⟩
      rcases haR with ⟨i, hi⟩
      subst a
      rcases htP with ⟨b, hbR, hb⟩
      rcases hbR with ⟨j, hj⟩
      subst b
      have hs0_iff : s = ∅ ↔ t = ∅ := by
        constructor
        · intro hs0
          by_contra ht0
          have hEq := hF'.prefix_free hs ht (by
            simpa [hs0] using (empty_initial t
              (Finset.nonempty_iff_ne_empty.mpr ht0)))
          exact ht0 (hEq.symm.trans hs0)
        · intro ht0
          by_contra hs0
          have hEq := hF'.prefix_free ht hs (by
            simpa [ht0] using (empty_initial s
              (Finset.nonempty_iff_ne_empty.mpr hs0)))
          exact hs0 (hEq.symm.trans ht0)
      have hshift (n : Nat) : ShiftMap x n = x (n + 1) := by
        rfl
      have ht_idx (n : Nat) : ShiftMap x n ∈ t ↔ n < j := by
        constructor
        · intro hn
          exact (ShiftMap x).lt_iff_lt.mp ((hb (ShiftMap x n)).mp hn).2
        · intro hn
          apply (hb (ShiftMap x n)).mpr
          exact ⟨⟨n, rfl⟩, (ShiftMap x).lt_iff_lt.mpr hn⟩
      have hs_idx (n : Nat) : x n ∈ s ↔ n < i := by
        constructor
        · intro hn
          exact x.lt_iff_lt.mp ((ha (x n)).mp hn).2
        · intro hn
          apply (ha (x n)).mpr
          exact ⟨⟨n, rfl⟩, x.lt_iff_lt.mpr hn⟩
      by_cases hs0 : s = ∅
      · have ht0 : t = ∅ := hs0_iff.mp hs0
        obtain ⟨y, hy⟩ := InfiniteSetEnumeration Y hYinf
        have empty_prefix : ∀ (w : IncSeq),
            ProperPrefixSet ∅ (Set.range (w : Nat → Nat)) := by
          intro w
          refine ⟨w 0, ⟨0, rfl⟩, ?_⟩
          intro k
          constructor
          · intro hk
            simp at hk
          · rintro ⟨⟨n, rfl⟩, hn⟩
            exact (Nat.not_lt_zero n (w.lt_iff_lt.mp hn)).elim
        refine ⟨y, ?_, ?_, ?_⟩
        · intro n hn
          rw [← hy]
          exact hn
        · simpa [hs0] using empty_prefix y
        · simpa [ht0] using empty_prefix (ShiftMap y)
      · have ht0 : t ≠ ∅ := by
          intro ht0
          exact hs0 (hs0_iff.mpr ht0)
        have hi_pos : 0 < i := by
          obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hs0
          obtain ⟨n, hn⟩ := ((ha k).mp hk).1
          have hni : n < i := x.lt_iff_lt.mp (by
            rw [hn]
            exact ((ha k).mp hk).2)
          omega
        have hLpos : 0 < max i (j + 1) := by
          exact lt_of_lt_of_le hi_pos (Nat.le_max_left _ _)
        let L := max i (j + 1)
        let p := x (L - 1)
        have hprefix_mem : ∀ k, k < L → x k ∈ Y := by
          intro k hk
          by_cases hki : k < i
          · exact hs.2 (x k) ((hs_idx k).mpr hki)
          · have hik : i ≤ k := Nat.le_of_not_gt hki
            have hkj : k ≤ j := by
              by_cases hil : i ≤ j + 1
              · have hL' : L = j + 1 := by
                  dsimp [L]
                  exact Nat.max_eq_right hil
                rw [hL'] at hk
                omega
              · have hL' : L = i := by
                  dsimp [L]
                  exact Nat.max_eq_left (Nat.le_of_not_ge hil)
                rw [hL'] at hk
                omega
            have hkone : 1 ≤ k := le_trans (Nat.succ_le_iff.mpr hi_pos) hik
            have hkm : k - 1 < j := by omega
            have htin : ShiftMap x (k - 1) ∈ t := (ht_idx (k - 1)).mpr hkm
            rw [hshift (k - 1)] at htin
            have htin' : x k ∈ t := by
              rw [Nat.sub_add_cancel hkone] at htin
              exact htin
            exact ht.2 (x k) htin'
        have htail : (Y \ Set.Iic p).Infinite := by
          exact hYinf.sdiff (Set.finite_Iic p)
        obtain ⟨v, hv⟩ := InfiniteSetEnumeration (Y \ Set.Iic p) htail
        have hv_mem : ∀ n, v n ∈ Y \ Set.Iic p := by
          intro n
          rw [← hv]
          exact ⟨n, rfl⟩
        have hv_gt : ∀ n, p < v n := by
          intro n
          apply Nat.lt_of_not_ge
          intro hnp
          exact (hv_mem n).2 (by simpa [Set.mem_Iic] using hnp)
        let g : Nat → Nat := fun n => if n < L then x n else v (n - L)
        have hg_succ : ∀ n, g n < g (n + 1) := by
          intro n
          by_cases hnL : n < L
          · by_cases hnext : n + 1 < L
            · simp [g, hnL, hnext]
            · have hn_eq : n + 1 = L := by omega
              simp [g, hnL, hnext, hn_eq]
              apply lt_of_le_of_lt
              · apply x.le_iff_le.mpr
                change n ≤ L - 1
                omega
              · exact hv_gt 0
          · have hnextL : ¬n + 1 < L := by omega
            simp [g, hnL, hnextL]
            have hLn : L ≤ n := Nat.le_of_not_gt hnL
            exact Nat.sub_lt_sub_right hLn (Nat.lt_succ_self n)
        have hg_strict : StrictMono g := strictMono_nat_of_lt_succ hg_succ
        let y : IncSeq := OrderEmbedding.ofStrictMono g hg_strict
        have hy_apply (n : Nat) : y n = g n := by
          rfl
        have hy_range : Set.range (y : Nat → Nat) ⊆ Y := by
          intro n hn
          rcases hn with ⟨k, rfl⟩
          by_cases hkL : k < L
          · rw [hy_apply]
            simp [g, hkL]
            exact hprefix_mem k hkL
          · rw [hy_apply]
            simp [g, hkL]
            exact (hv_mem (k - L)).1
        have hsy : ProperPrefixSet s (Set.range (y : Nat → Nat)) := by
          by_cases hiL : i < L
          · refine ⟨y i, ⟨i, rfl⟩, ?_⟩
            intro k
            constructor
            · intro hk
              obtain ⟨n, hn⟩ := ((ha k).mp hk).1
              have hni : n < i := x.lt_iff_lt.mp (by
                rw [hn]
                exact ((ha k).mp hk).2)
              refine ⟨⟨n, ?_⟩, ?_⟩
              · rw [hy_apply n]
                simp [g, Nat.lt_trans hni hiL]
                exact hn
              · rw [hy_apply i]
                simp [g, hiL]
                rw [← hn]
                exact x.lt_iff_lt.mpr hni
            · rintro ⟨⟨n, rfl⟩, hn⟩
              by_cases hnL : n < L
              · have hxn : x n < x i := by
                  rw [hy_apply n, hy_apply i] at hn
                  simp [g, hnL, hiL] at hn
                  exact x.lt_iff_lt.mpr hn
                have hyx : y n = x n := by
                  rw [hy_apply n]
                  simp [g, hnL]
                rw [hyx]
                exact (hs_idx n).mpr (x.lt_iff_lt.mp hxn)
              · rw [hy_apply n, hy_apply i] at hn
                simp [g, hnL, hiL] at hn
                have hxi_le : x i ≤ p := by
                  dsimp [p, L]
                  apply x.le_iff_le.mpr
                  omega
                exact False.elim ((Nat.not_lt_of_ge
                  (hxi_le.trans (Nat.le_of_lt (hv_gt (n - L))))) hn)
          · have hi_eq : i = L := by
              dsimp [L] at hiL ⊢
              omega
            refine ⟨v 0, ⟨L, ?_⟩, ?_⟩
            · rw [hy_apply]
              simp [g, hi_eq]
            · intro k
              constructor
              · intro hk
                obtain ⟨n, hn⟩ := ((ha k).mp hk).1
                have hni : n < i := x.lt_iff_lt.mp (by
                  rw [hn]
                  exact ((ha k).mp hk).2)
                refine ⟨⟨n, ?_⟩, ?_⟩
                · rw [hy_apply n]
                  have hnL : n < L := by omega
                  simp [g, hnL]
                  exact hn
                · have hxn_le_p : x n ≤ p := by
                    dsimp [p]
                    apply x.le_iff_le.mpr
                    omega
                  rw [← hn]
                  exact hxn_le_p.trans_lt (hv_gt 0)
              · rintro ⟨⟨n, rfl⟩, hn⟩
                by_cases hnL : n < L
                · have hyx : y n = x n := by
                    rw [hy_apply n]
                    simp [g, hnL]
                  rw [hyx]
                  have hni' : n < i := by
                    rw [hi_eq]
                    exact hnL
                  exact (hs_idx n).mpr hni'
                · rw [hy_apply n] at hn
                  simp [g, hnL] at hn
        have hshift_y (n : Nat) : ShiftMap y n = y (n + 1) := by
          rfl
        have hty : ProperPrefixSet t (Set.range (ShiftMap y : Nat → Nat)) := by
          by_cases hjL : j + 1 < L
          · refine ⟨ShiftMap y j, ⟨j, rfl⟩, ?_⟩
            intro k
            constructor
            · intro hk
              obtain ⟨n, hn⟩ := ((hb k).mp hk).1
              have hnj : n < j := (ShiftMap x).lt_iff_lt.mp (by
                rw [hn]
                exact ((hb k).mp hk).2)
              refine ⟨⟨n, ?_⟩, ?_⟩
              · rw [hshift_y n, hy_apply (n + 1)]
                have hnL : n + 1 < L := by omega
                simp [g, hnL]
                rw [← hshift n]
                exact hn
              · rw [hshift_y j, hy_apply (j + 1)]
                simp [g, hjL]
                rw [← hn, hshift n]
                exact x.lt_iff_lt.mpr (by omega)
            · rintro ⟨⟨n, rfl⟩, hn⟩
              by_cases hnL : n + 1 < L
              · have hxn : x (n + 1) < x (j + 1) := by
                  rw [hshift_y n, hshift_y j, hy_apply (n + 1),
                    hy_apply (j + 1)] at hn
                  simp [g, hnL, hjL] at hn
                  exact x.lt_iff_lt.mpr (by omega)
                have hnj : n < j := by
                  exact Nat.lt_of_succ_lt_succ (x.lt_iff_lt.mp hxn)
                have htn : ShiftMap x n ∈ t := (ht_idx n).mpr hnj
                have heq : ShiftMap y n = ShiftMap x n := by
                  rw [hshift_y n, hy_apply (n + 1), hshift n]
                  simp [g, hnL]
                rw [heq]
                exact htn
              · rw [hshift_y n, hshift_y j, hy_apply (n + 1),
                  hy_apply (j + 1)] at hn
                simp [g, hnL, hjL] at hn
                have hcut_le : x (j + 1) ≤ p := by
                  dsimp [p]
                  apply x.le_iff_le.mpr
                  change j + 1 ≤ L - 1
                  omega
                exact False.elim ((Nat.not_lt_of_ge
                  (hcut_le.trans (Nat.le_of_lt (hv_gt (n + 1 - L))))) hn)
          · have hj_eq : j + 1 = L := by
              dsimp [L] at hjL ⊢
              omega
            refine ⟨v 0, ⟨j, ?_⟩, ?_⟩
            · rw [hshift_y j, hy_apply (j + 1)]
              simp [g, hj_eq]
            · intro k
              constructor
              · intro hk
                obtain ⟨n, hn⟩ := ((hb k).mp hk).1
                have hnj : n < j := (ShiftMap x).lt_iff_lt.mp (by
                  rw [hn]
                  exact ((hb k).mp hk).2)
                refine ⟨⟨n, ?_⟩, ?_⟩
                · rw [hshift_y n, hy_apply (n + 1)]
                  have hnL : n + 1 < L := by omega
                  simp [g, hnL]
                  rw [← hshift n]
                  exact hn
                · have hcut_le : x (n + 1) ≤ p := by
                    dsimp [p]
                    apply x.le_iff_le.mpr
                    change n + 1 ≤ L - 1
                    omega
                  rw [← hn]
                  exact hcut_le.trans_lt (hv_gt 0)
              · rintro ⟨⟨n, rfl⟩, hn⟩
                by_cases hnL : n + 1 < L
                · have hnj : n < j := by
                    omega
                  have htn : ShiftMap x n ∈ t := (ht_idx n).mpr hnj
                  have heq : ShiftMap y n = ShiftMap x n := by
                    rw [hshift_y n, hy_apply (n + 1), hshift n]
                    simp [g, hnL]
                  rw [heq]
                  exact htn
                · rw [hshift_y n, hy_apply (n + 1)] at hn
                  simp [g, hnL] at hn
        exact ⟨y, hy_range, hsy, hty⟩
    obtain ⟨y, hyY, hys, hyt⟩ := construct s t hs ht hst
    have hex : ∀ n : Nat, ∃ m : Nat, z.1 m = y n := by
      intro n
      apply hyY
      exact ⟨n, rfl⟩
    choose u hu using hex
    have hu_strict : StrictMono u := by
      intro a b hab
      apply z.1.lt_iff_lt.mp
      rw [hu a, hu b]
      exact y.lt_iff_lt.mpr hab
    let u' : IncSeq := OrderEmbedding.ofStrictMono u hu_strict
    have hu'_apply (n : Nat) : u' n = u n := by
      rfl
    have hyfactor (n : Nat) : z.1 (u' n) = y n := by
      rw [hu'_apply]
      exact hu n
    let x0 : BaseIncSeq X :=
      ⟨IncSeqComp z.1 u', by
        intro n hn
        rcases hn with ⟨m, hm⟩
        apply z.2
        exact ⟨u' m, hm⟩⟩
    let x1 : BaseIncSeq X :=
      ⟨IncSeqComp z.1 (ShiftMap u'), by
        intro n hn
        rcases hn with ⟨m, hm⟩
        apply z.2
        exact ⟨ShiftMap u' m, hm⟩⟩
    have hcomp0 : IncSeqComp z.1 u' = y := by
      ext n
      change z.1 (u' n) = y n
      exact hyfactor n
    have hcomp1 : IncSeqComp z.1 (ShiftMap u') = ShiftMap y := by
      calc
        IncSeqComp z.1 (ShiftMap u') = ShiftMap (IncSeqComp z.1 u') :=
          RestrictionShift z.1 u'
        _ = ShiftMap y := by rw [hcomp0]
    have qs : FrontPrefix F s x0.1 := by
      refine ⟨hs.1, ?_⟩
      change ProperPrefixSet s (Set.range (IncSeqComp z.1 u' : Nat → Nat))
      simpa [hcomp0] using hys
    have qt : FrontPrefix F t x1.1 := by
      refine ⟨ht.1, ?_⟩
      change ProperPrefixSet t (Set.range (IncSeqComp z.1 (ShiftMap u') : Nat → Nat))
      simpa [hcomp1] using hyt
    have he0 := hext x0 s qs
    have he1 := hext x1 t qt
    have hr : r (h x0) (h x1) := by
      simpa [BaseRestrict, x0, x1] using hp u'
    rw [he0, he1] at hr
    change r (f.value ⟨s, hsub hs⟩) (f.value ⟨t, hsub ht⟩)
    simpa using hr
