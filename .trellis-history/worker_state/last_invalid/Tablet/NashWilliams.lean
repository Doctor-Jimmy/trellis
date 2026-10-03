import Tablet.Front
import Tablet.FrontRestrict
import Tablet.FrontRayClosure
import Tablet.FrontRestriction
import Tablet.FrontTreeWellFounded
import Tablet.BooleanInfinitePigeonhole
import Tablet.SubFrontCharacterization
import Tablet.InitialSegmentInsert

-- [TABLET NODE: NashWilliams]
theorem NashWilliams (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (S : Set (Finset Nat)) (hS : S ⊆ F) :
    ∃ F' : Set (Finset Nat), ∃ Y : Set Nat,
      Front F' Y ∧ F' ⊆ F ∧ (F' ⊆ S ∨ F' ∩ S = ∅) := by
-- BODY
  classical
  let Stem : Finset Nat → Set (Finset Nat) → Prop := fun p G =>
    p ∈ PrefixTree F ∧
      ∀ s : Finset Nat, s ∈ PrefixTree G →
        (∀ a ∈ p, ∀ b ∈ s, a < b) ∧ p ∪ s ∈ PrefixTree F
  let P : {s : Finset Nat // s ∈ PrefixTree F} → Prop := fun u =>
    ∀ (G : Set (Finset Nat)) (Z : Set Nat), Front G Z → Stem u.1 G →
      ∀ T : Set (Finset Nat),
        ∃ G' : Set (Finset Nat), ∃ W : Set Nat,
          Front G' W ∧ G' ⊆ G ∧ (G' ⊆ T ∨ G' ∩ T = ∅)
  have hWF := FrontTreeWellFounded F X hF
  have hP : ∀ u, P u := by
    intro u
    induction u using hWF.induction with
    | h u ih =>
      intro G Z hG hStem T
      by_cases htriv : G = {∅}
      · subst G
        refine ⟨{∅}, Z, hG, ?_, ?_⟩
        · intro s hs
          exact hs
        · by_cases he : (∅ : Finset Nat) ∈ T
          · exact Or.inl (by simpa [he])
          · exact Or.inr (by simpa [he])
      · have hbase := (FrontNontrivialBase G Z hG htriv).2
        have hrays := FrontRayClosure G Z hG htriv
        have hnonempty := (FrontNontrivialBase G Z hG htriv).1
        have htail : ∀ n ∈ Z, (TailSet Z n).Infinite := by
          intro n hn
          apply Set.Infinite.mono (s := Z \ Set.Iic n) (t := TailSet Z n)
          · intro k hk
            exact ⟨hk.1, Nat.lt_of_not_ge hk.2⟩
          · exact hG.infinite_base.sdiff (Set.finite_Iic n)
        have hsingle : ∀ n ∈ Z, ({n} : Finset Nat) ∈ PrefixTree G := by
          intro n hn
          let Y : Set Nat := insert n (TailSet Z n)
          have hYinf : Y.Infinite := by
            apply Set.Infinite.mono (s := TailSet Z n) (t := Y)
            · intro k hk
              exact Set.mem_insert_iff.mpr (Or.inr hk)
            · exact htail n hn
          have hYsub : Y ⊆ Z := by
            intro k hk
            rcases Set.mem_insert_iff.mp hk with rfl | hk
            · exact hn
            · exact (hk.1)
          obtain ⟨t, htG, htp⟩ := hG.dense Y hYsub hYinf
          rcases htp with ⟨m, hmY, htm⟩
          have htne : t.Nonempty := hnonempty t htG
          have hmn : m ≠ n := by
            intro hmn
            obtain ⟨k, hkt⟩ := htne
            have hkt' := (htm k).mp hkt
            have hkY : k = n ∨ k ∈ TailSet Z n := by
              simpa only [Y, Set.mem_insert_iff] using hkt'.1
            rcases hkY with hkn | hkY
            · have hknm : k < m := hkt'.2
              omega
            · have hknm : k < m := hkt'.2
              subst m
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hkY.2)) hknm
          have hnm : n < m := by
            have hmY' : m = n ∨ m ∈ TailSet Z n := by
              simpa only [Y, Set.mem_insert_iff] using hmY
            rcases hmY' with rfl | hmY'
            · exact (hmn rfl).elim
            · exact hmY'.2
          have hnt : n ∈ t := by
            apply (htm n).mpr
            exact ⟨Set.mem_insert n (TailSet Z n), hnm⟩
          have hinit : InitialSegment ({n} : Finset Nat) t := by
            by_cases ht_single : t = {n}
            · exact Or.inl ht_single.symm
            · let d : Finset Nat := t \ {n}
              have hd : d.Nonempty := by
                apply Finset.sdiff_nonempty.mpr
                intro hsub
                apply ht_single
                apply Finset.Subset.antisymm hsub
                exact Finset.singleton_subset_iff.mpr hnt
              let q : Nat := d.min' hd
              have hq_d : q ∈ d := Finset.min'_mem d hd
              have hq_t : q ∈ t := (Finset.mem_sdiff.mp hq_d).1
              have hnq : n < q := by
                have hq_ne : q ≠ n := by
                  simpa using (Finset.mem_sdiff.mp hq_d).2
                have hqY := (htm q).mp hq_t
                have hqY' : q = n ∨ q ∈ TailSet Z n := by
                  simpa only [Y, Set.mem_insert_iff] using hqY.1
                rcases hqY' with hqn | hqY'
                · exact (hq_ne hqn).elim
                · exact hqY'.2
              refine Or.inr ⟨q, hq_t, ?_⟩
              ext k
              constructor
              · intro hk
                have hkn : k = n := by simpa using hk
                subst k
                exact Finset.mem_filter.mpr ⟨hnt, hnq⟩
              · intro hk
                have hk' := Finset.mem_filter.mp hk
                have hkY := (htm k).mp hk'.1
                have hkY' : k = n ∨ k ∈ TailSet Z n := by
                  simpa only [Y, Set.mem_insert_iff] using hkY.1
                rcases hkY' with hkn | hkY'
                · simpa [hkn]
                · have hk_d : k ∈ d := Finset.mem_sdiff.mpr
                    ⟨hk'.1, by simpa using (Nat.ne_of_gt hkY'.2)⟩
                  exact False.elim ((Nat.not_lt_of_ge
                    (Finset.min'_le d k hk_d)) hk'.2)
          exact ⟨t, htG, hinit⟩
        have hstage : ∀ (A : Set Nat), A ⊆ Z → A.Infinite →
            ∀ n ∈ A, ∃ q : Set Nat,
            q ⊆ TailSet A n ∧ q.Infinite ∧
              (FrontRestrict (Ray G n) q ⊆
                  {s | insert n s ∈ T} ∨
               FrontRestrict (Ray G n) q ∩
                  {s | insert n s ∈ T} = ∅) := by
          intro A hAZ hA n hn
          have hAtail : (TailSet A n).Infinite := by
            apply Set.Infinite.mono (s := A \ Set.Iic n) (t := TailSet A n)
            · intro k hk
              exact ⟨hk.1, Nat.lt_of_not_ge hk.2⟩
            · exact hA.sdiff (Set.finite_Iic n)
          have hqstage : Stem (insert n u.1) (Ray G n) := by
            refine ⟨?_, ?_⟩
            · simpa [Finset.union_comm] using
                ((hStem).2 ({n}) (hsingle n (hAZ hn))).2
            · intro s hs
              rcases hs with ⟨t, ht, hst⟩
              have hs' : insert n s ∈ PrefixTree G := by
                have ht' := ht
                refine ⟨insert n t, ht'.2, ?_⟩
                rcases hst with rfl | ⟨m, hm, hsm⟩
                · exact Or.inl rfl
                · right
                  refine ⟨m, Finset.mem_insert_of_mem hm, ?_⟩
                  ext k
                  have hnm : n < m := ht'.1 m hm
                  by_cases hkn : k = n
                  · subst k
                    simp [hnm]
                  · simp only [Finset.mem_insert, hkn, false_or,
                      Finset.mem_filter]
                    simpa [hsm]
              have hsp := (hStem).2 (insert n s) hs'
              constructor
              · intro a ha b hb
                rcases Finset.mem_insert.mp ha with rfl | ha
                · have hsub : s ⊆ t := by
                    rcases hst with rfl | ⟨q, hq, hfilter⟩
                    · exact Finset.Subset.rfl
                    · rw [hfilter]
                      exact Finset.filter_subset _ _
                  exact ht.1 b (hsub hb)
                · exact hsp.1 a ha b
                    (Finset.mem_insert_of_mem hb)
              · have heq : insert n u.1 ∪ s = u.1 ∪ insert n s := by
                  ext k
                  simp [or_assoc, or_left_comm, or_comm]
                exact heq ▸ hsp.2
          have hproper : ProperInitialSegment u.1 (insert n u.1) := by
            have hpn : ∀ a ∈ u.1, a < n := by
              intro a ha
              exact (hStem).2 ({n}) (hsingle n (hAZ hn)) |>.1 a ha n
                (Finset.mem_singleton_self n)
            have hneq : n ∉ u.1 := by
              intro hnu
              exact Nat.lt_irrefl n (hpn n hnu)
            refine ⟨?_, ?_⟩
            · exact InitialSegmentInsert u.1 u.1 (Or.inl rfl) n hpn
            · intro heq
              apply hneq
              have : n ∈ insert n u.1 := Finset.mem_insert_self n u.1
              rw [← heq] at this
              exact this
          have hrec := ih ⟨insert n u.1, hqstage.1⟩ hproper
          have hK : Front (FrontRestrict (Ray G n) (TailSet A n))
              (TailSet A n) := by
            apply FrontRestriction (Ray G n) (TailSet Z n)
              (hrays.1 n (hAZ hn))
              (TailSet A n)
            · intro k hk
              exact ⟨hAZ hk.1, hk.2⟩
            · exact hAtail
          obtain ⟨H, W, hH, hHK, halt⟩ :=
            hrec (FrontRestrict (Ray G n) (TailSet A n)) (TailSet A n)
              hK
              (by
                refine ⟨hqstage.1, ?_⟩
                intro s hs
                have hs' : s ∈ PrefixTree (Ray G n) := by
                  rcases hs with ⟨t, ht, hst⟩
                  exact ⟨t, ht.1, hst⟩
                exact hqstage.2 s hs')
              {s | insert n s ∈ T}
          obtain ⟨q, hqA, hqinf, hEq⟩ :=
            (SubFrontCharacterization
              (FrontRestrict (Ray G n) (TailSet A n)) (TailSet A n)
              hK H hHK).mp ⟨W, hH⟩
          have hrestrict_eq :
              FrontRestrict (FrontRestrict (Ray G n) (TailSet A n)) q =
                FrontRestrict (Ray G n) q := by
            ext s
            constructor
            · intro hs
              exact ⟨hs.1.1, hs.2⟩
            · intro hs
              refine ⟨⟨hs.1, ?_⟩, hs.2⟩
              intro k hk
              exact hqA (hs.2 k hk)
          rw [hEq, hrestrict_eq] at halt
          rcases halt with halt | halt
          · exact ⟨q, hqA, hqinf, Or.inl halt⟩
          · exact ⟨q, hqA, hqinf, Or.inr halt⟩
        let D : Type := {A : Set Nat // A ⊆ Z ∧ A.Infinite}
        let d0 : D := ⟨Z, by intro k hk; exact hk, hG.infinite_base⟩
        have hmin_exists : ∀ d : D, ∃ n, n ∈ d.1 := by
          intro d
          exact d.2.2.nonempty
        let mn : D → Nat := fun d => Nat.find (hmin_exists d)
        have hmn_mem (d : D) : mn d ∈ d.1 := by
          exact Nat.find_spec (hmin_exists d)
        have hmn_le (d : D) {x : Nat} (hx : x ∈ d.1) : mn d ≤ x := by
          exact Nat.find_min' (hmin_exists d) hx
        let next : D → D := fun d =>
          let n := mn d
          let q := Classical.choose
            (hstage d.1 d.2.1 d.2.2 (mn d) (hmn_mem d))
          ⟨q, (Classical.choose_spec
              (hstage d.1 d.2.1 d.2.2 (mn d) (hmn_mem d))).1.trans
                (by intro x hx; exact (d.2.1 hx.1)),
            (Classical.choose_spec
              (hstage d.1 d.2.1 d.2.2 (mn d) (hmn_mem d))).2.1⟩
        have hnext_spec (d : D) :
            (next d).1 ⊆ TailSet d.1 (mn d) ∧
              (next d).1.Infinite ∧
              (FrontRestrict (Ray G (mn d)) (next d).1 ⊆
                  {s | insert (mn d) s ∈ T} ∨
               FrontRestrict (Ray G (mn d)) (next d).1 ∩
                  {s | insert (mn d) s ∈ T} = ∅) := by
          dsimp [next]
          exact Classical.choose_spec
            (hstage d.1 d.2.1 d.2.2 (mn d) (hmn_mem d))
        let ds : Nat → D := Nat.rec d0 (fun _ d => next d)
        let nseq : Nat → Nat := fun k =>
          mn (ds k)
        have hds_sub : ∀ k, (ds (k + 1)).1 ⊆ (ds k).1 := by
          intro k
          have hs : (next (ds k)).1 ⊆
              TailSet (ds k).1 (mn (ds k)) :=
            (hnext_spec (ds k)).1
          change (next (ds k)).1 ⊆ (ds k).1
          intro x hx
          exact (hs hx).1
        have hnmem : ∀ k, nseq k ∈ Z := by
          intro k
          exact (ds k).2.1 (hmn_mem (ds k))
        have hninc : ∀ k, nseq k < nseq (k + 1) := by
          intro k
          have hs := (hnext_spec (ds k)).1
          have hm : nseq (k + 1) ∈ (ds (k + 1)).1 := hmn_mem (ds (k + 1))
          exact (hs hm).2
        have hds_nested : ∀ {i j : Nat}, i ≤ j →
            (ds j).1 ⊆ (ds i).1 := by
          intro i j hij
          induction j, hij using Nat.le_induction with
          | base => exact Set.Subset.rfl
          | succ j hij ih =>
              have hsuc : (ds (Nat.succ j)).1 ⊆ (ds j).1 := by
                simpa only [Nat.succ_eq_add_one] using hds_sub j
              exact hsuc.trans ih
        have hnmono : ∀ {i j : Nat}, i ≤ j → nseq i ≤ nseq j := by
          intro i j hij
          induction j, hij using Nat.le_induction with
          | base => exact Nat.le_refl _
          | succ j hij ih => exact ih.trans (Nat.le_of_lt (hninc j))
        have hnlt : ∀ {i j : Nat}, i < j → nseq i < nseq j := by
          intro i j hij
          exact (hninc i).trans_le (hnmono (Nat.succ_le_iff.mpr hij))
        let b : Nat → Bool := fun k =>
          if FrontRestrict (Ray G (nseq k)) (ds (k + 1)).1 ⊆
              {s | insert (nseq k) s ∈ T} then true else false
        obtain ⟨c, hc⟩ := BooleanInfinitePigeonhole b
        let I : Set Nat := {k | b k = c}
        let Y : Set Nat := nseq '' I
        have hYsub : Y ⊆ Z := by
          intro y hy
          rcases hy with ⟨k, hk, rfl⟩
          exact hnmem k
        have hIinj : Set.InjOn nseq I := by
          intro i hi j hj heq
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hij | hji
          · exact (Nat.ne_of_lt (hnlt hij)) heq
          · exact (Nat.ne_of_lt (hnlt hji)) heq.symm
        have hYinf : Y.Infinite := Set.Infinite.image hIinj hc
        have hfrontY : Front (FrontRestrict G Y) Y :=
          FrontRestriction G Z hG Y hYsub hYinf
        have hsubG : FrontRestrict G Y ⊆ G := by
          intro s hs
          exact hs.1
        have hresult :
            (FrontRestrict G Y ⊆ T ∨ FrontRestrict G Y ∩ T = ∅) := by
          by_cases hc' : c = true
          · left
            intro s hs
            have hsG : s ∈ G := hs.1
            have hsY : ∀ k, k ∈ s → k ∈ Y := hs.2
            have hsne : s.Nonempty := hnonempty s hsG
            let m := s.min' hsne
            have hmY : m ∈ Y := hsY m (Finset.min'_mem s hsne)
            rcases hmY with ⟨k, hkI, hmk⟩
            have hmk' : m = nseq k := hmk.symm
            have hkmin : ∀ q, q ∈ s → m ≤ q := by
              intro q hq
              exact Finset.min'_le s q hq
            have htRay : s.erase m ∈ Ray G (nseq k) := by
              refine ⟨?_, ?_⟩
              · intro q hq
                have hqS : q ∈ s := Finset.mem_of_mem_erase hq
                have hqne : q ≠ m := (Finset.mem_erase.mp hq).1
                have hqgt : m < q := lt_of_le_of_ne (hkmin q hqS)
                  (Ne.symm hqne)
                simpa [hmk'] using hqgt
              · have hst : insert (nseq k) (s.erase m) = s := by
                  simpa [m, hmk] using
                    Finset.insert_erase (Finset.min'_mem s hsne)
                exact hst.symm ▸ hsG
            have htA : s.erase m ∈ FrontRestrict (Ray G (nseq k))
                (ds (k + 1)).1 := by
              refine ⟨htRay, ?_⟩
              intro q hq
              have hqS : q ∈ s := Finset.mem_of_mem_erase hq
              have hqY := hsY q hqS
              rcases hqY with ⟨j, hjI, rfl⟩
              have hqne : nseq j ≠ nseq k := by
                intro heq
                apply (Finset.mem_erase.mp hq).1
                simpa [hmk'] using heq
              have hkj : k < j := by
                by_contra hkj
                have hle : j ≤ k := Nat.le_of_not_gt hkj
                have := hnmono hle
                have hmle : nseq k ≤ nseq j := by
                  simpa [hmk'] using (hkmin _ hqS)
                exact hqne (Nat.le_antisymm this hmle)
              exact hds_nested (Nat.succ_le_iff.mpr hkj)
                (hmn_mem (ds j))
            have hbk : b k = c := hkI
            have hbt : FrontRestrict (Ray G (nseq k)) (ds (k + 1)).1 ⊆
                {s | insert (nseq k) s ∈ T} := by
              have hbc : b k = true := by simpa [hc'] using hbk
              simpa [b] using hbc
            have hmember := hbt htA
            have hst : insert (nseq k) (s.erase m) = s := by
              calc
                insert (nseq k) (s.erase m) = insert m (s.erase m) := by
                  rw [hmk']
                _ = s := Finset.insert_erase (Finset.min'_mem s hsne)
            exact hst ▸ hmember
          · right
            ext s
            constructor
            · intro hs
              have hsF : s ∈ FrontRestrict G Y := hs.1
              have hsT : s ∈ T := hs.2
              have hsG : s ∈ G := hsF.1
              have hsY : ∀ k, k ∈ s → k ∈ Y := hsF.2
              have hsne : s.Nonempty := hnonempty s hsG
              let m := s.min' hsne
              have hmY : m ∈ Y := hsY m (Finset.min'_mem s hsne)
              rcases hmY with ⟨k, hkI, hmk⟩
              have hmk' : m = nseq k := hmk.symm
              have hkmin : ∀ q, q ∈ s → m ≤ q := by
                intro q hq
                exact Finset.min'_le s q hq
              have htRay : s.erase m ∈ Ray G (nseq k) := by
                refine ⟨?_, ?_⟩
                · intro q hq
                  have hqS : q ∈ s := Finset.mem_of_mem_erase hq
                  have hqne : q ≠ m := (Finset.mem_erase.mp hq).1
                  have hqgt : m < q := lt_of_le_of_ne (hkmin q hqS)
                    (Ne.symm hqne)
                  simpa [hmk'] using hqgt
                · have hst : insert (nseq k) (s.erase m) = s := by
                    simpa [m, hmk] using
                      Finset.insert_erase (Finset.min'_mem s hsne)
                  exact hst.symm ▸ hsG
              have htA : s.erase m ∈ FrontRestrict (Ray G (nseq k))
                  (ds (k + 1)).1 := by
                refine ⟨htRay, ?_⟩
                intro q hq
                have hqS : q ∈ s := Finset.mem_of_mem_erase hq
                have hqY := hsY q hqS
                rcases hqY with ⟨j, hjI, rfl⟩
                have hqne : nseq j ≠ nseq k := by
                  intro heq
                  apply (Finset.mem_erase.mp hq).1
                  simpa [hmk'] using heq
                have hkj : k < j := by
                  by_contra hkj
                  have hle : j ≤ k := Nat.le_of_not_gt hkj
                  have hle' := hnmono hle
                  have hmle : nseq k ≤ nseq j := by
                    simpa [hmk'] using (hkmin _ hqS)
                  exact hqne (Nat.le_antisymm hle' hmle)
                exact hds_nested (Nat.succ_le_iff.mpr hkj)
                  (hmn_mem (ds j))
              have hbc : b k ≠ true := by
                intro hb
                apply hc'
                calc
                  c = b k := hkI.symm
                  _ = true := hb
              have hdisj : FrontRestrict (Ray G (nseq k)) (ds (k + 1)).1 ∩
                  {s | insert (nseq k) s ∈ T} = ∅ := by
                rcases (hnext_spec (ds k)).2.2 with hsub | hdisj
                · apply (hbc (by simpa [b] using hsub)).elim
                · exact hdisj
              have hst : insert (nseq k) (s.erase m) = s := by
                simpa [m, hmk] using
                  Finset.insert_erase (Finset.min'_mem s hsne)
              have hmember : s.erase m ∈
                  {s | insert (nseq k) s ∈ T} := by
                change insert (nseq k) (s.erase m) ∈ T
                simpa only [hst] using hsT
              have hbad : s.erase m ∈
                  FrontRestrict (Ray G (nseq k)) (ds (k + 1)).1 ∩
                    {s | insert (nseq k) s ∈ T} := ⟨htA, hmember⟩
              rw [hdisj] at hbad
              exact False.elim (by simpa using hbad)
            · intro hs
              exact False.elim (by simpa using hs)
        exact ⟨FrontRestrict G Y, Y, hfrontY, hsubG, hresult⟩
  have hu : (∅ : Finset Nat) ∈ PrefixTree F := by
    obtain ⟨s, hs, hsp⟩ := hF.dense X (by intro k hk; exact hk) hF.infinite_base
    refine ⟨s, hs, ?_⟩
    rcases s.eq_empty_or_nonempty with hs0 | hs0
    · exact Or.inl hs0.symm
    · let n := s.min' hs0
      right
      refine ⟨n, ?_, ?_⟩
      · exact Finset.min'_mem s hs0
      · ext k
        constructor
        · intro hk
          exact False.elim (by simpa using hk)
        · intro hk
          have hk' := Finset.mem_filter.mp hk
          exact False.elim ((Nat.not_lt_of_ge (Finset.min'_le s k hk'.1)) hk'.2)
  have hroot := hP ⟨∅, hu⟩ F X hF (by
    constructor
    · exact hu
    · intro s hs
      exact ⟨by simp, by simpa using hs⟩) S
  exact hroot
