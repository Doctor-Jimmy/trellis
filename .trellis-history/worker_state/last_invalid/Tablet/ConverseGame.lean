import Tablet.TildeFSingleton
import Tablet.HerCtblRel
import Tablet.FrontBridgeInit
import Tablet.FrontBridgeStep
import Tablet.FrontBridgeTerminal
import Tablet.BadSuperSequence
import Tablet.PowerRelAtomAtom
import Tablet.PowerRelAtomNode
import Tablet.PowerRelNodeAtom
import Tablet.PowerRelNodeNode

universe u

-- [TABLET NODE: ConverseGame]
theorem ConverseGame {Q : Type u} {F : Set (Finset Nat)}
    (r : Q → Q → Prop) (f : SuperSequence F Set.univ Q)
    (htriv : ∅ ∉ F) (hbad : BadSuperSequence r f) :
    ∀ m n : Nat, m < n →
      ¬ HerCtblRel r
        ⟨TildeFSingleton f htriv m,
          TildeFHerCtbl f
            ⟨{m}, FrontTreeSingleton F f.front htriv m⟩⟩
        ⟨TildeFSingleton f htriv n,
          TildeFHerCtbl f
            ⟨{n}, FrontTreeSingleton F f.front htriv n⟩⟩ := by
-- BODY
  intro m n hmn hrel
  let Tree := {s : Finset Nat // s ∈ PrefixTree F}
  let sm : Tree := ⟨{m}, FrontTreeSingleton F f.front htriv m⟩
  let sn : Tree := ⟨{n}, FrontTreeSingleton F f.front htriv n⟩
  have hcomp : PowerRel r (TildeF f sm) (TildeF f sn) := by
    simpa [HerCtblRel, TildeFSingleton, sm, sn] using hrel
  have hb : FrontBridge F sm.1 sn.1 ({m, n} : Finset Nat) := by
    exact FrontBridgeInit F f.front htriv hmn
  have hWF : WellFounded (fun x y : Tree =>
      ProperInitialSegment y.1 x.1) := by
    exact FrontTreeWellFounded F Set.univ f.front
  have hpairWF : WellFounded (Prod.Lex
      (fun x y : Tree => ProperInitialSegment y.1 x.1)
      (fun x y : Tree => ProperInitialSegment y.1 x.1)) :=
    WellFounded.prod_lex hWF hWF
  have game : ∀ (p : Tree × Tree) (u : Finset Nat),
      FrontBridge F p.1.1 p.2.1 u →
      PowerRel r (TildeF f p.1) (TildeF f p.2) → False := by
    have tail_bound : ∀ {t u : Finset Nat} {q : Nat}, t.Nonempty →
        t = FrontBridgeTail u →
        ProperInitialSegment t (insert q t) →
        ∀ j, j ∈ u → j < q := by
      intro t u q ht htu hq j hju
      have hq_gt_t : ∀ k, k ∈ t → k < q := by
        intro k hkt
        rcases hq.1 with heq | ⟨c, hc, hfilter⟩
        · exact (hq.2 heq).elim
        · have hkf : k ∈ (insert q t).filter (fun z => z < c) := by
            rw [← hfilter]
            exact hkt
          have hkc : k < c := (Finset.mem_filter.mp hkf).2
          have hcq : c = q := by
            rcases Finset.mem_insert.mp hc with hcq | hct
            · exact hcq
            · have hcf : c ∈ (insert q t).filter (fun z => z < c) := by
                rw [← hfilter]
                exact hct
              exact (Nat.lt_irrefl c (Finset.mem_filter.mp hcf).2).elim
          simpa [hcq] using hkc
      by_cases hjtail : j ∈ FrontBridgeTail u
      · have hjt : j ∈ t := by
          rw [htu]
          exact hjtail
        exact hq_gt_t j hjt
      · have hjmin : ∀ k, k ∈ u → j ≤ k := by
          intro k hku
          by_contra hnot
          have hkj : k < j := Nat.lt_of_not_ge hnot
          apply hjtail
          rw [FrontBridgeTail]
          exact Finset.mem_filter.mpr ⟨hju, ⟨k, hku, hkj⟩⟩
        obtain ⟨k, hkt⟩ := ht
        have hku : k ∈ u := by
          rw [htu] at hkt
          exact (Finset.mem_filter.mp hkt).1
        exact lt_of_le_of_lt (hjmin k hku) (hq_gt_t k (htu ▸ hkt))
    intro p
    induction p using hpairWF.induction with
    | h p ih =>
      intro u hbridge hpow
      let s : Tree := p.1
      let t : Tree := p.2
      have hs : s.1 ∈ PrefixTree F := s.2
      have ht : t.1 ∈ PrefixTree F := t.2
      have hb' := hbridge
      rw [FrontBridge] at hb'
      rcases hb' with ⟨hs_tree', ht_tree', ht_ne', hu_ne', hs_init',
        hs_ext', ht_init', ht_tail'⟩
      by_cases hsF : s.1 ∈ F
      · by_cases htF : t.1 ∈ F
        · rw [TildeFFrontEquation f s hsF,
            TildeFFrontEquation f t htF,
            PowerRelAtomAtom] at hpow
          have hshift : FiniteShift s.1 t.1 :=
            FrontBridgeTerminal F hbridge hsF htF
          exact hbad s.1 t.1 hsF htF hshift hpow
        · rw [TildeFFrontEquation f s hsF,
            TildeFNonfrontEquation f t htF,
            PowerRelAtomNode] at hpow
          obtain ⟨i, hi⟩ := hpow
          have ht_ne : t.1.Nonempty := ht_ne'
          have hnu : ∀ j, j ∈ u → j < i.down.1 :=
            tail_bound ht_ne (ht_tail' htF)
              i.down.2.1
          have hnext := FrontBridgeStep F f.front hbridge
            (Or.inl ⟨hsF, rfl⟩)
            (Or.inl ⟨htF, ht_ne, i.down.2.1, i.down.2.2,
              ⟨i.down.1, rfl, hnu, rfl⟩⟩)
          apply ih (s, ⟨insert i.down.1 t.1, i.down.2.2⟩)
            (Prod.Lex.right s i.down.2.1) (insert i.down.1 u) hnext.1
          rw [TildeFFrontEquation f s hsF]
          simpa using hi
      · by_cases htF : t.1 ∈ F
        · rw [TildeFNonfrontEquation f s hsF,
            TildeFFrontEquation f t htF,
            PowerRelNodeAtom] at hpow
          obtain ⟨a, has, hua, hua_tree⟩ := hs_ext' hsF
          have ha_tree : insert a s.1 ∈ PrefixTree F := by
            simpa [hua] using hua_tree
          have hleft_pow := hpow
            (ULift.up ⟨a, has, ha_tree⟩)
          let k : Nat := u.max' hu_ne' + 1
          have hku : ∀ j, j ∈ u → j < k := by
            intro j hju
            dsimp [k]
            exact Nat.lt_succ_of_le (Finset.le_max' u j hju)
          have hnext := FrontBridgeStep F f.front hbridge
            (Or.inr ⟨hsF, rfl⟩)
            (Or.inr ⟨htF, rfl, k, hku, rfl⟩)
          apply ih (⟨u, hnext.2.1⟩, t)
            (Prod.Lex.left t t (by simpa [hua] using has))
            (insert k u) hnext.1
          rw [TildeFFrontEquation f t htF]
          simpa [hua] using hleft_pow
        · rw [TildeFNonfrontEquation f s hsF,
            TildeFNonfrontEquation f t htF,
            PowerRelNodeNode] at hpow
          obtain ⟨a, has, hua, hua_tree⟩ := hs_ext' hsF
          have ha_tree : insert a s.1 ∈ PrefixTree F := by
            simpa [hua] using hua_tree
          have hleft_pow := hpow
            (ULift.up ⟨a, has, ha_tree⟩)
          obtain ⟨i, hi⟩ := hleft_pow
          have hnu : ∀ j, j ∈ u → j < i.down.1 :=
            tail_bound ht_ne' (ht_tail' htF) i.down.2.1
          have hnext := FrontBridgeStep F f.front hbridge
            (Or.inr ⟨hsF, rfl⟩)
            (Or.inl ⟨htF, ht_ne', i.down.2.1, i.down.2.2,
              ⟨i.down.1, rfl, hnu, rfl⟩⟩)
          apply ih (⟨u, hnext.2.1⟩,
              ⟨insert i.down.1 t.1, i.down.2.2⟩)
            (Prod.Lex.left _ _ (by simpa [hua] using has))
            (insert i.down.1 u) hnext.1
          simpa [hua] using hi
  exact game (sm, sn) ({m, n} : Finset Nat) hb hcomp
