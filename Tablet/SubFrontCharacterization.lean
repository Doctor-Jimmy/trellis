import Tablet.Front
import Tablet.FrontRestrict
import Tablet.FrontRestriction

-- [TABLET NODE: SubFrontCharacterization]
theorem SubFrontCharacterization (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (F' : Set (Finset Nat))
    (hsub : F' ⊆ F) :
    (∃ Y : Set Nat, Front F' Y) ↔
      ∃ Z : Set Nat, Z ⊆ X ∧ Z.Infinite ∧ F' = FrontRestrict F Z := by
-- BODY
  classical
  constructor
  · rintro ⟨Y, hF'⟩
    by_cases htriv : F = ({∅} : Set (Finset Nat))
    · have hF'nonempty : F'.Nonempty := by
        obtain ⟨s, hs, _⟩ := hF'.dense Y (by rfl) hF'.infinite_base
        exact ⟨s, hs⟩
      have hsub_single : F' ⊆ ({∅} : Set (Finset Nat)) := by
        intro s hs
        have hsF : s ∈ F := hsub hs
        rw [htriv] at hsF
        simpa using hsF
      have hF'eq : F' = ({∅} : Set (Finset Nat)) := by
        apply Set.Subset.antisymm
        · exact hsub_single
        · intro s hs
          have hs0 : s = ∅ := by simpa using hs
          rcases hF'nonempty with ⟨t, ht⟩
          have ht0 : t = ∅ := by simpa using hsub_single ht
          simpa [hs0, ht0] using ht
      refine ⟨X, subset_rfl, hF.infinite_base, ?_⟩
      rw [hF'eq, htriv]
      ext s
      constructor
      · intro hs
        have hs0 : s = ∅ := by simpa using hs
        subst s
        simp [FrontRestrict]
      · intro hs
        change s ∈ ({∅} : Set (Finset Nat)) ∧ ∀ n, n ∈ s → n ∈ X at hs
        simpa using hs.1
    · have hbase : FrontBase F = X := by
        rcases hF.base_condition with h | h
        · exact (htriv h).elim
        · exact h
      have hemptyF : (∅ : Finset Nat) ∉ F := by
        intro hempty
        apply htriv
        ext s
        constructor
        · intro hs
          have hs0 : s = ∅ := by
            by_contra hsne
            have hspos : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hsne
            let m := s.min' hspos
            have hm : m ∈ s := Finset.min'_mem s hspos
            have hinit : InitialSegment (∅ : Finset Nat) s := by
              right
              refine ⟨m, hm, ?_⟩
              ext k
              simp only [Finset.mem_filter]
              constructor
              · intro hk
                simp at hk
              · intro hk
                exact False.elim ((Nat.not_lt_of_ge (Finset.min'_le s k hk.1)) hk.2)
            have heq : (∅ : Finset Nat) = s :=
              hF.prefix_free hempty hs hinit
            exact hsne heq.symm
          simpa [hs0]
        · intro hs
          have hs0 : s = ∅ := by simpa using hs
          simpa [hs0] using hempty
      have hemptyF' : (∅ : Finset Nat) ∉ F' := by
        intro hempty
        exact hemptyF (hsub hempty)
      have hbaseF' : FrontBase F' = Y := by
        rcases hF'.base_condition with h | h
        · exfalso
          apply hemptyF'
          rw [h]
          simp
        · exact h
      have hYsubX : Y ⊆ X := by
        intro n hn
        have hnbase' : n ∈ FrontBase F' := by
          rw [hbaseF']
          exact hn
        have hnbase : n ∈ FrontBase F := by
          rcases hnbase' with ⟨s, hs, hns⟩
          exact ⟨s, hsub hs, hns⟩
        simpa [hbase] using hnbase
      refine ⟨Y, hYsubX, hF'.infinite_base, ?_⟩
      apply Set.Subset.antisymm
      · intro s hs
        change s ∈ F ∧ ∀ n, n ∈ s → n ∈ Y
        refine ⟨hsub hs, ?_⟩
        intro n hns
        have hnbase' : n ∈ FrontBase F' := ⟨s, hs, hns⟩
        rw [hbaseF'] at hnbase'
        exact hnbase'
      · intro s hs
        change s ∈ F ∧ ∀ n, n ∈ s → n ∈ Y at hs
        have hsF : s ∈ F := hs.1
        have hsY : ∀ n, n ∈ s → n ∈ Y := hs.2
        have hsne : s.Nonempty := by
          apply Finset.nonempty_iff_ne_empty.mpr
          intro hs0
          apply hemptyF
          simpa [hs0] using hsF
        let m := s.max' hsne
        have hm : m ∈ s := Finset.max'_mem s hsne
        let Tail : Set Nat := {k | k ∈ Y ∧ m < k}
        have hTail_eq : Tail = Y \ Set.Iic m := by
          ext k
          simp [Tail, Set.mem_Iic, not_le]
        have hTailInf : Tail.Infinite := by
          rw [hTail_eq]
          exact hF'.infinite_base.sdiff (Set.finite_Iic m)
        let U : Set Nat := (s : Set Nat) ∪ Tail
        have hUsub : U ⊆ Y := by
          intro k hk
          change k ∈ (s : Set Nat) ∨ k ∈ Tail at hk
          rcases hk with hkS | hkT
          · exact hsY k hkS
          · change k ∈ Y ∧ m < k at hkT
            exact hkT.1
        have hUInf : U.Infinite := by
          apply Set.Infinite.mono (s := Tail) (t := U)
          · intro k hk
            change k ∈ (s : Set Nat) ∨ k ∈ Tail
            exact Or.inr hk
          · exact hTailInf
        obtain ⟨t, htF', htP⟩ := hF'.dense U hUsub hUInf
        rcases htP with ⟨n, hnU, htn⟩
        have hn_cases : n ∈ (s : Set Nat) ∨ n ∈ Tail := by
          change n ∈ (s : Set Nat) ∨ n ∈ Tail at hnU
          exact hnU
        have hcomp : InitialSegment s t ∨ InitialSegment t s := by
          rcases hn_cases with hnS | hnT
          · have hnm : n ≤ m := Finset.le_max' s n hnS
            right
            refine Or.inr ⟨n, hnS, ?_⟩
            ext k
            constructor
            · intro hk
              have hkU := (htn k).mp hk
              have hkUmem := hkU.1
              change k ∈ (s : Set Nat) ∨ k ∈ Tail at hkUmem
              rcases hkUmem with hkS | hkT
              · exact Finset.mem_filter.mpr ⟨hkS, hkU.2⟩
              · change k ∈ Y ∧ m < k at hkT
                have : False := by omega
                exact this.elim
            · intro hk
              have hk' := Finset.mem_filter.mp hk
              apply (htn k).mpr
              refine ⟨?_, hk'.2⟩
              change k ∈ (s : Set Nat) ∨ k ∈ Tail
              exact Or.inl hk'.1
          · change n ∈ Y ∧ m < n at hnT
            have hstsubset : s ⊆ t := by
              intro k hk
              have hkm : k ≤ m := Finset.le_max' s k hk
              apply (htn k).mpr
              refine ⟨?_, lt_of_le_of_lt hkm hnT.2⟩
              change k ∈ (s : Set Nat) ∨ k ∈ Tail
              exact Or.inl hk
            by_cases hts : t = s
            · left
              exact Or.inl hts.symm
            · left
              refine Or.inr ?_
              let d := t \ s
              have hd : d.Nonempty := by
                apply Finset.sdiff_nonempty.mpr
                intro htsub
                apply hts
                exact Finset.Subset.antisymm htsub hstsubset
              let q := d.min' hd
              have hq_d : q ∈ d := Finset.min'_mem d hd
              have hq_d' := Finset.mem_sdiff.mp hq_d
              have hq_t : q ∈ t := (Finset.mem_sdiff.mp hq_d).1
              refine ⟨q, hq_t, ?_⟩
              have hqTail : m < q := by
                have hqU := (htn q).mp hq_t
                have hqUmem := hqU.1
                change q ∈ (s : Set Nat) ∨ q ∈ Tail at hqUmem
                rcases hqUmem with hqS | hqT
                · exact (hq_d'.2 hqS).elim
                · change q ∈ Y ∧ m < q at hqT
                  exact hqT.2
              ext k
              constructor
              · intro hk
                have hkt : k ∈ t := hstsubset hk
                have hkm : k ≤ m := Finset.le_max' s k hk
                have hkq : k < q := lt_of_le_of_lt hkm hqTail
                exact Finset.mem_filter.mpr ⟨hkt, hkq⟩
              · intro hk
                have hk' := Finset.mem_filter.mp hk
                by_contra hks
                have hkd : k ∈ d := Finset.mem_sdiff.mpr ⟨hk'.1, hks⟩
                exact (Nat.not_lt_of_ge (Finset.min'_le d k hkd)) hk'.2
        rcases hcomp with hst | hts
        · have heq : s = t := hF.prefix_free hsF (hsub htF') hst
          rw [heq]
          exact htF'
        · have heq : t = s := hF.prefix_free (hsub htF') hsF hts
          rw [← heq]
          exact htF'
  · rintro ⟨Z, hZX, hZinf, hEq⟩
    refine ⟨Z, ?_⟩
    rw [hEq]
    exact FrontRestriction F X hF Z hZX hZinf
