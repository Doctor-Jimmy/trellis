import Tablet.Front
import Tablet.PrefixTree
import Tablet.ProperInitialSegment

-- [TABLET NODE: FrontTreeWellFounded]
theorem FrontTreeWellFounded (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) :
    WellFounded (fun u v : {s : Finset Nat // s ∈ PrefixTree F} =>
      ProperInitialSegment v.1 u.1) := by
-- BODY
  classical
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨?_⟩
  intro hchain
  rcases hchain with ⟨f, hf⟩
  have hstep : ∀ n, ProperInitialSegment (f n).1 (f (n + 1)).1 := by
    intro n
    exact hf n
  have hsub_initial : ∀ {a b : Finset Nat},
      InitialSegment a b → a ⊆ b := by
    intro a b hab
    rcases hab with rfl | ⟨n, hn, rfl⟩
    · exact Finset.Subset.rfl
    · exact Finset.filter_subset _ _
  have hstrict : ∀ n, (f n).1 ⊂ (f (n + 1)).1 := by
    intro n
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub_initial (hstep n).1, (hstep n).2⟩
  have hcardstep : ∀ n, (f n).1.card < (f (n + 1)).1.card := by
    intro n
    exact Finset.card_lt_card (hstrict n)
  have hcard : ∀ n, n ≤ (f n).1.card := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        have hs := hcardstep n
        omega
  have hmono : ∀ ⦃m n⦄, m ≤ n → (f m).1 ⊆ (f n).1 := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact Finset.Subset.rfl
    | succ n hmn ih =>
        exact ih.trans (hsub_initial (hstep n).1)
  have htrans : ∀ {a b c : Finset Nat},
      InitialSegment a b → InitialSegment b c → InitialSegment a c := by
    intro a b c hab hbc
    rcases hab with rfl | ⟨n, hn, rfl⟩
    · exact hbc
    · rcases hbc with rfl | ⟨m, hm, rfl⟩
      · exact Or.inr ⟨n, hn, rfl⟩
      · right
        refine ⟨n, ?_, ?_⟩
        · exact (Finset.mem_filter.mp hn).1
        · apply Finset.ext
          intro x
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨hx, hxm⟩, hxn⟩
            exact ⟨hx, hxn⟩
          · rintro ⟨hx, hxn⟩
            exact ⟨⟨hx, lt_trans hxn (Finset.mem_filter.mp hn).2⟩, hxn⟩
  let Y : Set Nat := ⋃ n : Nat, ((f n).1 : Set Nat)
  have hsubY : ∀ n, ((f n).1 : Set Nat) ⊆ Y := by
    intro n x hx
    change x ∈ ⋃ n : Nat, ((f n).1 : Set Nat)
    exact Set.mem_iUnion.2 ⟨n, hx⟩
  have hYinf : Y.Infinite := by
    by_contra hY
    have hYfin : Y.Finite := Set.not_infinite.mp hY
    let B : Finset Nat := hYfin.toFinset
    have hsubB : ∀ n, (f n).1 ⊆ B := by
      intro n
      exact hYfin.subset_toFinset.2 (hsubY n)
    have hcardB : ∀ n, (f n).1.card ≤ B.card := by
      intro n
      exact Finset.card_le_card (hsubB n)
    have hc := hcard (B.card + 1)
    have hc' := hcardB (B.card + 1)
    omega
  rcases hF.base_condition with htriv | hbase
  · have h0 : (f 0).1 = ∅ := by
      rcases (f 0).2 with ⟨t, htF, ht⟩
      rw [htriv] at htF
      subst t
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      rcases hne with ⟨x, hx⟩
      simpa using hsub_initial ht hx
    have h1 : (f 1).1 = ∅ := by
      rcases (f 1).2 with ⟨t, htF, ht⟩
      rw [htriv] at htF
      subst t
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      rcases hne with ⟨x, hx⟩
      simpa using hsub_initial ht hx
    exact (hstep 0).2 (h0.trans h1.symm)
  · have hbase' : Y ⊆ X := by
      intro y hy
      rcases Set.mem_iUnion.1 hy with ⟨n, hn⟩
      rcases (f n).2 with ⟨t, htF, ht⟩
      rw [← hbase]
      exact ⟨t, htF, hsub_initial ht hn⟩
    obtain ⟨s, hsF, hsY⟩ := hF.dense Y hbase' hYinf
    rcases hsY with ⟨a, haY, hasY⟩
    have hcapture : ∀ (s : Finset Nat),
        (∀ x ∈ s, x ∈ Y) → ∃ N, s ⊆ (f N).1 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          intro hs
          exact ⟨0, Finset.empty_subset _⟩
      | @insert a s ha ih =>
          intro hs
          obtain ⟨N, hNs⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
          obtain ⟨M, hMa⟩ := Set.mem_iUnion.1
            (hs a (Finset.mem_insert_self a s))
          refine ⟨max N M, ?_⟩
          apply Finset.insert_subset
          · exact hmono (Nat.le_max_right N M) hMa
          · exact hNs.trans (hmono (Nat.le_max_left N M))
    obtain ⟨N, hNs⟩ := hcapture s (fun x hx => (hasY x).mp hx |>.1)
    obtain ⟨A, hAa⟩ := Set.mem_iUnion.1 haY
    let K : Nat := max N A
    have hNK : N ≤ K := by
      dsimp [K]
      exact Nat.le_max_left _ _
    have hAK : A ≤ K := by
      dsimp [K]
      exact Nat.le_max_right _ _
    have hsubK : s ⊆ (f K).1 := hNs.trans (hmono hNK)
    have haK : a ∈ (f K).1 := hmono hAK hAa
    have hsfilter : s = (f K).1.filter (fun k => k < a) := by
      apply Finset.ext
      intro x
      constructor
      · intro hx
        exact Finset.mem_filter.mpr ⟨hsubK hx, (hasY x).mp hx |>.2⟩
      · intro hx
        have hx' := Finset.mem_filter.mp hx
        exact (hasY x).mpr ⟨hsubY K hx'.1, hx'.2⟩
    have hsInit : InitialSegment s (f K).1 := by
      rw [hsfilter]
      exact Or.inr ⟨a, haK, rfl⟩
    rcases (f K).2 with ⟨t, htF, hUt⟩
    have hst : InitialSegment s t := htrans hsInit hUt
    have hst_eq : s = t := hF.prefix_free hsF htF hst
    have ha_not_s : a ∉ s := by
      intro ha_s
      exact (Nat.lt_irrefl a) ((hasY a).mp ha_s).2
    have ha_t : a ∈ t := hsub_initial hUt haK
    exact ha_not_s (hst_eq.symm ▸ ha_t)
