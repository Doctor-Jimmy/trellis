import Tablet.FrontBridge
import Tablet.FrontTreeSingleton
import Tablet.FrontTreeOrderedExtension

-- [TABLET NODE: FrontBridgeInit]
theorem FrontBridgeInit (F : Set (Finset Nat))
    (hF : Front F Set.univ) (htriv : ∅ ∉ F) {m n : Nat} (hmn : m < n) :
    FrontBridge F ({m} : Finset Nat) ({n} : Finset Nat)
      ({m, n} : Finset Nat) := by
-- BODY
  classical
  rw [FrontBridge]
  have hm_tree : ({m} : Finset Nat) ∈ PrefixTree F :=
    FrontTreeSingleton F hF htriv m
  have hn_tree : ({n} : Finset Nat) ∈ PrefixTree F :=
    FrontTreeSingleton F hF htriv n
  have hpair : insert n ({m} : Finset Nat) = ({m, n} : Finset Nat) := by
    ext k
    simp [or_comm]
  have hleft_init : InitialSegment ({m} : Finset Nat) (insert n ({m} : Finset Nat)) := by
    right
    refine ⟨n, by simp, ?_⟩
    ext k
    simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_insert]
    omega
  have htail : FrontBridgeTail (insert n ({m} : Finset Nat)) = ({n} : Finset Nat) := by
    ext k
    simp only [FrontBridgeTail, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, q, hq, hqk⟩
      rcases hk with hk | hk
      · exact hk
      · rcases hq with hq | hq <;> omega
    · intro hk
      subst k
      refine ⟨Or.inl rfl, m, Or.inr rfl, hmn⟩
  have hleft_u : InitialSegment ({m} : Finset Nat) ({m, n} : Finset Nat) := by
    rw [← hpair]
    exact hleft_init
  have htail_u : FrontBridgeTail ({m, n} : Finset Nat) = ({n} : Finset Nat) := by
    rw [← hpair]
    exact htail
  have hproper : ProperInitialSegment ({m} : Finset Nat) (insert n ({m} : Finset Nat)) := by
    refine ⟨hleft_init, ?_⟩
    intro heq
    have hnmem : n ∈ insert n ({m} : Finset Nat) := Finset.mem_insert_self n {m}
    rw [← heq] at hnmem
    have hnm : n = m := by simpa using hnmem
    exact (Nat.ne_of_gt hmn) hnm
  refine ⟨hm_tree, hn_tree, by simp, by simp, ?_, ?_, ?_, ?_⟩
  · intro hsF
    exact hleft_u
  · intro hsF
    refine ⟨n, ?_, ?_, ?_⟩
    · exact hproper
    · ext k
      simp [Finset.pair_comm]
    · rw [← hpair]
      exact FrontTreeOrderedExtension F hF ({m} : Finset Nat) hm_tree hsF n hproper
  · intro htF
    exact Or.inl htail_u.symm
  · intro htF
    exact htail_u.symm
