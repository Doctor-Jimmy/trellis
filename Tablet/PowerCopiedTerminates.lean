import Tablet.PowerCopiedFailureMove
import Tablet.PowerCopiedTerminalAt
import Tablet.PowerGameDescentWellFounded

universe u

-- [TABLET NODE: PowerCopiedTerminates]
theorem PowerCopiedTerminates {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q))
    (hbad : BadMultiSequence (PowerRel r) h) (x : IncSeq) (n : Nat) :
    ∃ k, PowerCopiedTerminalAt r h x n k := by
-- BODY
  let P : Nat → PowerQ Q × PowerQ Q := fun j =>
    (PowerCopiedLeft r h x n j, PowerCopiedLeft r h x (n + 1) j)
  have hPfail : ∀ j, ¬ PowerRel r (P j).1 (P j).2 := by
    intro j
    simpa [P] using (PowerCopiedFailureMove r h hbad x n j).1
  have hPmove : ∀ j,
      PowerMove (P j).1 (P (j + 1)).1 ∧
        PowerMove (P j).2 (P (j + 1)).2 := by
    intro j
    constructor
    · simpa [P] using (PowerCopiedFailureMove r h hbad x n j).2
    · simpa [P] using
        (PowerCopiedFailureMove r h hbad x (n + 1) j).2
  have hdescent : ∀ j,
      ¬ (∃ q q', (P j).1 = .atom q ∧ (P j).2 = .atom q') →
        PowerGameDescent (P (j + 1)) (P j) := by
    intro j hj
    have hm1 := (hPmove j).1
    have hm2 := (hPmove j).2
    cases hfirst : (P j).1 with
    | atom q =>
        cases hsecond : (P j).2 with
        | atom q' =>
            exact False.elim (hj ⟨q, q', hfirst, hsecond⟩)
        | node ι hs f =>
            right
            constructor
            · rw [hfirst]
              unfold PowerMove at hm1
              rw [hfirst] at hm1
              simp at hm1
              exact hm1
            · rw [hsecond]
              unfold PowerMove at hm2
              rw [hsecond] at hm2
              simp at hm2
              exact hm2
    | node ι hs f =>
        left
        rw [hfirst]
        unfold PowerMove at hm1
        rw [hfirst] at hm1
        simp at hm1
        exact hm1
  have hacc : Acc (@PowerGameDescent Q) (P 0) :=
    PowerGameDescentWellFounded.apply (P 0)
  have hresult : ∀ p, Acc (@PowerGameDescent Q) p →
      ∀ j, p = P j → ∃ k, PowerCopiedTerminalAt r h x n k := by
    intro p hp
    refine Acc.recOn hp ?_
    intro p hp ih
    intro j hpj
    by_cases hterm : ∃ q q', p.1 = .atom q ∧ p.2 = .atom q'
    · rcases hterm with ⟨q, q', hq, hq'⟩
      refine ⟨j, q, q', ?_, ?_⟩
      · simpa [P, hpj] using hq
      · simpa [P, hpj] using hq'
    · have hnot : ¬ (∃ q q', (P j).1 = .atom q ∧
          (P j).2 = .atom q') := by
        intro ht
        apply hterm
        rw [hpj]
        exact ht
      have hdP : PowerGameDescent (P (j + 1)) (P j) :=
        hdescent j hnot
      have hd : PowerGameDescent (P (j + 1)) p := by
        rw [hpj]
        exact hdP
      exact ih (P (j + 1)) hd (j + 1) rfl
  exact hresult (P 0) hacc 0 rfl
