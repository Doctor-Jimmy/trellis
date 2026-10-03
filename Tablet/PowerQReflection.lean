import Tablet.PowerFiniteOrbitConstancy
import Tablet.PowerCopiedOrbitDependence
import Tablet.PowerCopiedTerminalShift
import Tablet.PowerCopiedTerminalSupport
import Tablet.PowerCopiedFailureMove

universe u

-- [TABLET NODE: PowerQReflection]
theorem PowerQReflection {Q : Type u} (r : Q → Q → Prop)
    [IsPreorder Q r] (h : MultiSequence (PowerQ Q))
    (hloc : LocallyConstant h)
    (hbad : BadMultiSequence (PowerRel r) h) :
    ∃ g : MultiSequence Q,
      LocallyConstant g ∧ BadMultiSequence r g ∧
        ∀ x, g x ∈ PowerSupport (h x) := by
-- BODY
  classical
  have hterminal : ∀ x, ∃ q, ∃ k,
      PowerCopiedLeft r h x 0 k = .atom q := by
    intro x
    rcases PowerCopiedFiniteTerminal r h hbad x with
      ⟨k, q, q', hq, hq', hfinite⟩
    exact ⟨q, k, hq⟩
  let g : MultiSequence Q := fun x => Classical.choose (hterminal x)
  have hgterminal : ∀ x, ∃ k,
      PowerCopiedLeft r h x 0 k = .atom (g x) := by
    intro x
    dsimp [g]
    exact Classical.choose_spec (hterminal x)
  have hpersist : ∀ (x : IncSeq) (q : Q) (a b : Nat),
      PowerCopiedLeft r h x 0 a = .atom q → a ≤ b →
        PowerCopiedLeft r h x 0 b = .atom q := by
    intro x q a b ha hab
    refine Nat.le_induction (m := a)
      (P := fun b _ => PowerCopiedLeft r h x 0 b = .atom q) ha ?_ b hab
    intro n han ih
    have hm := (PowerCopiedFailureMove r h hbad x 0 n).2
    have hm' : PowerMove (.atom q)
        (PowerCopiedLeft r h x 0 (n + 1)) := by
      rw [← ih]
      exact hm
    simpa [PowerMove] using hm'
  have hunique : ∀ (x : IncSeq) (k : Nat) (q : Q),
      PowerCopiedLeft r h x 0 k = .atom q → q = g x := by
    intro x k q hq
    rcases hgterminal x with ⟨k', hq'⟩
    by_cases hkk' : k ≤ k'
    · have hqk' := hpersist x q k k' hq hkk'
      apply PowerQ.atom.inj
      exact hqk'.symm.trans hq'
    · have hk'k : k' ≤ k := by omega
      have hqk := hpersist x (g x) k' k hq' hk'k
      apply PowerQ.atom.inj
      exact hq.symm.trans hqk
  have hbad' : BadMultiSequence r g := by
    intro x
    rcases PowerCopiedFiniteTerminal r h hbad x with
      ⟨k, q, q', hq, hq', hfinite⟩
    have hqx : q = g x := hunique x k q hq
    have hshift : PowerCopiedLeft r h (ShiftMap x) 0 k = .atom q' := by
      calc
        PowerCopiedLeft r h (ShiftMap x) 0 k =
            PowerCopiedLeft r h x (0 + 1) k :=
          PowerCopiedShiftIdentity r h x 0 k
        _ = PowerCopiedLeft r h x 1 k := by simp
        _ = .atom q' := hq'
    have hqshift : q' = g (ShiftMap x) := hunique (ShiftMap x) k q' hshift
    have hfail := (PowerCopiedFailureMove r h hbad x 0 k).1
    have hnot : ¬ r q q' := by
      intro hqq'
      apply hfail
      rw [hq, hq']
      exact (PowerRelAtomAtom r q q').mpr hqq'
    intro hgg'
    apply hnot
    rw [hqx, hqshift]
    exact hgg'
  have hsupport : ∀ x, g x ∈ PowerSupport (h x) := by
    intro x
    rcases PowerCopiedFiniteTerminal r h hbad x with
      ⟨k, q, q', hq, hq', hfinite⟩
    have hqx : q = g x := hunique x k q hq
    have hsub := PowerCopiedSupport r h hbad x 0 k
    have hsub' : PowerSupport (.atom q) ⊆ PowerSupport (h x) := by
      simpa [PowerShiftIter, hq] using hsub
    rw [← hqx]
    exact hsub' (by simp [PowerSupport])
  have hloc' : LocallyConstant g := by
    intro x
    rcases PowerCopiedFiniteTerminal r h hbad x with
      ⟨k, q, q', hq, hq', hfinite⟩
    obtain ⟨N, hN⟩ := PowerFiniteOrbitConstancy h hloc x (k + 2)
    refine ⟨N, ?_⟩
    intro y hxy
    have horbit : ∀ j : Nat, j ≤ 0 + k + 2 →
        h (PowerShiftIter j y) = h (PowerShiftIter j x) := by
      intro j hj
      exact hN y hxy j (by omega)
    have hcopy := PowerCopiedOrbitDependence r h y x 0 k (by
      intro j hj
      exact horbit j (by omega))
    have hyq : PowerCopiedLeft r h y 0 k = .atom q := hcopy.trans hq
    have hgy : q = g y := hunique y k q hyq
    have hgx : q = g x := hunique x k q hq
    exact hgy.symm.trans hgx
  exact ⟨g, hloc', hbad', hsupport⟩
