import Tablet.PowerRelRefl

universe u

-- [TABLET NODE: PowerRelTrans]
theorem PowerRelTrans {Q : Type u} (r : Q → Q → Prop) [IsPreorder Q r]
    (x y z : PowerQ Q) :
    PowerRel r x y → PowerRel r y z → PowerRel r x z := by
-- BODY
  have wf : WellFounded
      (Prod.Lex (@PowerChild Q)
        (Prod.Lex (@PowerChild Q) (@PowerChild Q))) := by
    exact WellFounded.prod_lex PowerChildWellFounded
      (WellFounded.prod_lex PowerChildWellFounded PowerChildWellFounded)
  refine wf.induction (C := fun p : PowerQ Q × (PowerQ Q × PowerQ Q) =>
      PowerRel r p.1 p.2.1 → PowerRel r p.2.1 p.2.2 → PowerRel r p.1 p.2.2)
    (x, (y, z)) ?_
  intro p ih
  rcases p with ⟨x, y, z⟩
  change PowerRel r x y → PowerRel r y z → PowerRel r x z
  cases x with
  | atom a =>
    cases y with
    | atom b =>
      cases z with
      | atom c =>
        intro hab hbc
        have hab' : r a b := (PowerRelAtomAtom r a b).mp hab
        have hbc' : r b c := (PowerRelAtomAtom r b c).mp hbc
        exact (PowerRelAtomAtom r a c).mpr (IsTrans.trans a b c hab' hbc')
      | node κ hk g =>
        intro hab hbc
        rw [PowerRelAtomNode] at hbc ⊢
        obtain ⟨k, hbk⟩ := hbc
        exact ⟨k, ih (PowerQ.atom a, (PowerQ.atom b, g k))
          (Prod.Lex.right _ (Prod.Lex.right _
          (show @PowerChild Q (g k) (.node κ hk g) from ⟨k, rfl⟩))) hab hbk⟩
    | node ι hi f =>
      cases z with
      | atom c =>
        intro hab hbc
        rw [PowerRelAtomNode] at hab
        rw [PowerRelNodeAtom] at hbc
        obtain ⟨i, hai⟩ := hab
        have hdesc : Prod.Lex (@PowerChild Q)
            (Prod.Lex (@PowerChild Q) (@PowerChild Q))
            (PowerQ.atom a, (f i, PowerQ.atom c))
            (PowerQ.atom a, (PowerQ.node ι hi f, PowerQ.atom c)) :=
          Prod.Lex.right _ (Prod.Lex.left _ _
            (show @PowerChild Q (f i) (.node ι hi f) from ⟨i, rfl⟩))
        have hstep : PowerRel r (PowerQ.atom a) (PowerQ.atom c) :=
          ih (PowerQ.atom a, (f i, PowerQ.atom c)) hdesc hai (hbc i)
        exact hstep
      | node κ hk g =>
        intro hab hbc
        rw [PowerRelAtomNode] at hab
        rw [PowerRelNodeNode] at hbc
        rw [PowerRelAtomNode]
        obtain ⟨i, hai⟩ := hab
        obtain ⟨j, hij⟩ := hbc i
        have hdesc : Prod.Lex (@PowerChild Q)
            (Prod.Lex (@PowerChild Q) (@PowerChild Q))
            (PowerQ.atom a, (f i, g j))
            (PowerQ.atom a, (PowerQ.node ι hi f, PowerQ.node κ hk g)) :=
          Prod.Lex.right _ (Prod.Lex.left _ _
            (show @PowerChild Q (f i) (.node ι hi f) from ⟨i, rfl⟩))
        have hstep : PowerRel r (PowerQ.atom a) (g j) :=
          ih (PowerQ.atom a, (f i, g j)) hdesc hai hij
        exact ⟨j, hstep⟩
  | node ι hi f =>
    cases y with
    | atom b =>
      cases z with
      | atom c =>
        intro hab hbc
        rw [PowerRelNodeAtom] at hab
        rw [PowerRelNodeAtom]
        intro i
        have hdesc : Prod.Lex (@PowerChild Q)
            (Prod.Lex (@PowerChild Q) (@PowerChild Q))
            (f i, (PowerQ.atom b, PowerQ.atom c))
            (PowerQ.node ι hi f, (PowerQ.atom b, PowerQ.atom c)) :=
          Prod.Lex.left _ _
            (show @PowerChild Q (f i) (.node ι hi f) from ⟨i, rfl⟩)
        have hstep : PowerRel r (f i) (PowerQ.atom c) :=
          ih (f i, (PowerQ.atom b, PowerQ.atom c)) hdesc (hab i) hbc
        exact hstep
      | node κ hk g =>
        intro hab hbc
        rw [PowerRelNodeAtom] at hab
        rw [PowerRelAtomNode] at hbc
        rw [PowerRelNodeNode]
        obtain ⟨j, hbcj⟩ := hbc
        intro i
        have hdesc : Prod.Lex (@PowerChild Q)
            (Prod.Lex (@PowerChild Q) (@PowerChild Q))
            (f i, (PowerQ.atom b, g j))
            (PowerQ.node ι hi f, (PowerQ.atom b, PowerQ.node κ hk g)) :=
          Prod.Lex.left _ _
            (show @PowerChild Q (f i) (.node ι hi f) from ⟨i, rfl⟩)
        have hstep : PowerRel r (f i) (g j) :=
          ih (f i, (PowerQ.atom b, g j)) hdesc (hab i) hbcj
        exact ⟨j, hstep⟩
    | node κ hk g =>
      cases z with
      | atom c =>
        intro hab hbc
        rw [PowerRelNodeNode] at hab
        rw [PowerRelNodeAtom] at hbc
        rw [PowerRelNodeAtom]
        intro i
        obtain ⟨j, hij⟩ := hab i
        have hdesc : Prod.Lex (@PowerChild Q)
            (Prod.Lex (@PowerChild Q) (@PowerChild Q))
            (f i, (g j, PowerQ.atom c))
            (PowerQ.node ι hi f, (PowerQ.node κ hk g, PowerQ.atom c)) :=
          Prod.Lex.left _ _
            (show @PowerChild Q (f i) (.node ι hi f) from ⟨i, rfl⟩)
        have hstep : PowerRel r (f i) (PowerQ.atom c) :=
          ih (f i, (g j, PowerQ.atom c)) hdesc hij (hbc j)
        exact hstep
      | node ν hν k =>
        intro hab hbc
        rw [PowerRelNodeNode] at hab
        rw [PowerRelNodeNode] at hbc
        rw [PowerRelNodeNode]
        intro i
        obtain ⟨j, hij⟩ := hab i
        obtain ⟨l, hjl⟩ := hbc j
        have hdesc : Prod.Lex (@PowerChild Q)
            (Prod.Lex (@PowerChild Q) (@PowerChild Q))
            (f i, (g j, k l))
            (PowerQ.node ι hi f, (PowerQ.node κ hk g, PowerQ.node ν hν k)) :=
          Prod.Lex.left _ _
            (show @PowerChild Q (f i) (.node ι hi f) from ⟨i, rfl⟩)
        have hstep : PowerRel r (f i) (k l) :=
          ih (f i, (g j, k l)) hdesc hij hjl
        exact ⟨l, hstep⟩
