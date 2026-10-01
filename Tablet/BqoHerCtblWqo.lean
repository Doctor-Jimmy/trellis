import Tablet.PowerQPresBqo
import Tablet.BqoImpliesWqo
import Tablet.BadMultiToNontrivialSuper
import Tablet.ConverseGame
import Tablet.TildeFSingleton
import Tablet.TildeFHerCtbl

universe u

-- [TABLET NODE: BqoHerCtblWqo]
theorem BqoHerCtblWqo {Q : Type u} (r : Q → Q → Prop)
    [IsPreorder Q r] :
    Bqo r ↔ WellQuasiOrdered (HerCtblRel r) := by
-- BODY
  constructor
  · intro hbqo a
    obtain ⟨m, n, hmn, hrel⟩ :=
      BqoImpliesWqo (PowerRel r) (PowerQPresBqo r hbqo)
        (fun k => (a k).1)
    exact ⟨m, n, hmn, hrel⟩
  · intro hwqo h hlc hbad
    obtain ⟨f, hfbad, htriv⟩ :=
      BadMultiToNontrivialSuper r h hlc hbad
    let a : Nat → HerCtblPower Q := fun k =>
      ⟨TildeFSingleton f htriv k,
        TildeFHerCtbl f ⟨{k}, FrontTreeSingleton _ f.front htriv k⟩⟩
    obtain ⟨m, n, hmn, hrel⟩ := hwqo a
    exact ConverseGame r f htriv hfbad m n hmn hrel
