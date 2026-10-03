import Tablet.HerCtblNodeClosure
import Tablet.HerCtblRel
import Tablet.HerCtblPowerIsPreorder
import Tablet.PowerRelNodeNode
import Tablet.PowerRelRefl

universe u

-- [TABLET NODE: HerCtblWqoIffWellFounded]
theorem HerCtblWqoIffWellFounded {Q : Type u} (r : Q → Q → Prop)
    [IsPreorder Q r] :
    WellQuasiOrdered (HerCtblRel r) ↔
      WellFounded (fun a b : HerCtblPower Q =>
        HerCtblRel r a b ∧ ¬ HerCtblRel r b a) := by
-- BODY
  constructor
  · exact WellQuasiOrdered.wellFounded
  · intro hwf
    by_contra hnwqo
    unfold WellQuasiOrdered at hnwqo
    push Not at hnwqo
    obtain ⟨a, hbad⟩ := hnwqo
    let T : Nat → HerCtblPower Q := fun n =>
      ⟨PowerQ.node (ULift.{u} Nat) inferInstance
          (fun k => (a (n + k.down)).1),
        HerCtblNodeClosure
          (I := ULift.{u} Nat) (fun k => a (n + k.down))⟩
    have hstep : ∀ n,
        (fun x y : HerCtblPower Q =>
          HerCtblRel r x y ∧ ¬ HerCtblRel r y x)
          (T (n + 1)) (T n) := by
      intro n
      constructor
      · change PowerRel r
          (.node (ULift.{u} Nat) inferInstance
            (fun k => (a (n + 1 + k.down)).1))
          (.node (ULift.{u} Nat) inferInstance
            (fun k => (a (n + k.down)).1))
        rw [PowerRelNodeNode]
        intro k
        refine ⟨ULift.up (k.down + 1), ?_⟩
        simpa only [ULift.down_up, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          PowerRelRefl r (a (n + 1 + k.down)).1
      · intro h
        change PowerRel r
            (.node (ULift.{u} Nat) inferInstance
              (fun k => (a (n + k.down)).1))
            (.node (ULift.{u} Nat) inferInstance
              (fun k => (a (n + 1 + k.down)).1)) at h
        rw [PowerRelNodeNode] at h
        obtain ⟨k, hk⟩ := h (ULift.up 0)
        change HerCtblRel r (a n) (a (n + 1 + k.down)) at hk
        exact hbad n (n + 1 + k.down) (by omega) hk
    exact (wellFounded_iff_isEmpty_descending_chain.mp hwf).false
      ⟨T, hstep⟩
