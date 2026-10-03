import Tablet.PowerWqoBadPairSequence
import Tablet.TripleHomogeneous
import Tablet.QuadrupleHomogeneous
import Tablet.InfiniteSetEnumeration
import Tablet.RadoOrder
import Tablet.RelationEmbedding

set_option maxHeartbeats 1000000

-- [TABLET NODE: RadoEmbedding]
theorem RadoEmbedding {Q : Type} (r : Q → Q → Prop) [IsPreorder Q r]
    (hQ : WellQuasiOrdered r)
    (hP : ¬ WellQuasiOrdered (SetDomination r)) :
    ∃ e : IncreasingPair → Q, RelationEmbedding RadoOrder r e := by
-- BODY
  obtain ⟨f, hf⟩ := (PowerWqoBadPairSequence r).mp hP
  classical
  let c3 : Finset Nat → Bool := fun s =>
    if ∃ (i j k : Nat) (hij : i < j) (hik : j < k),
        s = {i, j, k} ∧ r (f ⟨i, j, hij⟩) (f ⟨i, k, lt_trans hij hik⟩)
      then true else false
  have sorted3_unique : ∀ {u v t i j k : Nat}, u < v → v < t → i < j → j < k →
      ({u, v, t} : Finset Nat) = {i, j, k} → i = u ∧ j = v ∧ k = t := by
    intro u v t i j k huv hvt hij hjk hs
    have hu : u = i ∨ u = j ∨ u = k := by
      have h : u ∈ ({i, j, k} : Finset Nat) := by rw [← hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hv : v = i ∨ v = j ∨ v = k := by
      have h : v ∈ ({i, j, k} : Finset Nat) := by rw [← hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have ht : t = i ∨ t = j ∨ t = k := by
      have h : t ∈ ({i, j, k} : Finset Nat) := by rw [← hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hi : i = u ∨ i = v ∨ i = t := by
      have h : i ∈ ({u, v, t} : Finset Nat) := by rw [hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hj : j = u ∨ j = v ∨ j = t := by
      have h : j ∈ ({u, v, t} : Finset Nat) := by rw [hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hk : k = u ∨ k = v ∨ k = t := by
      have h : k ∈ ({u, v, t} : Finset Nat) := by rw [hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    rcases hu with hu | hu | hu <;>
      rcases hv with hv | hv | hv <;>
        rcases ht with ht | ht | ht <;>
          rcases hi with hi | hi | hi <;>
            rcases hj with hj | hj | hj <;>
              rcases hk with hk | hk | hk <;> omega
  have c3_of_rel {u v t : Nat} (huv : u < v) (hvt : v < t)
      (hrel : r (f ⟨u, v, huv⟩) (f ⟨u, t, by omega⟩)) :
      c3 {u, v, t} = true := by
    dsimp [c3]
    split
    · rfl
    · exfalso
      apply ‹¬ ∃ (i j k : Nat) (hij : i < j) (hik : j < k),
          ({u, v, t} : Finset Nat) = {i, j, k} ∧
          r (f ⟨i, j, hij⟩) (f ⟨i, k, lt_trans hij hik⟩)›
      exact ⟨u, v, t, huv, hvt, rfl, hrel⟩
  have rel_of_c3 {u v t : Nat} (huv : u < v) (hvt : v < t)
      (hc : c3 {u, v, t} = true) :
      r (f ⟨u, v, huv⟩) (f ⟨u, t, by omega⟩) := by
    dsimp [c3] at hc
    split at hc
    · obtain ⟨i, j, k, hij, hjk, hs, hrel⟩ := ‹∃ (i j k : Nat) (hij : i < j) (hik : j < k),
          ({u, v, t} : Finset Nat) = {i, j, k} ∧
          r (f ⟨i, j, hij⟩) (f ⟨i, k, lt_trans hij hik⟩)›
      obtain ⟨rfl, rfl, rfl⟩ := sorted3_unique huv hvt hij hjk hs
      exact hrel
    · simp at hc
  obtain ⟨N, hNN, hNinf, b3, hNhom⟩ :=
    TripleHomogeneous Set.univ Set.infinite_univ c3
  have hb3 : b3 = true := by
    cases b3 with
    | true => rfl
    | false =>
        obtain ⟨i, hiN⟩ := hNinf.nonempty
        let T : Set Nat := N \ Set.Iic i
        have hT : T.Infinite := by
          dsimp [T]
          exact hNinf.sdiff (Set.finite_Iic i)
        obtain ⟨x, hxT⟩ := InfiniteSetEnumeration T hT
        have hx_mem (n : Nat) : x n ∈ T := by
          rw [← hxT]
          exact ⟨n, rfl⟩
        have hi_lt (n : Nat) : i < x n := by
          exact Nat.lt_of_not_ge (by simpa [Set.mem_Iic] using (hx_mem n).2)
        let g : Nat → Q := fun n => f ⟨i, x n, hi_lt n⟩
        obtain ⟨u, v, huv, hrel⟩ := hQ g
        have hxu : x u ∈ N := (hx_mem u).1
        have hxv : x v ∈ N := (hx_mem v).1
        have hixu : i ≠ x u := Nat.ne_of_lt (hi_lt u)
        have hixv : i ≠ x v := Nat.ne_of_lt (hi_lt v)
        have hxuxv : x u ≠ x v := Nat.ne_of_lt (x.strictMono huv)
        have hc := hNhom {i, x u, x v} (by
          simp [Finset.card_insert_of_notMem, hixu, hixv, hxuxv])
          (by intro z hz; simp only [Finset.coe_insert, Finset.coe_singleton,
            Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
              rcases hz with rfl | rfl | rfl <;> assumption)
        have hctrue : c3 {i, x u, x v} = true := by
          apply c3_of_rel (hi_lt u) (x.strictMono huv)
          exact hrel
        rw [hctrue] at hc
        simp at hc
  let c4 : Finset Nat → Bool := fun s =>
    if ∃ (i j k l : Nat) (hij : i < j) (hjk : j < k) (hkl : k < l),
        s = {i, j, k, l} ∧ r (f ⟨i, j, hij⟩) (f ⟨k, l, hkl⟩)
      then true else false
  have sorted4_unique : ∀ {a b c d i j k l : Nat}, a < b → b < c → c < d →
      i < j → j < k → k < l →
      ({a, b, c, d} : Finset Nat) = {i, j, k, l} →
      i = a ∧ j = b ∧ k = c ∧ l = d := by
    intro a b c d i j k l hab hbc hcd hij hjk hkl hs
    have ha : a = i ∨ a = j ∨ a = k ∨ a = l := by
      have h : a ∈ ({i, j, k, l} : Finset Nat) := by rw [← hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hi : i = a ∨ i = b ∨ i = c ∨ i = d := by
      have h : i ∈ ({a, b, c, d} : Finset Nat) := by rw [hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hia : i = a := by
      rcases ha with ha | ha | ha | ha <;>
        rcases hi with hi | hi | hi | hi <;> omega
    subst i
    have hb : b = a ∨ b = j ∨ b = k ∨ b = l := by
      have h : b ∈ ({a, j, k, l} : Finset Nat) := by rw [← hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hj : j = a ∨ j = b ∨ j = c ∨ j = d := by
      have h : j ∈ ({a, b, c, d} : Finset Nat) := by rw [hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hjb : j = b := by
      rcases hb with hb | hb | hb | hb <;>
        rcases hj with hj | hj | hj | hj <;> omega
    subst j
    have hc : c = a ∨ c = b ∨ c = k ∨ c = l := by
      have h : c ∈ ({a, b, k, l} : Finset Nat) := by rw [← hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hk : k = a ∨ k = b ∨ k = c ∨ k = d := by
      have h : k ∈ ({a, b, c, d} : Finset Nat) := by rw [hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hkc : k = c := by
      rcases hc with hc | hc | hc | hc <;>
        rcases hk with hk | hk | hk | hk <;> omega
    subst k
    have hd : d = a ∨ d = b ∨ d = c ∨ d = l := by
      have h : d ∈ ({a, b, c, l} : Finset Nat) := by rw [← hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hl : l = a ∨ l = b ∨ l = c ∨ l = d := by
      have h : l ∈ ({a, b, c, d} : Finset Nat) := by rw [hs]; simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using h
    have hld : l = d := by
      rcases hd with hd | hd | hd | hd <;>
        rcases hl with hl | hl | hl | hl <;> omega
    exact ⟨rfl, rfl, rfl, hld⟩
  have c4_of_rel {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d)
      (hrel : r (f ⟨a, b, hab⟩) (f ⟨c, d, hcd⟩)) :
      c4 {a, b, c, d} = true := by
    dsimp [c4]
    split
    · rfl
    · exfalso
      apply ‹¬ ∃ (i j k l : Nat) (hij : i < j) (hjk : j < k) (hkl : k < l),
          ({a, b, c, d} : Finset Nat) = {i, j, k, l} ∧
          r (f ⟨i, j, hij⟩) (f ⟨k, l, hkl⟩)›
      exact ⟨a, b, c, d, hab, hbc, hcd, rfl, hrel⟩
  have rel_of_c4 {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d)
      (hc : c4 {a, b, c, d} = true) :
      r (f ⟨a, b, hab⟩) (f ⟨c, d, hcd⟩) := by
    dsimp [c4] at hc
    split at hc
    · obtain ⟨i, j, k, l, hij, hjk, hkl, hs, hrel⟩ :=
          ‹∃ (i j k l : Nat) (hij : i < j) (hjk : j < k) (hkl : k < l),
            ({a, b, c, d} : Finset Nat) = {i, j, k, l} ∧
            r (f ⟨i, j, hij⟩) (f ⟨k, l, hkl⟩)›
      obtain ⟨rfl, rfl, rfl, rfl⟩ := sorted4_unique hab hbc hcd hij hjk hkl hs
      exact hrel
    · simp at hc
  obtain ⟨M, hMN, hMinf, b4, hMhom⟩ := QuadrupleHomogeneous N hNinf c4
  have hb4 : b4 = true := by
    cases b4 with
    | true => rfl
    | false =>
        obtain ⟨z, hzM⟩ := InfiniteSetEnumeration M hMinf
        have hz_mem (n : Nat) : z n ∈ M := by
          rw [← hzM]
          exact ⟨n, rfl⟩
        have hpair (u : Nat) : 2 * u < 2 * u + 1 := by omega
        let g : Nat → Q := fun u =>
          f ⟨z (2 * u), z (2 * u + 1), z.strictMono (hpair u)⟩
        obtain ⟨u, v, huv, hrel⟩ := hQ g
        have hidx : 2 * u + 1 < 2 * v := by omega
        have hzt : z (2 * u) < z (2 * u + 1) := z.strictMono (hpair u)
        have hzuv : z (2 * u + 1) < z (2 * v) := z.strictMono hidx
        have hzv : z (2 * v) < z (2 * v + 1) := z.strictMono (hpair v)
        have hc := hMhom {z (2 * u), z (2 * u + 1), z (2 * v), z (2 * v + 1)}
          (by
            have hne1 : z (2 * u) ≠ z (2 * u + 1) := Nat.ne_of_lt hzt
            have hne2 : z (2 * u) ≠ z (2 * v) :=
              Nat.ne_of_lt (lt_trans hzt hzuv)
            have hne3 : z (2 * u) ≠ z (2 * v + 1) :=
              Nat.ne_of_lt (lt_trans (lt_trans hzt hzuv) hzv)
            have hne4 : z (2 * u + 1) ≠ z (2 * v) := Nat.ne_of_lt hzuv
            have hne5 : z (2 * u + 1) ≠ z (2 * v + 1) :=
              Nat.ne_of_lt (lt_trans hzuv hzv)
            have hne6 : z (2 * v) ≠ z (2 * v + 1) := Nat.ne_of_lt hzv
            simp [Finset.card_insert_of_notMem, hne1, hne2, hne3, hne4, hne5, hne6])
          (by
            intro q hq
            simp only [Finset.coe_insert, Set.mem_insert_iff,
              Finset.coe_singleton, Set.mem_singleton_iff] at hq
            rcases hq with rfl | rfl | rfl | rfl <;> exact hz_mem _)
        have hctrue : c4 {z (2 * u), z (2 * u + 1), z (2 * v), z (2 * v + 1)} = true := by
          apply c4_of_rel hzt hzuv hzv
          exact hrel
        rw [hctrue] at hc
        simp at hc
  have htriple_rel : ∀ {i j k : Nat} (hij : i < j) (hjk : j < k),
      i ∈ M → j ∈ M → k ∈ M →
      r (f ⟨i, j, hij⟩) (f ⟨i, k, lt_trans hij hjk⟩) := by
    intro i j k hij hjk hiM hjM hkM
    apply rel_of_c3 hij hjk
    have hc := hNhom {i, j, k}
      (by
        have hne1 : i ≠ j := Nat.ne_of_lt hij
        have hne2 : i ≠ k := Nat.ne_of_lt (lt_trans hij hjk)
        have hne3 : j ≠ k := Nat.ne_of_lt hjk
        simp [Finset.card_insert_of_notMem, hne1, hne2, hne3])
      (by
        intro q hq
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl
        · exact hMN hiM
        · exact hMN hjM
        · exact hMN hkM)
    simpa [hb3] using hc
  have hquad_rel : ∀ {i j k l : Nat} (hij : i < j) (hjk : j < k) (hkl : k < l),
      i ∈ M → j ∈ M → k ∈ M → l ∈ M →
      r (f ⟨i, j, hij⟩) (f ⟨k, l, hkl⟩) := by
    intro i j k l hij hjk hkl hiM hjM hkM hlM
    apply rel_of_c4 hij hjk hkl
    have hc := hMhom {i, j, k, l}
      (by
        have hne1 : i ≠ j := Nat.ne_of_lt hij
        have hne2 : i ≠ k := Nat.ne_of_lt (lt_trans hij hjk)
        have hne3 : i ≠ l := Nat.ne_of_lt (lt_trans (lt_trans hij hjk) hkl)
        have hne4 : j ≠ k := Nat.ne_of_lt hjk
        have hne5 : j ≠ l := Nat.ne_of_lt (lt_trans hjk hkl)
        have hne6 : k ≠ l := Nat.ne_of_lt hkl
        simp [Finset.card_insert_of_notMem, hne1, hne2, hne3, hne4, hne5, hne6])
      (by
        intro q hq
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact hiM
        · exact hjM
        · exact hkM
        · exact hlM)
    simpa [hb4] using hc
  have hMne : ∃ n : Nat, n ∈ M := hMinf.nonempty
  let a : Nat := Nat.find hMne
  have haM : a ∈ M := by
    exact Nat.find_spec hMne
  have hamin : ∀ n : Nat, n ∈ M → a ≤ n := by
    intro n hn
    exact Nat.find_min' hMne hn
  let X : Set Nat := M \ {a}
  have hXinf : X.Infinite := by
    dsimp [X]
    exact hMinf.sdiff (Set.finite_singleton a)
  obtain ⟨x, hxX⟩ := InfiniteSetEnumeration X hXinf
  have hxX_mem (n : Nat) : x n ∈ X := by
    rw [← hxX]
    exact ⟨n, rfl⟩
  have hxM (n : Nat) : x n ∈ M := (hxX_mem n).1
  have hax (n : Nat) : a < x n := by
    have hne : x n ≠ a := by
      intro h
      exact (hxX_mem n).2 (by simpa [h] using (Set.mem_singleton a))
    have hle : a ≤ x n := hamin (x n) (hxM n)
    omega
  have hmono : ∀ {u v s t : Nat} (huv : u < v) (hst : s < t),
      u ∈ M → v ∈ M → s ∈ M → t ∈ M →
      RadoOrder ⟨u, v, huv⟩ ⟨s, t, hst⟩ →
      r (f ⟨u, v, huv⟩) (f ⟨s, t, hst⟩) := by
    intro u v s t huv hst huM hvM hsM htM hord
    rcases hord with ⟨hus, hvt⟩ | hvs
    · by_cases hvt' : v = t
      · have hus' : u = s := hus
        subst s
        subst t
        exact refl_of r (f ⟨u, v, huv⟩)
      · have hvtlt : v < t := Nat.lt_of_le_of_ne hvt hvt'
        have hrel := htriple_rel huv hvtlt huM hvM htM
        change u = s at hus
        subst s
        exact hrel
    · exact hquad_rel huv hvs hst huM hvM hsM htM
  let e : IncreasingPair → Q := fun p =>
    f ⟨x p.first, x p.second, x.strictMono p.increasing⟩
  have hpres : ∀ p q : IncreasingPair, RadoOrder p q → r (e p) (e q) := by
    intro p q hpq
    rcases hpq with ⟨hfirst, hsecond⟩ | hsep
    · have hfirst' : x p.first = x q.first := congrArg x hfirst
      have hsecond' : x p.second ≤ x q.second := x.monotone hsecond
      have hm := hmono (x.strictMono p.increasing) (x.strictMono q.increasing)
        (hxM p.first) (hxM p.second) (hxM q.first) (hxM q.second)
        (Or.inl ⟨hfirst', hsecond'⟩)
      exact hm
    · have hpq' : x p.second < x q.first := x.strictMono hsep
      have hm := hmono (x.strictMono p.increasing) (x.strictMono q.increasing)
        (hxM p.first) (hxM p.second) (hxM q.first) (hxM q.second)
        (Or.inr hpq')
      exact hm
  have href : ∀ p q : IncreasingPair, r (e p) (e q) → RadoOrder p q := by
    intro p q hrel
    by_contra hnord
    have hsecond : q.first ≤ p.second := by
      by_contra hnot
      apply hnord
      exact Or.inr (Nat.lt_of_not_ge hnot)
    have hfail : p.first ≠ q.first ∨ q.second < p.second := by
      have hnotfirst : ¬ (p.first = q.first ∧ p.second ≤ q.second) := by
        intro h
        apply hnord
        exact Or.inl h
      by_cases hneq : p.first = q.first
      · right
        have hnle : ¬ p.second ≤ q.second := by
          intro hle
          exact hnotfirst ⟨hneq, hle⟩
        exact Nat.lt_of_not_ge hnle
      · exact Or.inl hneq
    rcases hfail with hfirstne | hlt
    · have hcases : p.first < q.first ∨ q.first < p.first :=
        Nat.lt_or_gt_of_ne hfirstne
      rcases hcases with hpk | hkp
      · have hleft : r (f ⟨x p.first, x q.first, x.strictMono hpk⟩)
            (f ⟨x p.first, x p.second, x.strictMono p.increasing⟩) := by
          apply hmono (x.strictMono hpk) (x.strictMono p.increasing)
            (hxM p.first) (hxM q.first) (hxM p.first) (hxM p.second)
          exact Or.inl ⟨rfl, x.monotone hsecond⟩
        have hcomp : r (f ⟨x p.first, x q.first, x.strictMono hpk⟩)
            (f ⟨x q.first, x q.second, x.strictMono q.increasing⟩) := by
          exact trans_of r hleft (by simpa [e] using hrel)
        exact (hf (x p.first) (x q.first) (x q.second)
          (x.strictMono hpk) (x.strictMono q.increasing)) hcomp
      · have hleft : r (f ⟨a, x q.first, hax q.first⟩)
            (f ⟨x p.first, x p.second, x.strictMono p.increasing⟩) := by
          apply hmono (hax q.first) (x.strictMono p.increasing)
            haM (hxM q.first) (hxM p.first) (hxM p.second)
          exact Or.inr (x.strictMono hkp)
        have hcomp : r (f ⟨a, x q.first, hax q.first⟩)
            (f ⟨x q.first, x q.second, x.strictMono q.increasing⟩) := by
          exact trans_of r hleft (by simpa [e] using hrel)
        exact (hf a (x q.first) (x q.second)
          (hax q.first) (x.strictMono q.increasing)) hcomp
    · have hn : p.second < p.second + 1 := Nat.lt_succ_self _
      have hqn : r (f ⟨x q.first, x q.second, x.strictMono q.increasing⟩)
          (f ⟨x p.second, x (p.second + 1), x.strictMono hn⟩) := by
        apply hmono (x.strictMono q.increasing) (x.strictMono hn)
          (hxM q.first) (hxM q.second) (hxM p.second) (hxM (p.second + 1))
        exact Or.inr (x.strictMono hlt)
      have hcomp : r (f ⟨x p.first, x p.second, x.strictMono p.increasing⟩)
          (f ⟨x p.second, x (p.second + 1), x.strictMono hn⟩) := by
        exact trans_of r (by simpa [e] using hrel) hqn
      exact (hf (x p.first) (x p.second) (x (p.second + 1))
        (x.strictMono p.increasing) (x.strictMono hn)) hcomp
  have hinj : Function.Injective e := by
    intro p q heq
    have hpq : RadoOrder p q := href p q (by
      rw [heq]
      exact refl_of r (e q))
    have hqp : RadoOrder q p := href q p (by
      rw [← heq]
      exact refl_of r (e p))
    have hpinc : p.first < p.second := p.increasing
    have hqinc : q.first < q.second := q.increasing
    rcases hpq with hpq | hpq
    · rcases hqp with hqp | hqp
      · have hfirsteq : p.first = q.first := hpq.1
        have hsecondeq : p.second = q.second := Nat.le_antisymm hpq.2 hqp.2
        cases p
        cases q
        simp_all only [IncreasingPair.mk.injEq]
      · exfalso
        omega
    · rcases hqp with hqp | hqp
      · exfalso
        omega
      · exfalso
        omega
  refine ⟨e, ?_⟩
  unfold RelationEmbedding
  let E : @RelEmbedding IncreasingPair Q RadoOrder r :=
    { toEmbedding := ⟨e, hinj⟩
      map_rel_iff' := by
        intro p q
        exact ⟨href p q, hpres p q⟩ }
  exact ⟨E, rfl⟩
