import Std

/- Connectedness is the usual finite cut definition: every Boolean coloring
   constant along crossing edges is constant. All cuts are explicitly finite;
   no imported connected-pairing theorem or enumeration oracle is used. -/
namespace ECC.ChordConnectivity

macro "finite_omega" : tactic => `(tactic| (
  repeat' first | apply Iff.intro | apply And.intro | intro
  all_goals (try simp only [Decidable.iff_iff_and_or_not_and_not, not_or,
    Decidable.not_and_iff_or_not] at *)
  all_goals omega))

structure Diagram (n L : Nat) where
  lo : Fin n → Nat
  hi : Fin n → Nat
  ordered : ∀ a, lo a < hi a
  bounded : ∀ a, hi a < L
  cover : ∀ p, p < L → ∃ a, lo a = p ∨ hi a = p
  disjoint : ∀ a b, a ≠ b →
    lo a ≠ lo b ∧ lo a ≠ hi b ∧ hi a ≠ lo b ∧ hi a ≠ hi b

def Cross {n L} (D : Diagram n L) (a b : Fin n) : Prop :=
  (D.lo a < D.lo b ∧ D.lo b < D.hi a ∧ D.hi a < D.hi b) ∨
  (D.lo b < D.lo a ∧ D.lo a < D.hi b ∧ D.hi b < D.hi a)
instance {n L} (D : Diagram n L) (a b) : Decidable (Cross D a b) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)))

def Invariant {n L} (D : Diagram n L) (c : Fin n → Bool) : Prop :=
  ∀ a b, Cross D a b → c a = c b
instance {n L} (D : Diagram n L) (c) : Decidable (Invariant D c) :=
  inferInstanceAs (Decidable (∀ a b, Cross D a b → c a = c b))

def Connected {n L} (D : Diagram n L) : Prop :=
  ∀ c, Invariant D c → ∀ a b, c a = c b

def ClosedInterval {n L} (D : Diagram n L) (s t : Nat) : Prop :=
  ∀ a, (s ≤ D.lo a ∧ D.lo a < t) ↔ (s ≤ D.hi a ∧ D.hi a < t)

def NoInterval {n L} (D : Diagram n L) : Prop :=
  ∀ s t, s < t → t < L → ¬ ClosedInterval D s t

-- This finite cut inventory is independent of any matching inventory.
def colors : (n : Nat) → List (Fin n → Bool)
  | 0 => [fun i => Fin.elim0 i]
  | n+1 => (colors n).flatMap fun c => [Fin.cases false c, Fin.cases true c]

theorem mem_colors {n} (c : Fin n → Bool) : c ∈ colors n := by
  induction n with
  | zero =>
    have h : c = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
    simp [colors, h]
  | succ n ih =>
    apply List.mem_flatMap.2
    refine ⟨fun i => c i.succ, ih _, ?_⟩
    have h : c = Fin.cases (c 0) (fun i => c i.succ) := by
      funext i
      exact Fin.cases (by rfl) (fun _ => by rfl) i
    rw [h]
    cases c 0 <;> simp

def component {n L} (D : Diagram n L) (root a : Fin n) : Bool :=
  (colors n).all fun c => decide (Invariant D c → c root = c a)

theorem component_iff {n L} (D : Diagram n L) (root a) :
    component D root a = true ↔ ∀ c, Invariant D c → c root = c a := by
  simp only [component, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h c; exact h c (mem_colors c)
  · intro h c _; exact h c

theorem component_self {n L} (D : Diagram n L) (root) :
    component D root root = true :=
  (component_iff D root root).2 (fun _ _ => rfl)

theorem component_step {n L} (D : Diagram n L) (root a b)
    (ha : component D root a = true) (hab : Cross D a b) :
    component D root b = true := by
  apply (component_iff D root b).2
  intro c hc
  exact ((component_iff D root a).1 ha c hc).trans (hc a b hab)

theorem cross_symm {n L} (D : Diagram n L) (a b) :
    Cross D a b → Cross D b a := Or.symm

-- A chord not crossing x has either both endpoints inside x or neither.
theorem inside_pair {n L} (D : Diagram n L) (x y)
    (hne : x ≠ y) (hn : ¬ Cross D x y) :
    (D.lo x < D.lo y ∧ D.lo y < D.hi x) ↔
      (D.lo x < D.hi y ∧ D.hi y < D.hi x) := by
  have ho := D.ordered y
  have hd := D.disjoint x y hne
  simp only [Cross] at hn
  finite_omega

-- Two crossing chords which avoid x cannot lie on different sides of x.
theorem inside_step {n L} (D : Diagram n L) (x y z)
    (hy : x ≠ y) (hz : x ≠ z)
    (hxy : ¬ Cross D x y) (hxz : ¬ Cross D x z) (hyz : Cross D y z) :
    (D.lo x < D.lo y ∧ D.lo y < D.hi x) ↔
      (D.lo x < D.lo z ∧ D.lo z < D.hi x) := by
  have hp := inside_pair D x y hy hxy
  have hq := inside_pair D x z hz hxz
  simp only [Cross] at hyz
  finite_omega

-- Finite bounded minimization, proved here instead of using choice.
theorem least {P : Nat → Prop} [DecidablePred P] {b : Nat}
    (h : ∃ i, i < b ∧ P i) :
    ∃ i, i < b ∧ P i ∧ ∀ j, j < i → ¬ P j := by
  induction b with
  | zero => obtain ⟨i, hi, _⟩ := h; exact False.elim (Nat.not_lt_zero i hi)
  | succ b ih =>
    by_cases hpFin : ∃ i : Fin b, P i.val
    · have hp : ∃ i, i < b ∧ P i := by
        obtain ⟨i, hi⟩ := hpFin
        exact ⟨i.val, i.isLt, hi⟩
      exact let ⟨i, hi, hpi, hm⟩ := ih hp; ⟨i, Nat.lt_succ_of_lt hi, hpi, hm⟩
    · have hp : ¬ ∃ i, i < b ∧ P i := by
        rintro ⟨i, hi, hpi⟩
        exact hpFin ⟨⟨i, hi⟩, hpi⟩
      have hb : P b := by
          obtain ⟨i, hi, hpi⟩ := h
          by_cases hib : i < b
          · exact False.elim (hp ⟨i, hib, hpi⟩)
          · have : i = b := Nat.le_antisymm (Nat.le_of_lt_succ hi) (Nat.le_of_not_gt hib)
            simpa only [this] using hpi
      exact ⟨b, Nat.lt_succ_self b, hb, fun j hj hjp => hp ⟨j, hj, hjp⟩⟩

-- In the component containing endpoint zero, an outside chord encloses no
-- component endpoint. This is the noncrossing-component argument in full.
theorem outside_encloses_none {n L} (D : Diagram n L) (root x : Fin n)
    (hr : D.lo root = 0) (hx : component D root x ≠ true) :
    ∀ y, component D root y = true →
      ¬ (D.lo x < D.lo y ∧ D.lo y < D.hi x) ∧
      ¬ (D.lo x < D.hi y ∧ D.hi y < D.hi x) := by
  let c : Fin n → Bool := fun y =>
    decide (component D root y = true ∧ D.lo x < D.lo y ∧ D.lo y < D.hi x)
  have avoid : ∀ y, component D root y = true → x ≠ y ∧ ¬ Cross D x y := by
    intro y hy
    constructor
    · intro he; subst y; exact hx hy
    · intro he
      exact hx (component_step D root y x hy (cross_symm D x y he))
  have hc : Invariant D c := by
    intro y z hyz
    by_cases hy : component D root y = true
    · have hz := component_step D root y z hy hyz
      have he := inside_step D x y z (avoid y hy).1 (avoid z hz).1
        (avoid y hy).2 (avoid z hz).2 hyz
      simp only [c, hy, hz, true_and]
      exact (decide_eq_decide).2 he
    · have hz : component D root z ≠ true := by
        intro hz
        exact hy (component_step D root z y hz (cross_symm D y z hyz))
      simp [c, hy, hz]
  have hcroot : c root = false := by simp [c, hr]
  intro y hy
  have he := (component_iff D root y).1 hy c hc
  have hn : ¬ (D.lo x < D.lo y ∧ D.lo y < D.hi x) := by
    intro h
    have ht : c y = true := by simp [c, hy, h.1, h.2]
    rw [hcroot, ht] at he
    contradiction
  exact ⟨hn, fun h => hn ((inside_pair D x y (avoid y hy).1 (avoid y hy).2).2 h)⟩

-- An actual interval witness is constructed from a separating graph cut.
theorem separating_cut_interval {n L} (D : Diagram n L) (hL : 0 < L)
    (c : Fin n → Bool) (hc : Invariant D c) (u v : Fin n) (huv : c u ≠ c v) :
    ∃ s t, s < t ∧ t < L ∧ ClosedInterval D s t := by
  obtain ⟨root, hr⟩ := D.cover 0 hL
  have hr0 : D.lo root = 0 := by
    rcases hr with hr | hr
    · exact hr
    · have := D.ordered root; finite_omega
  have outside : ∃ x, component D root x ≠ true := by
    by_cases hu : c root = c u
    · refine ⟨v, ?_⟩
      intro hv
      exact huv (hu.symm.trans ((component_iff D root v).1 hv c hc))
    · exact ⟨u, fun h => hu ((component_iff D root u).1 h c hc)⟩
  let P : Nat → Prop := fun p => ∃ a : Fin n,
    (D.lo a = p ∨ D.hi a = p) ∧ component D root a ≠ true
  have hP : ∃ i, i < L ∧ P i := by
    obtain ⟨x, hx⟩ := outside
    exact ⟨D.lo x, Nat.lt_trans (D.ordered x) (D.bounded x), x, Or.inl rfl, hx⟩
  obtain ⟨s, hs, hsp, hmin⟩ := least hP
  obtain ⟨x, hxs, hx⟩ := hsp
  clear hP outside
  have hspos : 0 < s := by
    by_cases hn : 0 < s
    · exact hn
    · exfalso
      have hs0 : s = 0 := by finite_omega
      have hxr : x = root := by
        by_cases hne : x = root
        · exact hne
        · exfalso
          have hd := D.disjoint x root hne
          rcases hxs with hxs | hxs <;> finite_omega
      subst x
      exact hx (component_self D root)
  -- choose the first component endpoint after s, or the endpoint L.
  let Q : Nat → Prop := fun p => p = L ∨ (s < p ∧ ∃ a : Fin n,
    (D.lo a = p ∨ D.hi a = p) ∧ component D root a = true)
  obtain ⟨t, ht, htQ, htmin⟩ := least (P := Q) (b := L+1) ⟨L, Nat.lt_succ_self L, Or.inl rfl⟩
  have hst : s < t := by
    rcases htQ with he | ⟨he, _⟩
    · omega
    · exact he
  have htL : t ≤ L := Nat.le_of_lt_succ ht
  have between_out : ∀ y p, (D.lo y = p ∨ D.hi y = p) →
      s ≤ p → p < t → component D root y ≠ true := by
    intro y p hyp hsy hyt hy
    by_cases hsy' : s = p
    · have hxy : x = y := by
        by_cases hne : x = y
        · exact hne
        · exfalso
          have hd := D.disjoint x y hne
          rcases hxs with hxs | hxs <;> rcases hyp with hyp | hyp <;> finite_omega
      subst x; exact hx hy
    · exact htmin p hyt (Or.inr ⟨by finite_omega, y, hyp, hy⟩)
  have closed : ClosedInterval D s t := by
    intro y
    have hoy := D.ordered y
    constructor
    · rintro ⟨hsy, hyt⟩
      have hy := between_out y (D.lo y) (Or.inl rfl) hsy hyt
      refine ⟨by finite_omega, ?_⟩
      by_cases hn : D.hi y < t
      · exact hn
      · exfalso
        have hthi : t ≤ D.hi y := by finite_omega
        have htlt : t < L := by have := D.bounded y; finite_omega
        obtain ⟨z, hz, hzC⟩ := (htQ.resolve_left (by finite_omega)).2
        have hens := outside_encloses_none D root y hr0 hy z hzC
        have hne : y ≠ z := by intro he; subst z; exact hy hzC
        have hd := D.disjoint y z hne
        rcases hz with hz | hz <;> finite_omega
    · rintro ⟨hsy, hyt⟩
      refine ⟨?_, by finite_omega⟩
      by_cases hn : s ≤ D.lo y
      · exact hn
      · exfalso
        exact hmin (D.lo y) (by finite_omega)
          ⟨y, Or.inl rfl, between_out y (D.hi y) (Or.inr rfl) hsy hyt⟩
  -- If t=L use the complementary prefix [0,s), which excludes root wrap.
  by_cases htlt : t < L
  · exact ⟨s, t, hst, htlt, closed⟩
  · have htEq : t = L := by finite_omega
    refine ⟨0, s, hspos, hs, ?_⟩
    intro y
    have hb := D.bounded y
    have ho := D.ordered y
    have he := closed y
    rw [htEq] at he
    finite_omega

theorem connected_iff_no_interval {n L} (D : Diagram n L) (hL : 0 < L) :
    Connected D ↔ NoInterval D := by
  constructor
  · intro hc s t hst htL hi
    let c : Fin n → Bool := fun a => decide (s ≤ D.lo a ∧ D.lo a < t)
    have inv : Invariant D c := by
      intro a b hab
      have ha := hi a
      have hb := hi b
      simp only [Cross] at hab
      have he : (s ≤ D.lo a ∧ D.lo a < t) ↔ (s ≤ D.lo b ∧ D.lo b < t) := by finite_omega
      exact (decide_eq_decide).2 he
    obtain ⟨a, ha⟩ := D.cover s (by finite_omega)
    obtain ⟨b, hb⟩ := D.cover t htL
    have hca : c a = true := by
      have hp := hi a
      rcases ha with ha | ha <;> simp only [c, decide_eq_true_eq] <;> finite_omega
    have hcb : c b = false := by
      have hp := hi b
      rcases hb with hb | hb <;> simp only [c, decide_eq_false_iff_not] <;> finite_omega
    have he := hc c inv a b
    rw [hca, hcb] at he
    contradiction
  · intro hn c hc a b
    by_cases he : c a = c b
    · exact he
    · exfalso
      obtain ⟨s, t, hst, htL, hi⟩ := separating_cut_interval D hL c hc a b he
      exact hn s t hst htL hi

-- Word is represented by the two ordered occurrence positions of each label.
-- The cover/disjoint fields ensure exactly one label at each position.
def state {n L} (D : Diagram n L) (t : Nat) (a : Fin n) : Bool :=
  decide (D.lo a < t ∧ t ≤ D.hi a)

theorem state_collision {n L} (D : Diagram n L) (s t : Nat) (hst : s ≤ t) :
    (∀ a, state D s a = state D t a) ↔ ClosedInterval D s t := by
  constructor
  · intro h a
    have ha := h a
    have ho := D.ordered a
    simp only [state, decide_eq_decide] at ha
    finite_omega
  · intro h a
    have ha := h a
    have ho := D.ordered a
    simp only [state, decide_eq_decide]
    finite_omega

def CollisionFree {n L} (D : Diagram n L) : Prop :=
  ∀ s t : Fin L, (∀ a, state D s.val a = state D t.val a) → s = t

theorem collision_free_iff_connected {n L} (D : Diagram n L) (hL : 0 < L) :
    CollisionFree D ↔ Connected D := by
  rw [connected_iff_no_interval D hL]
  constructor
  · intro hi s t hst htL hclosed
    have he := hi ⟨s, by finite_omega⟩ ⟨t, htL⟩ ((state_collision D s t (by finite_omega)).2 hclosed)
    have hv : s = t := congrArg Fin.val he
    finite_omega
  · intro hn s t he
    apply Fin.ext
    by_cases hst : s.val < t.val
    · exact False.elim (hn s.val t.val hst t.isLt ((state_collision D _ _ (by finite_omega)).1 he))
    · by_cases hts : t.val < s.val
      · exact False.elim (hn t.val s.val hts s.isLt
          ((state_collision D _ _ (by finite_omega)).1 (fun a => (he a).symm)))
      · finite_omega

#print axioms mem_colors
#print axioms component_iff
#print axioms component_self
#print axioms component_step
#print axioms cross_symm
#print axioms inside_pair
#print axioms inside_step
#print axioms least
#print axioms outside_encloses_none
#print axioms separating_cut_interval
#print axioms connected_iff_no_interval
#print axioms state_collision
#print axioms collision_free_iff_connected
end ECC.ChordConnectivity
