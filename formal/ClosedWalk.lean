import EventShuffle

/- Finite factor-walk validity, endpoint closure and root normalization.
   Edge relations need not be symmetric or irreflexive: genuine changes are
   required explicitly, as they are in CartesianAdj. -/
namespace ECC.ClosedWalk
open ECC.CollisionBridge ECC.EventShuffle

def advance {α : Type} : α → List α → α
  | x, [] => x
  | _, y :: ys => advance y ys

def finish {q : Nat} {n : Fin q → Nat} : Vertex n → List (Event n) → Vertex n
  | v, [] => v
  | v, e :: es => finish (update v e) es

def before {q : Nat} {n : Fin q → Nat} : Vertex n → List (Event n) → List (Vertex n)
  | _, [] => []
  | v, e :: es => v :: before (update v e) es

def FactorWalk {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (a : Fin q) : Fin (n a) → List (Fin (n a)) → Prop
  | _, [] => True
  | x, y :: ys => (edge a x y ∧ x ≠ y) ∧ FactorWalk edge a y ys

def Valid {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop) :
    Vertex n → List (Event n) → Prop
  | _, [] => True
  | v, e :: es => (edge e.fst (v e.fst) e.snd ∧ v e.fst ≠ e.snd) ∧
      Valid edge (update v e) es

theorem update_self {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (a : Fin q) (u : Fin (n a)) : update v ⟨a, u⟩ a = u := by simp [update]

theorem update_other {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (a b : Fin q) (u : Fin (n a)) (h : a ≠ b) : update v ⟨a, u⟩ b = v b := by
  simp [update, Ne.symm h]

theorem finish_coordinate {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) (a : Fin q) :
    finish v es a = advance (v a) (project es a) := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨b, u⟩
    by_cases h : b = a
    · subst b
      simpa [finish, project, advance, update] using ih (update v ⟨a, u⟩)
    · simpa [finish, project, h, update_other v b a u h] using ih (update v ⟨b, u⟩)

theorem closure_iff {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) :
    finish v es = v ↔ ∀ a, advance (v a) (project es a) = v a := by
  constructor
  · intro h a
    rw [← finish_coordinate, h]
  · intro h
    funext a
    exact (finish_coordinate v es a).trans (h a)

theorem valid_iff_factor_walks {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Vertex n) (es : List (Event n)) :
    Valid edge v es ↔ ∀ a, FactorWalk edge a (v a) (project es a) := by
  induction es generalizing v with
  | nil => simp [Valid, project, FactorWalk]
  | cons e es ih =>
    rcases e with ⟨b, u⟩
    constructor
    · rintro ⟨step, tail⟩ a
      have ht := (ih (update v ⟨b, u⟩)).mp tail a
      by_cases h : b = a
      · subst b
        rw [project_head]
        exact ⟨step, by simpa [update] using ht⟩
      · simpa [project, h, update_other v b a u h] using ht
    · intro h
      have hb : (edge b (v b) u ∧ v b ≠ u) ∧ FactorWalk edge b u (project es b) := by
        simpa [project, FactorWalk] using h b
      refine ⟨hb.1, (ih (update v ⟨b, u⟩)).mpr ?_⟩
      intro a
      by_cases ha : b = a
      · subst b
        simpa [update] using hb.2
      · simpa [project, ha, update_other v b a u ha] using h a

theorem closed_valid_iff {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Vertex n) (es : List (Event n)) :
    (Valid edge v es ∧ finish v es = v) ↔
      ∀ a, FactorWalk edge a (v a) (project es a) ∧
        advance (v a) (project es a) = v a := by
  rw [valid_iff_factor_walks, closure_iff]
  constructor
  · exact fun h a => ⟨h.1 a, h.2 a⟩
  · exact fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩

theorem coordinate_step_update {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (a : Fin q) (u : Fin (n a)) (h : v a ≠ u) :
    CoordinateStep a v (update v ⟨a, u⟩) := by
  refine ⟨by simpa [update] using h, ?_⟩
  intro b hb
  simp [update, hb]

theorem valid_head_cartesian {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Vertex n) (e : Event n) (es : List (Event n)) (h : Valid edge v (e :: es)) :
    CartesianAdj edge v (update v e) := by
  rcases e with ⟨a, u⟩
  exact ⟨a, by simpa [update] using h.1.1, coordinate_step_update v a u h.1.2⟩

theorem replay_split {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) : replay v es = before v es ++ [finish v es] := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih => simpa [replay, before, finish] using congrArg (v :: ·) (ih (update v e))

theorem before_length {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) : (before v es).length = es.length := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih => simp [before, ih]

theorem replay_length {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) : (replay v es).length = es.length + 1 := by
  rw [replay_split, List.length_append, before_length]
  rfl

theorem before_eq_dropLast {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) : before v es = (replay v es).dropLast := by
  rw [replay_split, List.dropLast_concat]

theorem closed_replay_split {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) (h : finish v es = v) :
    replay v es = before v es ++ [v] := by rw [replay_split, h]

theorem update_cartesian_iff {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Vertex n) (a : Fin q) (u : Fin (n a)) :
    CartesianAdj edge v (update v ⟨a, u⟩) ↔ edge a (v a) u ∧ v a ≠ u := by
  constructor
  · rintro ⟨b, he, hs⟩
    have hb : b = a := by
      by_cases h : b = a
      · exact h
      · exact False.elim (hs.1 (by simp [update, h]))
    subst b
    simpa [update] using And.intro he hs.1
  · rintro ⟨he, hn⟩
    exact ⟨a, by simpa [update] using he, coordinate_step_update v a u hn⟩

def ProductWalk {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop) :
    Vertex n → List (Event n) → Prop
  | _, [] => True
  | v, e :: es => CartesianAdj edge v (update v e) ∧ ProductWalk edge (update v e) es

theorem product_walk_iff_valid {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Vertex n) (es : List (Event n)) : ProductWalk edge v es ↔ Valid edge v es := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a, u⟩
    change (CartesianAdj edge v (update v ⟨a, u⟩) ∧ _) ↔ _
    rw [update_cartesian_iff, ih]
    rfl

/- This realization equivalence is for closed walks, not simple cycles. -/
theorem closed_walk_realizable_iff {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Vertex n) (word : List (Fin q)) (queues : Queues n) :
    (∃ es, axes es = word ∧ project es = queues ∧
      ProductWalk edge v es ∧ finish v es = v) ↔
    Compatible word queues ∧ ∀ a, FactorWalk edge a (v a) (queues a) ∧
      advance (v a) (queues a) = v a := by
  constructor
  · rintro ⟨es, rfl, rfl, hw, hc⟩
    exact ⟨projection_compatible es,
      (closed_valid_iff edge v es).mp ⟨(product_walk_iff_valid edge v es).mp hw, hc⟩⟩
  · rintro ⟨hcompatible, hclosed⟩
    obtain ⟨es, hword, hqueues⟩ := compatible_reconstruction word queues hcompatible
    have h := (closed_valid_iff edge v es).mpr (by simpa only [hqueues] using hclosed)
    exact ⟨es, hword, hqueues, (product_walk_iff_valid edge v es).mpr h.1, h.2⟩

def trace {q : Nat} {n : Fin q → Nat} (v : Vertex n) (es : List (Event n))
    (t : Fin es.length) : Vertex n :=
  (before v es)[t.val]'(by rw [before_length]; exact t.isLt)

theorem trace_injective_iff_nodup {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) : TraceInjective (trace v es) ↔ (before v es).Nodup := by
  constructor
  · intro h
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj heq
    have hi' : i < es.length := by rwa [before_length] at hi
    have hj' : j < es.length := by rwa [before_length] at hj
    exact congrArg Fin.val (h ⟨i, hi'⟩ ⟨j, hj'⟩ heq)
  · intro h s t heq
    apply Fin.ext
    exact h.eq_of_getElem_eq _ _ heq

theorem before_transitions {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (records : List (Fin q × Vertex n)) (h : Coherent v records) :
    before v (transitionEvents records) = (v :: records.map Prod.snd).dropLast := by
  rw [before_eq_dropLast, replay_transitions v records h]

theorem closed_replay_not_nodup {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) (hne : es ≠ []) (hc : finish v es = v) :
    ¬ (replay v es).Nodup := by
  intro h
  rw [closed_replay_split v es hc, List.nodup_append] at h
  have hv : v ∈ before v es := by
    cases es with
    | nil => exact False.elim (hne rfl)
    | cons e es => exact List.mem_cons_self
  exact h.2.2 v hv v (List.mem_cons_self) rfl

#print axioms update_self
#print axioms update_other
#print axioms finish_coordinate
#print axioms closure_iff
#print axioms valid_iff_factor_walks
#print axioms closed_valid_iff
#print axioms coordinate_step_update
#print axioms valid_head_cartesian
#print axioms replay_split
#print axioms before_length
#print axioms replay_length
#print axioms before_eq_dropLast
#print axioms closed_replay_split
#print axioms update_cartesian_iff
#print axioms product_walk_iff_valid
#print axioms closed_walk_realizable_iff
#print axioms trace_injective_iff_nodup
#print axioms before_transitions
#print axioms closed_replay_not_nodup

end ECC.ClosedWalk
