import ClosedWalk

/- Modular cycle adjacency for the finite departure trace of an event list. -/
namespace ECC.CycleTrace
open ECC.CollisionBridge ECC.EventShuffle ECC.ClosedWalk

def state {q : Nat} {n : Fin q → Nat} : Vertex n → List (Event n) → Nat → Vertex n
  | v, [], _ => v
  | v, _ :: _, 0 => v
  | v, e :: es, k + 1 => state (update v e) es k

theorem state_zero {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) : state v es 0 = v := by cases es <;> rfl

theorem state_end {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) : state v es es.length = finish v es := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih => exact ih (update v e)

theorem before_get_state {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) (k : Nat) (hk : k < es.length) :
    (before v es)[k]'(by rw [before_length]; exact hk) = state v es k := by
  induction es generalizing v k with
  | nil => exact False.elim (Nat.not_lt_zero _ hk)
  | cons e es ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih (update v e) k (Nat.lt_of_succ_lt_succ hk)

theorem trace_eq_state {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) (t : Fin es.length) : trace v es t = state v es t.val :=
  before_get_state v es t.val t.isLt

theorem valid_iff_state_edges {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Vertex n) (es : List (Event n)) :
    Valid edge v es ↔ ∀ k, k < es.length →
      CartesianAdj edge (state v es k) (state v es (k + 1)) := by
  induction es generalizing v with
  | nil =>
    constructor
    · intro _ k hk
      exact False.elim (Nat.not_lt_zero _ hk)
    · intro _
      trivial
  | cons e es ih =>
    rcases e with ⟨a, u⟩
    constructor
    · rintro ⟨hhead, htail⟩ k hk
      cases k with
      | zero =>
        simpa only [state, state_zero] using
          (update_cartesian_iff edge v a u).mpr hhead
      | succ k => exact (ih (update v ⟨a, u⟩)).mp htail k (Nat.lt_of_succ_lt_succ hk)
    · intro h
      refine ⟨(update_cartesian_iff edge v a u).mp ?_, (ih (update v ⟨a, u⟩)).mpr ?_⟩
      · simpa only [state, state_zero] using h 0 (by simp)
      · intro k hk
        exact h (k + 1) (Nat.succ_lt_succ hk)

theorem trace_next_eq_state {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (es : List (Event n)) (hm : 0 < es.length) (hc : finish v es = v)
    (t : Fin es.length) : trace v es (Next hm t) = state v es (t.val + 1) := by
  rw [trace_eq_state]
  by_cases h : t.val + 1 < es.length
  · change state v es ((t.val + 1) % es.length) = _
    rw [Nat.mod_eq_of_lt h]
  · have hlast : t.val + 1 = es.length := by omega
    change state v es ((t.val + 1) % es.length) = _
    rw [hlast, Nat.mod_self, state_zero, state_end, hc]

theorem closed_trace_edges_iff {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Vertex n) (es : List (Event n)) (hm : 0 < es.length)
    (hc : finish v es = v) :
    (∀ t, CartesianAdj edge (trace v es t) (trace v es (Next hm t))) ↔
      Valid edge v es := by
  rw [valid_iff_state_edges]
  constructor
  · intro h k hk
    have ht := h ⟨k, hk⟩
    simpa only [trace_next_eq_state v es hm hc, trace_eq_state] using ht
  · intro h t
    rw [trace_next_eq_state v es hm hc, trace_eq_state]
    exact h t.val t.isLt

theorem closed_cycle_iff {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Vertex n) (es : List (Event n)) (hm : 0 < es.length)
    (hc : finish v es = v) :
    CycleEmbedding hm edge (trace v es) ↔
      3 ≤ es.length ∧ (before v es).Nodup ∧ Valid edge v es := by
  unfold CycleEmbedding
  rw [trace_injective_iff_nodup, closed_trace_edges_iff edge v es hm hc]

theorem closed_cycle_iff_factor_walks {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Vertex n) (es : List (Event n)) (hm : 0 < es.length)
    (hc : finish v es = v) :
    CycleEmbedding hm edge (trace v es) ↔
      3 ≤ es.length ∧ (before v es).Nodup ∧
        ∀ a, FactorWalk edge a (v a) (project es a) := by
  rw [closed_cycle_iff edge v es hm hc, valid_iff_factor_walks]

/- A self-contained criterion: neither side silently assumes closure. -/
theorem cycle_data_iff {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Vertex n) (es : List (Event n)) (hm : 0 < es.length) :
    (CycleEmbedding hm edge (trace v es) ∧ finish v es = v) ↔
      3 ≤ es.length ∧ (before v es).Nodup ∧
        ∀ a, FactorWalk edge a (v a) (project es a) ∧
          advance (v a) (project es a) = v a := by
  constructor
  · rintro ⟨hcycle, hc⟩
    have h := (closed_cycle_iff edge v es hm hc).mp hcycle
    exact ⟨h.1, h.2.1, (closed_valid_iff edge v es).mp ⟨h.2.2, hc⟩⟩
  · rintro ⟨hlen, hinj, hfactors⟩
    have h := (closed_valid_iff edge v es).mpr hfactors
    exact ⟨(closed_cycle_iff edge v es hm h.2).mpr ⟨hlen, hinj, h.1⟩, h.2⟩

#print axioms state_zero
#print axioms state_end
#print axioms before_get_state
#print axioms trace_eq_state
#print axioms valid_iff_state_edges
#print axioms trace_next_eq_state
#print axioms closed_trace_edges_iff
#print axioms closed_cycle_iff
#print axioms closed_cycle_iff_factor_walks
#print axioms cycle_data_iff

end ECC.CycleTrace
