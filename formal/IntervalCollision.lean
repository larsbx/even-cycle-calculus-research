import CollisionBridge

/- Finite collision criterion for injective periodic coordinate projections.
   Bounds and monotonicity are hypotheses; the application to word prefix counts,
   connected-partition enumeration and motif cardinalities remain prose. -/
namespace ECC.IntervalCollision
open ECC.CollisionBridge

theorem bounded_mod_eq_iff (d u v : Nat) (_hd : 0 < d)
    (huv : u ≤ v) (hvd : v ≤ d) :
    u % d = v % d ↔ v - u = 0 ∨ v - u = d := by
  by_cases hv : v < d
  · have hu : u < d := by omega
    rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv]
    constructor
    · intro h
      exact Or.inl (by omega)
    · intro h
      rcases h with h | h
      · omega
      · omega
  · have hvd' : v = d := by omega
    subst v
    by_cases hu : u < d
    · rw [Nat.mod_eq_of_lt hu, Nat.mod_self]
      constructor
      · intro h
        exact Or.inr (by omega)
      · intro h
        rcases h with h | h
        · omega
        · omega
    · have hud : u = d := by omega
      subst u
      constructor
      · intro _
        exact Or.inl (Nat.sub_self d)
      · intro _
        rfl

def phase {q : Nat} {d : Fin q → Nat} (hd : ∀ a, 0 < d a)
    (c : Fin q → Nat) : Vertex d :=
  fun a => ⟨c a % d a, Nat.mod_lt _ (hd a)⟩

def WholeBlocks {q : Nat} (d u v : Fin q → Nat) : Prop :=
  ∀ a, v a - u a = 0 ∨ v a - u a = d a

theorem phase_equal_iff {q : Nat} {d : Fin q → Nat}
    (hd : ∀ a, 0 < d a) (u v : Fin q → Nat)
    (huv : ∀ a, u a ≤ v a) (hvd : ∀ a, v a ≤ d a) :
    phase hd u = phase hd v ↔ WholeBlocks d u v := by
  constructor
  · intro h a
    have ha := congrArg Fin.val (congrFun h a)
    exact (bounded_mod_eq_iff (d a) (u a) (v a) (hd a) (huv a) (hvd a)).1 ha
  · intro h
    funext a
    apply Fin.ext
    exact (bounded_mod_eq_iff (d a) (u a) (v a) (hd a) (huv a) (hvd a)).2 (h a)

theorem decoded_equal_iff {q : Nat} {d N : Fin q → Nat}
    (hd : ∀ a, 0 < d a)
    (f : (a : Fin q) → Fin (d a) → Fin (N a)) (hf : FactorInjective f)
    (u v : Fin q → Nat) (huv : ∀ a, u a ≤ v a) (hvd : ∀ a, v a ≤ d a) :
    Decode f (phase hd u) = Decode f (phase hd v) ↔ WholeBlocks d u v := by
  exact (decode_equal_iff f hf _ _).trans (phase_equal_iff hd u v huv hvd)

theorem trace_injective_iff_no_interval {L q : Nat} {d : Fin q → Nat}
    (hd : ∀ a, 0 < d a) (c : Fin L → Fin q → Nat)
    (hmono : ∀ s t, s.val ≤ t.val → ∀ a, c s a ≤ c t a)
    (hbound : ∀ t a, c t a ≤ d a) :
    TraceInjective (fun t => phase hd (c t)) ↔
      ∀ s t, s.val < t.val → ¬ WholeBlocks d (c s) (c t) := by
  constructor
  · intro hi s t hst hblocks
    have heq := (phase_equal_iff hd (c s) (c t)
      (hmono s t (by omega)) (hbound t)).2 hblocks
    have hs := hi s t heq
    have := congrArg Fin.val hs
    omega
  · intro hn s t heq
    apply Fin.ext
    by_cases hst : s.val < t.val
    · exact False.elim (hn s t hst ((phase_equal_iff hd (c s) (c t)
        (hmono s t (by omega)) (hbound t)).1 heq))
    · by_cases hts : t.val < s.val
      · exact False.elim (hn t s hts ((phase_equal_iff hd (c t) (c s)
          (hmono t s (by omega)) (hbound s)).1 heq.symm))
      · omega

theorem decoded_injective_iff_no_interval {L q : Nat} {d N : Fin q → Nat}
    (hd : ∀ a, 0 < d a)
    (f : (a : Fin q) → Fin (d a) → Fin (N a)) (hf : FactorInjective f)
    (c : Fin L → Fin q → Nat)
    (hmono : ∀ s t, s.val ≤ t.val → ∀ a, c s a ≤ c t a)
    (hbound : ∀ t a, c t a ≤ d a) :
    TraceInjective (fun t => Decode f (phase hd (c t))) ↔
      ∀ s t, s.val < t.val → ¬ WholeBlocks d (c s) (c t) := by
  exact (trace_injective_iff f hf _).trans
    (trace_injective_iff_no_interval hd c hmono hbound)

/- The three exclusions are essential; these are finite kernel reductions. -/
theorem full_period_is_collision : 0 % 3 = 3 % 3 ∧ 3 - 0 = 3 := by decide

theorem upper_bound_needed : 0 % 2 = 4 % 2 ∧ ¬ (4 - 0 = 0 ∨ 4 - 0 = 2) := by decide

theorem injective_projection_needed :
    (#[0, 1, 0, 1] : Array Nat)[0]! = (#[0, 1, 0, 1] : Array Nat)[2]! ∧
      ¬ (2 - 0 = 0 ∨ 2 - 0 = 4) := by decide

#print axioms bounded_mod_eq_iff
#print axioms phase_equal_iff
#print axioms decoded_equal_iff
#print axioms trace_injective_iff_no_interval
#print axioms decoded_injective_iff_no_interval
#print axioms full_period_is_collision
#print axioms upper_bound_needed
#print axioms injective_projection_needed

end ECC.IntervalCollision
