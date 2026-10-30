import Std

/- Five phases before/after the four distinguished steps. The application to
   word-prefix phases, matching enumeration and motif cardinalities is prose. -/
namespace ECC.RepeatedEdge

def folded (p : Fin 5) : Bool := p.val % 2 == 1

def front (p : Fin 5) : Bool × Bool := (p.val == 1, p.val == 3)

def outer (p : Fin 5) : Bool × Bool := (0 < p.val && p.val < 4, p.val == 2)

theorem phase_collision : ∀ p q : Fin 5,
    folded p = folded q ↔ front p = front q ∨ outer p = outer q := by decide

theorem state_collision {N : Nat} (p q : Fin 5) (x y : Fin N) :
    (folded p, x) = (folded q, y) ↔
      (front p, x) = (front q, y) ∨ (outer p, x) = (outer q, y) := by
  constructor
  · intro h
    have hp := congrArg Prod.fst h
    have hx := congrArg Prod.snd h
    rcases (phase_collision p q).1 hp with hf | ho
    · exact Or.inl (Prod.ext hf hx)
    · exact Or.inr (Prod.ext ho hx)
  · intro h
    rcases h with h | h
    · have hp : front p = front q := congrArg Prod.fst h
      have hx : x = y := congrArg Prod.snd h
      exact Prod.ext ((phase_collision p q).2 (Or.inl hp)) hx
    · have hp : outer p = outer q := congrArg Prod.fst h
      have hx : x = y := congrArg Prod.snd h
      exact Prod.ext ((phase_collision p q).2 (Or.inr hp)) hx

-- Arbitrary finite departure traces; no assumptions about coordinate monotonicity.
def Injective {A B : Type} (f : A → B) : Prop := ∀ s t, f s = f t → s = t

theorem trace_injective_iff {L N : Nat} (phase : Fin L → Fin 5)
    (rest : Fin L → Fin N) :
    Injective (fun t => (folded (phase t), rest t)) ↔
      Injective (fun t => (front (phase t), rest t)) ∧
      Injective (fun t => (outer (phase t), rest t)) := by
  constructor
  · intro hi
    constructor
    · intro s t h
      exact hi s t ((state_collision _ _ _ _).2 (Or.inl h))
    · intro s t h
      exact hi s t ((state_collision _ _ _ _).2 (Or.inr h))
  · rintro ⟨hf, ho⟩ s t h
    rcases (state_collision _ _ _ _).1 h with h | h
    · exact hf s t h
    · exact ho s t h

theorem front_only_insufficient : front 1 ≠ front 3 ∧ folded 1 = folded 3 := by decide

theorem outer_only_insufficient : outer 0 ≠ outer 2 ∧ folded 0 = folded 2 := by decide

theorem endpoint_return : folded 0 = folded 4 ∧ front 0 = front 4 ∧ outer 0 = outer 4 := by decide

theorem distinct_rest_prevents_collision :
    ((folded 0, (0 : Fin 2)) ≠ (folded 2, (1 : Fin 2))) := by decide

#print axioms phase_collision
#print axioms state_collision
#print axioms trace_injective_iff
#print axioms front_only_insufficient
#print axioms outer_only_insufficient
#print axioms endpoint_return
#print axioms distinct_rest_prevents_collision

end ECC.RepeatedEdge
