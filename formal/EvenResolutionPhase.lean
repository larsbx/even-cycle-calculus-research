import RepeatedEdge

/- Two alternating matchings of an even occurrence block. Values are the
   exact parity vectors after p events, including the final return phase. -/
namespace ECC.EvenResolutionPhase
open ECC.RepeatedEdge (Injective)

local instance vectorDecidableEq {A : Type} [DecidableEq A] (n : Nat) : DecidableEq (Fin n → A) :=
  fun f g => if h : ∀ a, f a = g a then isTrue (funext h)
    else isFalse (fun heq => h (fun a => congrFun heq a))

def first (m p : Nat) : Fin m → Bool := fun a => decide (p = 2*a.val+1)

def second (m p : Nat) : Fin m → Bool := fun a =>
  if a.val = 0 then 0 < p && p < 2*m else decide (p = 2*a.val)

theorem first_even (m p : Nat) (hp : p % 2 = 0) :
    first m p = fun _ => false := by
  funext a
  have h : p ≠ 2*a.val+1 := by omega
  simp [first, h]

theorem second_odd (m p : Nat) (hp : p % 2 = 1) (hb : p ≤ 2*m) :
    second m p = fun a => decide (a.val = 0) := by
  funext a
  have hpos : 0 < p := by omega
  have hlt : p < 2*m := by omega
  have hne : p ≠ 2*a.val := by omega
  by_cases ha : a.val = 0 <;> simp [second, ha, hpos, hlt, hne]

theorem first_odd_ne_even (m p q : Nat) (hp : p % 2 = 1)
    (hq : q % 2 = 0) (hb : p ≤ 2*m) : first m p ≠ first m q := by
  let a : Fin m := ⟨p/2, by omega⟩
  have hp' : p = 2*a.val+1 := by dsimp [a]; omega
  have hq' : q ≠ 2*a.val+1 := by omega
  intro heq
  have hx := congrFun heq a
  simp [first, hp', hq'] at hx

theorem second_odd_ne_even (m p q : Nat) (hm : 0 < m)
    (hp : p % 2 = 1) (hq : q % 2 = 0) (hpb : p ≤ 2*m) (hqb : q ≤ 2*m) :
    second m p ≠ second m q := by
  intro heq
  rw [second_odd m p hp hpb] at heq
  by_cases hqend : q = 0 ∨ q = 2*m
  · have hx := congrFun heq (⟨0, hm⟩ : Fin m)
    rcases hqend with h | h <;> simp [second, h] at hx
  · have hqpos : 0 < q := by omega
    have hqlt : q < 2*m := by omega
    let a : Fin m := ⟨q/2, by omega⟩
    have ha : a.val ≠ 0 := by dsimp [a]; omega
    have hq' : q = 2*a.val := by dsimp [a]; omega
    have hx := congrFun heq a
    simp [second, ha, hq'] at hx

theorem first_reflects_parity (m p q : Nat) (hp : p ≤ 2*m) (hq : q ≤ 2*m)
    (h : first m p = first m q) : p % 2 = q % 2 := by
  by_cases hpo : p % 2 = 1
  · by_cases hqo : q % 2 = 1
    · omega
    · exact False.elim (first_odd_ne_even m p q hpo (by omega) hp h)
  · by_cases hqo : q % 2 = 1
    · exact False.elim (first_odd_ne_even m q p hqo (by omega) hq h.symm)
    · omega

theorem second_reflects_parity (m p q : Nat) (hm : 0 < m)
    (hp : p ≤ 2*m) (hq : q ≤ 2*m) (h : second m p = second m q) : p % 2 = q % 2 := by
  by_cases hpo : p % 2 = 1
  · by_cases hqo : q % 2 = 1
    · omega
    · exact False.elim (second_odd_ne_even m p q hm hpo (by omega) hp hq h)
  · by_cases hqo : q % 2 = 1
    · exact False.elim (second_odd_ne_even m q p hm hqo (by omega) hq hp h.symm)
    · omega

theorem phase_collision (m p q : Nat) (hm : 0 < m) (hp : p ≤ 2*m) (hq : q ≤ 2*m) :
    p % 2 = q % 2 ↔ first m p = first m q ∨ second m p = second m q := by
  constructor
  · intro h
    by_cases he : p % 2 = 0
    · exact Or.inl ((first_even m p he).trans (first_even m q (by omega)).symm)
    · exact Or.inr ((second_odd m p (by omega) hp).trans
        (second_odd m q (by omega) hq).symm)
  · intro h
    rcases h with h | h
    · exact first_reflects_parity m p q hp hq h
    · exact second_reflects_parity m p q hm hp hq h

def resolved {q : Nat} (m : Fin q → Nat) (phase : (a : Fin q) → Fin (2*m a+1))
    (choice : Fin q → Bool) : (a : Fin q) → Fin (m a) → Bool :=
  fun a => if choice a then second (m a) (phase a).val else first (m a) (phase a).val

def parity {q : Nat} {m : Fin q → Nat} (phase : (a : Fin q) → Fin (2*m a+1)) :
    Fin q → Nat := fun a => (phase a).val % 2

theorem resolution_reflects_collision {q : Nat} (m : Fin q → Nat) (hm : ∀ a, 0 < m a)
    (p s : (a : Fin q) → Fin (2*m a+1)) (choice : Fin q → Bool)
    (h : resolved m p choice = resolved m s choice) : parity p = parity s := by
  funext a
  have ha := congrFun h a
  have hp : (p a).val ≤ 2*m a := by have := (p a).isLt; omega
  have hs : (s a).val ≤ 2*m a := by have := (s a).isLt; omega
  apply (phase_collision (m a) _ _ (hm a) hp hs).2
  cases hc : choice a with
  | false => exact Or.inl (by simpa [resolved, hc] using ha)
  | true => exact Or.inr (by simpa [resolved, hc] using ha)

theorem collision_has_resolution {q : Nat} (m : Fin q → Nat) (hm : ∀ a, 0 < m a)
    (p s : (a : Fin q) → Fin (2*m a+1)) (h : parity p = parity s) :
    ∃ choice : Fin q → Bool, resolved m p choice = resolved m s choice := by
  let choice : Fin q → Bool := fun a => decide (first (m a) (p a).val ≠ first (m a) (s a).val)
  refine ⟨choice, ?_⟩
  funext a
  have hp : (p a).val ≤ 2*m a := by have := (p a).isLt; omega
  have hs : (s a).val ≤ 2*m a := by have := (s a).isLt; omega
  have hor := (phase_collision (m a) _ _ (hm a) hp hs).1 (congrFun h a)
  by_cases hf : first (m a) (p a).val = first (m a) (s a).val
  · simp [resolved, choice, hf]
  · have ho := hor.resolve_left hf
    simpa [resolved, choice, hf] using ho

theorem collision_iff_exists_resolution {q : Nat} (m : Fin q → Nat) (hm : ∀ a, 0 < m a)
    (p s : (a : Fin q) → Fin (2*m a+1)) :
    parity p = parity s ↔ ∃ choice : Fin q → Bool, resolved m p choice = resolved m s choice := by
  constructor
  · exact collision_has_resolution m hm p s
  · rintro ⟨choice, h⟩
    exact resolution_reflects_collision m hm p s choice h

theorem all_resolutions_injective_iff {L q : Nat} (m : Fin q → Nat)
    (hm : ∀ a, 0 < m a) (phase : Fin L → (a : Fin q) → Fin (2*m a+1)) :
    Injective (fun t => parity (phase t)) ↔
      ∀ choice : Fin q → Bool, Injective (fun t => resolved m (phase t) choice) := by
  constructor
  · intro hi choice s t h
    exact hi s t (resolution_reflects_collision m hm _ _ choice h)
  · intro hi s t h
    obtain ⟨choice, hc⟩ := collision_has_resolution m hm _ _ h
    exact hi choice s t hc

theorem six_event_vectors :
    (List.range 7).map (fun p => (List.finRange 3).map (first 3 p)) =
      [[false,false,false],[true,false,false],[false,false,false],[false,true,false],
       [false,false,false],[false,false,true],[false,false,false]] ∧
    (List.range 7).map (fun p => (List.finRange 3).map (second 3 p)) =
      [[false,false,false],[true,false,false],[true,true,false],[true,false,false],
       [true,false,true],[true,false,false],[false,false,false]] := by decide

theorem positive_half_period_needed :
    first 0 0 = first 0 1 ∧ second 0 0 = second 0 1 ∧ 0 % 2 ≠ 1 % 2 := by decide

theorem phase_bound_needed :
    first 2 0 = first 2 5 ∧ second 2 0 = second 2 5 ∧ 0 % 2 ≠ 5 % 2 := by decide

def pControl : (a : Fin 2) → Fin (2*(fun _ : Fin 2 => 2) a+1) :=
  fun a => if a.val = 0 then 1 else 0

def sControl : (a : Fin 2) → Fin (2*(fun _ : Fin 2 => 2) a+1) :=
  fun a => if a.val = 0 then 3 else 2

theorem diagonal_choices_insufficient :
    parity pControl = parity sControl ∧
    resolved (fun _ => 2) pControl (fun _ => false) ≠ resolved (fun _ => 2) sControl (fun _ => false) ∧
    resolved (fun _ => 2) pControl (fun _ => true) ≠ resolved (fun _ => 2) sControl (fun _ => true) ∧
    resolved (fun _ => 2) pControl (fun a => decide (a.val = 0)) =
      resolved (fun _ => 2) sControl (fun a => decide (a.val = 0)) := by decide

#print axioms diagonal_choices_insufficient

#print axioms first_even
#print axioms second_odd
#print axioms first_odd_ne_even
#print axioms second_odd_ne_even
#print axioms first_reflects_parity
#print axioms second_reflects_parity
#print axioms phase_collision
#print axioms resolution_reflects_collision
#print axioms collision_has_resolution
#print axioms collision_iff_exists_resolution
#print axioms all_resolutions_injective_iff
#print axioms six_event_vectors
#print axioms positive_half_period_needed
#print axioms phase_bound_needed

end ECC.EvenResolutionPhase
