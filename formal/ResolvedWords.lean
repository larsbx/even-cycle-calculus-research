import RepeatedEdge

/- Literal resolutions of finite axis words. none is the four-step axis;
   some a is any other labeled edge axis. All replays use exact Booleans. -/
namespace ECC.ResolvedWords
open ECC.RepeatedEdge (Injective)

def steps {r : Nat} : List (Option (Fin r)) → Nat
  | [] => 0
  | none :: w => 1 + steps w
  | some _ :: w => steps w

def frontColor (n : Nat) : Bool := n ≥ 2

def outerColor (n : Nat) : Bool := n == 1 || n == 2

def foldPhase (n : Nat) : Bool := n % 2 == 1

def frontPhase (n : Nat) : Bool × Bool := (n == 1, n == 3)

def outerPhase (n : Nat) : Bool × Bool := (0 < n && n < 4, n == 2)

def flipPair (b : Bool) (x : Bool × Bool) : Bool × Bool :=
  if b then (x.1, !x.2) else (!x.1, x.2)

def flipRest {r : Nat} (a : Fin r) (x : Fin r → Bool) : Fin r → Bool :=
  fun b => if b = a then !x b else x b

def resolve {r : Nat} (color : Nat → Bool) (n : Nat) :
    List (Option (Fin r)) → List (Sum Bool (Fin r))
  | [] => []
  | none :: w => Sum.inl (color n) :: resolve color (n+1) w
  | some a :: w => Sum.inr a :: resolve color n w

def restRun {r : Nat} : List (Option (Fin r)) → (Fin r → Bool) → (Fin r → Bool)
  | [], x => x
  | none :: w, x => restRun w x
  | some a :: w, x => restRun w (flipRest a x)

def foldRun {r : Nat} : List (Option (Fin r)) →
    (Bool × (Fin r → Bool)) → (Bool × (Fin r → Bool))
  | [], x => x
  | none :: w, x => foldRun w (!x.1, x.2)
  | some a :: w, x => foldRun w (x.1, flipRest a x.2)

def splitRun {r : Nat} : List (Sum Bool (Fin r)) →
    ((Bool × Bool) × (Fin r → Bool)) → ((Bool × Bool) × (Fin r → Bool))
  | [], x => x
  | Sum.inl b :: w, x => splitRun w (flipPair b x.1, x.2)
  | Sum.inr a :: w, x => splitRun w (x.1, flipRest a x.2)

theorem phase_collision (p q : Nat) (hp : p ≤ 4) (hq : q ≤ 4) :
    foldPhase p = foldPhase q ↔
      frontPhase p = frontPhase q ∨ outerPhase p = outerPhase q := by
  exact ECC.RepeatedEdge.phase_collision ⟨p, by omega⟩ ⟨q, by omega⟩

private theorem finite_phase_steps : ∀ p : Fin 4,
    ((!foldPhase p.val) = foldPhase (p.val+1)) ∧
    (flipPair (frontColor p.val) (frontPhase p.val) = frontPhase (p.val+1)) ∧
    (flipPair (outerColor p.val) (outerPhase p.val) = outerPhase (p.val+1)) := by decide

theorem phase_steps (n : Nat) (hn : n < 4) :
    ((!foldPhase n) = foldPhase (n+1)) ∧
    (flipPair (frontColor n) (frontPhase n) = frontPhase (n+1)) ∧
    (flipPair (outerColor n) (outerPhase n) = outerPhase (n+1)) :=
  finite_phase_steps ⟨n, hn⟩

theorem resolve_length {r : Nat} (color : Nat → Bool) (n : Nat)
    (w : List (Option (Fin r))) : (resolve color n w).length = w.length := by
  induction w generalizing n with
  | nil => rfl
  | cons a w ih => cases a <;> simp [resolve, ih]

theorem resolve_take {r : Nat} (color : Nat → Bool) (n k : Nat)
    (w : List (Option (Fin r))) :
    resolve color n (w.take k) = (resolve color n w).take k := by
  induction w generalizing n k with
  | nil => simp [resolve]
  | cons a w ih => cases k with
    | zero => simp [resolve]
    | succ k => cases a <;> simp [resolve, ih]

theorem steps_take_le {r : Nat} (k : Nat) (w : List (Option (Fin r))) :
    steps (w.take k) ≤ steps w := by
  induction w generalizing k with
  | nil => simp [steps]
  | cons a w ih => cases k with
    | zero => cases a <;> simp [steps]
    | succ k => cases a <;> simp [steps, ih]

theorem folded_replay {r : Nat} (w : List (Option (Fin r)))
    (n : Nat) (x : Fin r → Bool) (h : n + steps w ≤ 4) :
    foldRun w (foldPhase n, x) = (foldPhase (n + steps w), restRun w x) := by
  induction w generalizing n x with
  | nil => simp [foldRun, restRun, steps]
  | cons a w ih => cases a with
    | none =>
      have hn : n < 4 := by simp [steps] at h; omega
      simp only [foldRun, restRun]
      rw [(phase_steps n hn).1, ih (n+1) x (by simp [steps] at h; omega)]
      simp [steps, Nat.add_assoc]
    | some a => simpa [foldRun, restRun, steps] using ih n (flipRest a x) h

theorem split_replay {r : Nat} (color : Nat → Bool) (phase : Nat → Bool × Bool)
    (hstep : ∀ n, n < 4 → flipPair (color n) (phase n) = phase (n+1))
    (w : List (Option (Fin r))) (n : Nat) (x : Fin r → Bool)
    (h : n + steps w ≤ 4) :
    splitRun (resolve color n w) (phase n, x) =
      (phase (n + steps w), restRun w x) := by
  induction w generalizing n x with
  | nil => simp [resolve, splitRun, restRun, steps]
  | cons a w ih => cases a with
    | none =>
      have hn : n < 4 := by simp [steps] at h; omega
      simp only [resolve, splitRun, restRun]
      rw [hstep n hn, ih (n+1) x (by simp [steps] at h; omega)]
      simp [steps, Nat.add_assoc]
    | some a => simpa [resolve, splitRun, restRun, steps] using ih n (flipRest a x) h

def foldedTrace {r : Nat} (w : List (Option (Fin r))) (t : Fin w.length) :=
  foldRun (w.take t.val) (false, fun _ => false)

def resolvedTrace {r : Nat} (color : Nat → Bool) (w : List (Option (Fin r)))
    (t : Fin w.length) :=
  splitRun ((resolve color 0 w).take t.val) ((false, false), fun _ => false)

theorem folded_prefix {r : Nat} (w : List (Option (Fin r))) (hw : steps w ≤ 4)
    (t : Fin w.length) : foldedTrace w t =
      (foldPhase (steps (w.take t.val)), restRun (w.take t.val) (fun _ => false)) := by
  simpa [foldedTrace, foldPhase] using
    folded_replay (w.take t.val) 0 (fun _ => false)
      (by have := steps_take_le t.val w; omega)

theorem resolved_prefix {r : Nat} (color : Nat → Bool) (phase : Nat → Bool × Bool)
    (hzero : phase 0 = (false, false))
    (hstep : ∀ n, n < 4 → flipPair (color n) (phase n) = phase (n+1))
    (w : List (Option (Fin r))) (hw : steps w ≤ 4) (t : Fin w.length) :
    resolvedTrace color w t =
      (phase (steps (w.take t.val)), restRun (w.take t.val) (fun _ => false)) := by
  unfold resolvedTrace
  rw [← resolve_take]
  rw [← hzero]
  simpa using split_replay color phase hstep (w.take t.val) 0 (fun _ => false)
    (by have := steps_take_le t.val w; omega)

theorem word_collision {r : Nat} (w : List (Option (Fin r))) (hw : steps w ≤ 4)
    (s t : Fin w.length) :
    foldedTrace w s = foldedTrace w t ↔
      resolvedTrace frontColor w s = resolvedTrace frontColor w t ∨
      resolvedTrace outerColor w s = resolvedTrace outerColor w t := by
  rw [folded_prefix w hw s, folded_prefix w hw t,
      resolved_prefix frontColor frontPhase rfl (fun n hn => (phase_steps n hn).2.1) w hw s,
      resolved_prefix frontColor frontPhase rfl (fun n hn => (phase_steps n hn).2.1) w hw t,
      resolved_prefix outerColor outerPhase rfl (fun n hn => (phase_steps n hn).2.2) w hw s,
      resolved_prefix outerColor outerPhase rfl (fun n hn => (phase_steps n hn).2.2) w hw t]
  simp only [Prod.mk.injEq]
  rw [phase_collision _ _ (Nat.le_trans (steps_take_le _ _) hw)
      (Nat.le_trans (steps_take_le _ _) hw)]
  exact or_and_right

theorem word_injective_iff {r : Nat} (w : List (Option (Fin r))) (hw : steps w ≤ 4) :
    Injective (foldedTrace w) ↔
      Injective (resolvedTrace frontColor w) ∧ Injective (resolvedTrace outerColor w) := by
  constructor
  · intro hi
    constructor
    · intro s t h
      exact hi s t ((word_collision w hw s t).2 (Or.inl h))
    · intro s t h
      exact hi s t ((word_collision w hw s t).2 (Or.inr h))
  · rintro ⟨hf, ho⟩ s t h
    rcases (word_collision w hw s t).1 h with h | h
    · exact hf s t h
    · exact ho s t h

def occurs {A : Type} [DecidableEq A] (a : A) : List A → Nat
  | [] => 0
  | b :: w => (if b = a then 1 else 0) + occurs a w

def colorCount (color : Nat → Bool) (n : Nat) : Nat → Bool → Nat
  | 0, _ => 0
  | k+1, b => (if color n = b then 1 else 0) + colorCount color (n+1) k b

theorem steps_occurs {r : Nat} (w : List (Option (Fin r))) : steps w = occurs none w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [steps, occurs, ih]

theorem resolve_count_other {r : Nat} (color : Nat → Bool) (n : Nat)
    (w : List (Option (Fin r))) (a : Fin r) :
    occurs (Sum.inr a) (resolve color n w) = occurs (some a) w := by
  induction w generalizing n with
  | nil => rfl
  | cons b w ih => cases b <;> simp [resolve, occurs, ih]

theorem resolve_count_split {r : Nat} (color : Nat → Bool) (n : Nat)
    (w : List (Option (Fin r))) (b : Bool) :
    occurs (Sum.inl b) (resolve color n w) = colorCount color n (steps w) b := by
  induction w generalizing n with
  | nil => rfl
  | cons a w ih => cases a <;> simp [resolve, occurs, steps, Nat.add_comm 1, colorCount, ih]

theorem four_split_counts {r : Nat} (w : List (Option (Fin r))) (hw : steps w = 4) :
    occurs (Sum.inl false) (resolve frontColor 0 w) = 2 ∧
    occurs (Sum.inl true) (resolve frontColor 0 w) = 2 ∧
    occurs (Sum.inl false) (resolve outerColor 0 w) = 2 ∧
    occurs (Sum.inl true) (resolve outerColor 0 w) = 2 := by
  simp only [resolve_count_split, hw]
  decide

theorem four_step_inventory {r : Nat} (w : List (Option (Fin r)))
    (hw : steps w = 4) (hother : ∀ a, occurs (some a) w = 2) :
    (∀ a, occurs (Sum.inr a) (resolve frontColor 0 w) = 2) ∧
    (∀ a, occurs (Sum.inr a) (resolve outerColor 0 w) = 2) ∧
    (occurs (Sum.inl false) (resolve frontColor 0 w) = 2 ∧
     occurs (Sum.inl true) (resolve frontColor 0 w) = 2 ∧
     occurs (Sum.inl false) (resolve outerColor 0 w) = 2 ∧
     occurs (Sum.inl true) (resolve outerColor 0 w) = 2) := by
  exact ⟨fun a => (resolve_count_other _ _ _ _).trans (hother a),
         fun a => (resolve_count_other _ _ _ _).trans (hother a), four_split_counts w hw⟩

theorem literal_resolution_control :
    resolve frontColor 0 ([none, some 0, none, none, some 0, none] : List (Option (Fin 1))) =
      [Sum.inl false, Sum.inr 0, Sum.inl false, Sum.inl true, Sum.inr 0, Sum.inl true] ∧
    resolve outerColor 0 ([none, some 0, none, none, some 0, none] : List (Option (Fin 1))) =
      [Sum.inl false, Sum.inr 0, Sum.inl true, Sum.inl true, Sum.inr 0, Sum.inl false] := by decide

theorem budget_bound_control :
    (splitRun (resolve frontColor 0 ([none,none,none,none,none] : List (Option (Fin 0))))
      ((false,false), fun _ => false)).1 = (false,true) ∧ frontPhase 5 = (false,false) := by decide

theorem departure_endpoint_control :
    (foldRun ([none,none,none,none] : List (Option (Fin 0))) (false, fun _ => false)).1 = false ∧
    (resolve frontColor 0 ([none,none,none,none] : List (Option (Fin 0)))).length = 4 := by decide

#print axioms steps_occurs
#print axioms resolve_count_other
#print axioms resolve_count_split
#print axioms four_split_counts
#print axioms four_step_inventory
#print axioms literal_resolution_control
#print axioms budget_bound_control
#print axioms departure_endpoint_control

#print axioms phase_collision
#print axioms phase_steps
#print axioms resolve_length
#print axioms resolve_take
#print axioms steps_take_le
#print axioms folded_replay
#print axioms split_replay
#print axioms folded_prefix
#print axioms resolved_prefix
#print axioms word_collision
#print axioms word_injective_iff

end ECC.ResolvedWords
