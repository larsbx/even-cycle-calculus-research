import Shuffle
import CycleTrace

/- A bounds-safe model of the literal Shuffle.vertices prefix-index recursion.
   Coordinate templates have positive finite periods; axes are Fin q values. -/
namespace ECC.ExecutableTrace
open ECC.CollisionBridge ECC.EventShuffle ECC.ClosedWalk ECC.CycleTrace

abbrev Templates {q : Nat} (n period : Fin q → Nat) :=
  (a : Fin q) → Fin (period a) → Fin (n a)

def read {q : Nat} {n period : Fin q → Nat} (hp : ∀ a, 0 < period a)
    (p : Templates n period) (pos : Fin q → Nat) : Vertex n :=
  fun a => p a ⟨pos a % period a, Nat.mod_lt _ (hp a)⟩

def tick {q : Nat} (pos : Fin q → Nat) (a : Fin q) : Fin q → Nat :=
  fun b => if b = a then pos b + 1 else pos b

def events {q : Nat} {n period : Fin q → Nat} (hp : ∀ a, 0 < period a)
    (p : Templates n period) : List (Fin q) → (Fin q → Nat) → List (Event n)
  | [], _ => []
  | a :: word, pos => ⟨a, read hp p (tick pos a) a⟩ :: events hp p word (tick pos a)

def encode {q : Nat} {n : Fin q → Nat} (v : Vertex n) : List Nat :=
  List.ofFn fun a => (v a).val

def rawPatterns {q : Nat} {n period : Fin q → Nat} (p : Templates n period) : List (List Nat) :=
  List.ofFn fun a => List.ofFn fun i => (p a i).val

def rawPos {q : Nat} (pos : Fin q → Nat) : List Nat := List.ofFn pos

def rawRead (patterns : List (List Nat)) (pos : List Nat) : List Nat :=
  (List.range patterns.length).map fun b =>
    let p := patterns[b]!
    p[pos[b]! % p.length]!

theorem encode_injective {q : Nat} {n : Fin q → Nat} (v w : Vertex n)
    (h : encode v = encode w) : v = w := by
  funext a
  apply Fin.ext
  have same := congrArg (fun xs : List Nat => xs[a.val]!) h
  simpa [encode, getElem!_pos, a.isLt] using same

theorem read_update {q : Nat} {n period : Fin q → Nat} (hp : ∀ a, 0 < period a)
    (p : Templates n period) (pos : Fin q → Nat) (a : Fin q) :
    update (read hp p pos) ⟨a, read hp p (tick pos a) a⟩ = read hp p (tick pos a) := by
  funext b
  by_cases h : b = a
  · subst b
    simp [update]
  · simp [update, read, tick, h]

/- Std's getElem_modify theorem in the pinned release imports choice.
   This bounded structural proof uses only the literal list recursion. -/
theorem get_modify_safe {α : Type} (f : α → α) (xs : List α) (i j : Nat)
    (hj : j < xs.length) :
    (xs.modify i f)[j]'(by rw [List.length_modify]; exact hj) =
      if i = j then f xs[j] else xs[j] := by
  induction xs generalizing i j with
  | nil => exact False.elim (Nat.not_lt_zero _ hj)
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.modify_zero_cons, List.getElem_cons_succ, Nat.zero_ne_add_one, ite_false]
    | succ i =>
      cases j with
      | zero =>
        simp only [List.modify_succ_cons, List.getElem_cons_zero, Nat.succ_ne_zero, ite_false]
      | succ j =>
        simpa only [List.modify_succ_cons, List.getElem_cons_succ, Nat.succ.injEq] using
          ih i j (Nat.lt_of_succ_lt_succ hj)

theorem raw_tick {q : Nat} (pos : Fin q → Nat) (a : Fin q) :
    (rawPos pos).modify a.val (· + 1) = rawPos (tick pos a) := by
  apply List.ext_getElem
  · simp [rawPos]
  · intro i hi hj
    have hiq : i < q := by simpa [rawPos] using hj
    rw [get_modify_safe (· + 1) (rawPos pos) a.val i (by simpa [rawPos] using hiq)]
    simp only [rawPos, List.getElem_ofFn, tick]
    by_cases h : a.val = i
    · subst i
      simp
    · have hfin : (⟨i, hiq⟩ : Fin q) ≠ a := fun heq => h (congrArg Fin.val heq).symm
      simp [h, hfin]

theorem raw_read {q : Nat} {n period : Fin q → Nat} (hp : ∀ a, 0 < period a)
    (p : Templates n period) (pos : Fin q → Nat) :
    rawRead (rawPatterns p) (rawPos pos) = encode (read hp p pos) := by
  apply List.ext_getElem
  · simp [rawRead, rawPatterns, encode]
  · intro i hi hj
    have hiq : i < q := by simpa [encode] using hj
    simp only [rawRead, rawPatterns, rawPos, encode, read, List.length_ofFn,
      List.getElem_map, List.getElem_range]
    simp [getElem!_pos, hiq, Nat.mod_lt _ (hp ⟨i, hiq⟩)]

theorem vertices_eq_encoded_departures {q : Nat} {n period : Fin q → Nat}
    (hp : ∀ a, 0 < period a) (p : Templates n period)
    (word : List (Fin q)) (pos : Fin q → Nat) :
    ECC.vertices (rawPatterns p) (word.map Fin.val) (rawPos pos) =
      (before (read hp p pos) (events hp p word pos)).map encode := by
  induction word generalizing pos with
  | nil => rfl
  | cons a word ih =>
    change rawRead (rawPatterns p) (rawPos pos) ::
      ECC.vertices (rawPatterns p) (word.map Fin.val) ((rawPos pos).modify a.val (· + 1)) = _
    rw [raw_read hp, raw_tick, ih]
    simp only [events, before, List.map_cons, read_update]

theorem events_axes {q : Nat} {n period : Fin q → Nat}
    (hp : ∀ a, 0 < period a) (p : Templates n period)
    (word : List (Fin q)) (pos : Fin q → Nat) : axes (events hp p word pos) = word := by
  induction word generalizing pos with
  | nil => rfl
  | cons a word ih =>
    change a :: axes (events hp p word (tick pos a)) = a :: word
    rw [ih]

theorem events_length {q : Nat} {n period : Fin q → Nat}
    (hp : ∀ a, 0 < period a) (p : Templates n period)
    (word : List (Fin q)) (pos : Fin q → Nat) : (events hp p word pos).length = word.length := by
  have h := congrArg List.length (events_axes hp p word pos)
  simpa only [axes, List.length_map] using h

def endPos {q : Nat} : List (Fin q) → (Fin q → Nat) → (Fin q → Nat)
  | [], pos => pos
  | a :: word, pos => endPos word (tick pos a)

theorem finish_events {q : Nat} {n period : Fin q → Nat}
    (hp : ∀ a, 0 < period a) (p : Templates n period)
    (word : List (Fin q)) (pos : Fin q → Nat) :
    finish (read hp p pos) (events hp p word pos) = read hp p (endPos word pos) := by
  induction word generalizing pos with
  | nil => rfl
  | cons a word ih =>
    simp only [events, finish, read_update, endPos, ih]

theorem endPos_coordinate {q : Nat} (word : List (Fin q)) (pos : Fin q → Nat) (a : Fin q) :
    endPos word pos a = pos a + steps word a := by
  induction word generalizing pos with
  | nil => simp [endPos, steps]
  | cons b word ih =>
    simp only [endPos, ih, tick, steps]
    by_cases h : b = a
    · subst b
      simp only [eq_self, ite_true]
      omega
    · simp [h, Ne.symm h]

theorem closure_if_periods_divide_steps {q : Nat} {n period : Fin q → Nat}
    (hp : ∀ a, 0 < period a) (p : Templates n period)
    (word : List (Fin q)) (pos : Fin q → Nat)
    (hcounts : ∀ a, steps word a % period a = 0) :
    finish (read hp p pos) (events hp p word pos) = read hp p pos := by
  rw [finish_events]
  funext a
  unfold read
  apply congrArg (p a)
  apply Fin.ext
  simp [endPos_coordinate, Nat.add_mod, hcounts]

theorem distinct_iff_nodup (xs : List (List Nat)) : ECC.distinct xs = true ↔ xs.Nodup := by
  induction xs with
  | nil => simp [ECC.distinct]
  | cons x xs ih => simp [ECC.distinct, ih, List.nodup_cons]

theorem encoded_nodup_iff {q : Nat} {n : Fin q → Nat} (xs : List (Vertex n)) :
    (xs.map encode).Nodup ↔ xs.Nodup := by
  rw [List.nodup_iff_eq_of_getElem_eq, List.nodup_iff_eq_of_getElem_eq]
  constructor
  · intro h i j hi hj heq
    apply h i j (by simpa only [List.length_map] using hi) (by simpa only [List.length_map] using hj)
    simpa only [List.getElem_map] using congrArg encode heq
  · intro h i j hi hj heq
    have hi' : i < xs.length := by simpa only [List.length_map] using hi
    have hj' : j < xs.length := by simpa only [List.length_map] using hj
    exact h i j hi' hj' (encode_injective xs[i] xs[j] (by
      simpa only [List.getElem_map] using heq))

theorem executable_collision_iff {q : Nat} {n period : Fin q → Nat}
    (hp : ∀ a, 0 < period a) (p : Templates n period)
    (word : List (Fin q)) (pos : Fin q → Nat) :
    ECC.distinct (ECC.vertices (rawPatterns p) (word.map Fin.val) (rawPos pos)) = true ↔
      (before (read hp p pos) (events hp p word pos)).Nodup := by
  rw [vertices_eq_encoded_departures hp, distinct_iff_nodup, encoded_nodup_iff]

theorem executable_injectivity_iff {q : Nat} {n period : Fin q → Nat}
    (hp : ∀ a, 0 < period a) (p : Templates n period)
    (word : List (Fin q)) (pos : Fin q → Nat) :
    ECC.distinct (ECC.vertices (rawPatterns p) (word.map Fin.val) (rawPos pos)) = true ↔
      TraceInjective (trace (read hp p pos) (events hp p word pos)) := by
  rw [executable_collision_iff hp, trace_injective_iff_nodup]

theorem executable_cycle_iff {q : Nat} {n period : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (hp : ∀ a, 0 < period a) (p : Templates n period)
    (word : List (Fin q)) (pos : Fin q → Nat) (hm : 0 < (events hp p word pos).length) :
    (CycleEmbedding hm edge (trace (read hp p pos) (events hp p word pos)) ∧
      finish (read hp p pos) (events hp p word pos) = read hp p pos) ↔
    3 ≤ (events hp p word pos).length ∧
      ECC.distinct (ECC.vertices (rawPatterns p) (word.map Fin.val) (rawPos pos)) = true ∧
      ∀ a, FactorWalk edge a (read hp p pos a) (project (events hp p word pos) a) ∧
        advance (read hp p pos a) (project (events hp p word pos) a) = read hp p pos a := by
  rw [cycle_data_iff, executable_collision_iff hp]

#print axioms encode_injective
#print axioms read_update
#print axioms get_modify_safe
#print axioms raw_tick
#print axioms raw_read
#print axioms vertices_eq_encoded_departures
#print axioms events_axes
#print axioms events_length
#print axioms finish_events
#print axioms endPos_coordinate
#print axioms closure_if_periods_divide_steps
#print axioms distinct_iff_nodup
#print axioms encoded_nodup_iff
#print axioms executable_collision_iff
#print axioms executable_injectivity_iff
#print axioms executable_cycle_iff

end ECC.ExecutableTrace
