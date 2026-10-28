import CollisionBridge

/- Lossless finite coordinate-event projection and interleaving.
   Values and coordinate axes are finite; no graph-counting conclusion is assumed. -/
namespace ECC.EventShuffle
open ECC.CollisionBridge

abbrev Event {q : Nat} (n : Fin q → Nat) := (a : Fin q) × Fin (n a)
abbrev Queues {q : Nat} (n : Fin q → Nat) := (a : Fin q) → List (Fin (n a))

def axes {q : Nat} {n : Fin q → Nat} (es : List (Event n)) : List (Fin q) :=
  es.map Sigma.fst

def project {q : Nat} {n : Fin q → Nat} :
    List (Event n) → (a : Fin q) → List (Fin (n a))
  | [], _ => []
  | e :: es, a => if h : e.fst = a then (h ▸ e.snd) :: project es a else project es a

def setQueue {q : Nat} {n : Fin q → Nat} (queues : Queues n)
    (a : Fin q) (tail : List (Fin (n a))) : Queues n :=
  fun b => if h : b = a then h.symm ▸ tail else queues b

def emptyQueues {q : Nat} (n : Fin q → Nat) : Queues n := fun _ => []

def weave {q : Nat} {n : Fin q → Nat} :
    List (Fin q) → Queues n → Option (List (Event n) × Queues n)
  | [], queues => some ([], queues)
  | a :: word, queues =>
      match queues a with
      | [] => none
      | value :: tail =>
          match weave word (setQueue queues a tail) with
          | none => none
          | some (es, rest) => some (⟨a, value⟩ :: es, rest)

def steps {q : Nat} : List (Fin q) → Fin q → Nat
  | [], _ => 0
  | b :: word, a => if b = a then steps word a + 1 else steps word a

def Compatible {q : Nat} {n : Fin q → Nat} (word : List (Fin q)) (queues : Queues n) :=
  ∀ a, (queues a).length = steps word a

theorem project_head {q : Nat} {n : Fin q → Nat} (a : Fin q)
    (value : Fin (n a)) (es : List (Event n)) :
    project (⟨a, value⟩ :: es) a = value :: project es a := by simp [project]

theorem project_other {q : Nat} {n : Fin q → Nat} (a b : Fin q)
    (value : Fin (n a)) (es : List (Event n)) (h : a ≠ b) :
    project (⟨a, value⟩ :: es) b = project es b := by simp [project, h]

theorem project_length {q : Nat} {n : Fin q → Nat} (es : List (Event n)) (a : Fin q) :
    (project es a).length = steps (axes es) a := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨b, value⟩
    by_cases h : b = a
    · subst b
      simp [project, axes, steps, ih]
    · simp [project, axes, steps, h, ih]

theorem projection_compatible {q : Nat} {n : Fin q → Nat} (es : List (Event n)) :
    Compatible (axes es) (project es) := project_length es

theorem queue_after_project_head {q : Nat} {n : Fin q → Nat} (a : Fin q)
    (value : Fin (n a)) (es : List (Event n)) :
    setQueue (project (⟨a, value⟩ :: es)) a (project es a) = project es := by
  funext b
  by_cases h : a = b
  · subst b
    simp [setQueue]
  · simp [setQueue, project, h, Ne.symm h]

theorem weave_project {q : Nat} {n : Fin q → Nat} (es : List (Event n)) :
    weave (axes es) (project es) = some (es, emptyQueues n) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a, value⟩
    change weave (a :: axes es) (project (⟨a, value⟩ :: es)) = _
    simp only [weave, project_head, queue_after_project_head, ih]

theorem weave_sound {q : Nat} {n : Fin q → Nat} (word : List (Fin q))
    (queues : Queues n) (es : List (Event n)) (rest : Queues n)
    (h : weave word queues = some (es, rest)) :
    axes es = word ∧ ∀ a, project es a ++ rest a = queues a := by
  induction word generalizing queues es rest with
  | nil =>
    simp only [weave, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => rfl⟩
  | cons a word ih =>
    cases hq : queues a with
    | nil => simp [weave, hq] at h
    | cons value tail =>
      cases hw : weave word (setQueue queues a tail) with
      | none => simp [weave, hq, hw] at h
      | some result =>
        rcases result with ⟨events, remaining⟩
        simp only [weave, hq, hw, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have sound := ih _ _ _ hw
        refine ⟨?_, ?_⟩
        · change a :: axes events = a :: word
          exact congrArg (a :: ·) sound.1
        · intro b
          have coordinate := sound.2 b
          by_cases hb : a = b
          · subst b
            simpa [project, setQueue, hq] using congrArg (value :: ·) coordinate
          · simpa [project, setQueue, hb, Ne.symm hb] using coordinate

theorem compatible_tail {q : Nat} {n : Fin q → Nat} (a : Fin q)
    (word : List (Fin q)) (queues : Queues n) (value : Fin (n a))
    (tail : List (Fin (n a))) (hq : queues a = value :: tail)
    (h : Compatible (a :: word) queues) : Compatible word (setQueue queues a tail) := by
  intro b
  have bound := h b
  by_cases hb : a = b
  · subst b
    have short : tail.length = steps word a := by simpa [steps, hq] using bound
    simpa [setQueue] using short
  · simpa [steps, setQueue, hb, Ne.symm hb] using bound

theorem weave_complete {q : Nat} {n : Fin q → Nat} (word : List (Fin q))
    (queues : Queues n) (h : Compatible word queues) :
    ∃ es, weave word queues = some (es, emptyQueues n) := by
  induction word generalizing queues with
  | nil =>
    have empty : queues = emptyQueues n := by
      funext a
      exact List.eq_nil_of_length_eq_zero (h a)
    exact ⟨[], by simp [weave, empty]⟩
  | cons a word ih =>
    cases hq : queues a with
    | nil =>
      have bound := h a
      simp only [steps, eq_self, ite_true, hq, List.length_nil] at bound
      exact False.elim (by omega)
    | cons value tail =>
      obtain ⟨events, hevents⟩ := ih _ (compatible_tail a word queues value tail hq h)
      exact ⟨⟨a, value⟩ :: events, by simp [weave, hq, hevents]⟩

theorem compatible_reconstruction {q : Nat} {n : Fin q → Nat} (word : List (Fin q))
    (queues : Queues n) (h : Compatible word queues) :
    ∃ es, axes es = word ∧ project es = queues := by
  obtain ⟨es, he⟩ := weave_complete word queues h
  have sound := weave_sound word queues es (emptyQueues n) he
  refine ⟨es, sound.1, ?_⟩
  funext a
  simpa [emptyQueues] using sound.2 a

theorem reconstruction_unique {q : Nat} {n : Fin q → Nat}
    (es other : List (Event n)) (hw : axes es = axes other)
    (hq : project es = project other) : es = other := by
  have same := weave_project es
  rw [hw, hq, weave_project other] at same
  exact congrArg Prod.fst (Option.some.inj same).symm

theorem reconstruction_iff_compatible {q : Nat} {n : Fin q → Nat}
    (word : List (Fin q)) (queues : Queues n) :
    (∃ es, axes es = word ∧ project es = queues) ↔ Compatible word queues := by
  constructor
  · rintro ⟨es, rfl, rfl⟩
    exact projection_compatible es
  · exact compatible_reconstruction word queues

def update {q : Nat} {n : Fin q → Nat} (v : Vertex n) (e : Event n) : Vertex n :=
  fun a => if h : a = e.fst then h.symm ▸ e.snd else v a

theorem update_of_stationary {q : Nat} {n : Fin q → Nat} (a : Fin q)
    (v w : Vertex n) (h : ∀ b, b ≠ a → v b = w b) : update v ⟨a, w a⟩ = w := by
  funext b
  by_cases hb : b = a
  · subst b
    simp [update]
  · simp [update, hb, h b hb]

theorem update_of_coordinate_step {q : Nat} {n : Fin q → Nat} (a : Fin q)
    (v w : Vertex n) (h : CoordinateStep a v w) : update v ⟨a, w a⟩ = w :=
  update_of_stationary a v w h.2

def replay {q : Nat} {n : Fin q → Nat} : Vertex n → List (Event n) → List (Vertex n)
  | v, [] => [v]
  | v, e :: es => v :: replay (update v e) es

def transitionEvents {q : Nat} {n : Fin q → Nat}
    (records : List (Fin q × Vertex n)) : List (Event n) :=
  records.map fun r => ⟨r.fst, r.snd r.fst⟩

theorem transition_axis_word {q : Nat} {n : Fin q → Nat}
    (records : List (Fin q × Vertex n)) : axes (transitionEvents records) = records.map Prod.fst := by
  simp [axes, transitionEvents, List.map_map, Function.comp_def]

def Coherent {q : Nat} {n : Fin q → Nat} : Vertex n → List (Fin q × Vertex n) → Prop
  | _, [] => True
  | v, (a, w) :: records => CoordinateStep a v w ∧ Coherent w records

theorem replay_transitions {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (records : List (Fin q × Vertex n)) (h : Coherent v records) :
    replay v (transitionEvents records) = v :: records.map Prod.snd := by
  induction records generalizing v with
  | nil => rfl
  | cons r records ih =>
    rcases r with ⟨a, w⟩
    have step := update_of_coordinate_step a v w h.1
    simpa only [transitionEvents, List.map_cons, replay, step] using congrArg (v :: ·) (ih w h.2)

theorem weave_replay_transitions {q : Nat} {n : Fin q → Nat} (v : Vertex n)
    (records : List (Fin q × Vertex n)) (h : Coherent v records) :
    (weave (axes (transitionEvents records)) (project (transitionEvents records))).map
      (fun result => replay v result.fst) = some (v :: records.map Prod.snd) := by
  rw [weave_project]
  exact congrArg some (replay_transitions v records h)

#print axioms project_head
#print axioms project_other
#print axioms project_length
#print axioms projection_compatible
#print axioms queue_after_project_head
#print axioms weave_project
#print axioms weave_sound
#print axioms compatible_tail
#print axioms weave_complete
#print axioms compatible_reconstruction
#print axioms reconstruction_unique
#print axioms reconstruction_iff_compatible
#print axioms update_of_stationary
#print axioms update_of_coordinate_step
#print axioms transition_axis_word
#print axioms replay_transitions
#print axioms weave_replay_transitions

end ECC.EventShuffle
