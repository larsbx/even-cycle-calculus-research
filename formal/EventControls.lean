import EventShuffle

namespace ECC.EventControls
open ECC.CollisionBridge ECC.EventShuffle

def sizes (a : Fin 2) : Nat := if a.val = 0 then 4 else 2
instance (a : Fin 2) : NeZero (sizes a) := ⟨by dsimp [sizes]; split <;> decide⟩
def origin : Vertex sizes := fun a => ⟨0, by dsimp [sizes]; split <;> decide⟩
def display (v : Vertex sizes) : Nat × Nat := ((v 0).val, (v 1).val)

/- The recorded ordinary c8 witness in C4 square K2, with the final root. -/
def prism : List (Event sizes) :=
  [⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨0, 3⟩, ⟨1, 0⟩, ⟨0, 0⟩]

theorem prism_projections :
    ((project prism 0).map Fin.val, (project prism 1).map Fin.val) =
      ([1, 2, 3, 0], [1, 0, 1, 0]) := by decide

theorem prism_vertex_path :
    ((replay origin prism).map display) =
      [(0, 0), (0, 1), (1, 1), (1, 0), (2, 0), (2, 1), (3, 1), (3, 0), (0, 0)] := by decide

theorem short_queue_fails :
    (weave (axes prism) (setQueue (project prism) 0 [1, 2, 3])).isNone = true := by decide

def extra : Queues sizes := setQueue (project prism) 0 [1, 2, 3, 0, 0]

theorem extra_queue_not_exact :
    (match weave (axes prism) extra with
     | none => false
     | some (_, remaining) => (remaining 0).length == 1) = true ∧
    ¬ Compatible (axes prism) extra := by
  constructor
  · decide
  · intro h
    have bad : (5 : Nat) = 4 := h 0
    exact (by decide : (5 : Nat) ≠ 4) bad

/- A target changing both coordinates cannot be recovered by one stated event. -/
theorem stationarity_required :
    display (update origin ⟨0, 1⟩) = (1, 0) ∧
      display (update origin ⟨0, 1⟩) ≠ (1, 1) := by decide

#print axioms prism_projections
#print axioms prism_vertex_path
#print axioms short_queue_fails
#print axioms extra_queue_not_exact
#print axioms stationarity_required

end ECC.EventControls
