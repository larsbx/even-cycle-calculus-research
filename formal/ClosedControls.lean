import ClosedWalk
import EventControls

namespace ECC.ClosedControls
open ECC.CollisionBridge ECC.EventShuffle ECC.ClosedWalk ECC.EventControls

/- Constructive finite function equality, with no classical choice instance. -/
instance {q : Nat} {n : Fin q → Nat} : DecidableEq (Vertex n) :=
  fun v w => decidable_of_iff (∀ a, v a = w a) ⟨fun h => funext h, fun h a => congrFun h a⟩

def prismEdge (a : Fin 2) (x y : Fin (sizes a)) : Prop :=
  if a.val = 0 then (x.val + 1) % 4 = y.val ∨ (y.val + 1) % 4 = x.val else x ≠ y

theorem prism_valid_closed : Valid prismEdge origin prism ∧ finish origin prism = origin := by
  constructor
  · dsimp [Valid, prism, prismEdge, update, origin]
    decide
  · decide

theorem prism_departures_distinct : (before origin prism).Nodup := by decide

theorem prism_full_replay_repeats : ¬ (replay origin prism).Nodup :=
  closed_replay_not_nodup origin prism (by decide) prism_valid_closed.2

/- Same closed coordinate queues, different interleaving, with an early return. -/
def colliding : List (Event sizes) :=
  [⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]

theorem colliding_same_queues : ∀ a, project colliding a = project prism a := by decide

theorem colliding_closed_walk_not_cycle :
    Valid prismEdge origin colliding ∧ finish origin colliding = origin ∧
      ¬ (before origin colliding).Nodup := by
  constructor
  · dsimp [Valid, colliding, prismEdge, update, origin]
    decide
  constructor <;> decide

def jumping : List (Event sizes) :=
  [⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 3⟩, ⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩, ⟨0, 0⟩]

theorem closure_not_edges : finish origin jumping = origin ∧ ¬ Valid prismEdge origin jumping := by
  constructor
  · decide
  · dsimp [Valid, jumping, prismEdge, update, origin]
    decide

def triangleSizes (a : Fin 3) : Nat := if a.val = 0 then 2 else 3
instance (a : Fin 3) : NeZero (triangleSizes a) :=
  ⟨by dsimp [triangleSizes]; split <;> decide⟩
def triangleRoot : Vertex triangleSizes :=
  fun a => ⟨0, by dsimp [triangleSizes]; split <;> decide⟩
def completeEdge (a : Fin 3) (x y : Fin (triangleSizes a)) : Prop := x ≠ y
def paired : List (Event triangleSizes) :=
  [⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 0⟩]

theorem paired_triangles_valid_simple :
    Valid completeEdge triangleRoot paired ∧ finish triangleRoot paired = triangleRoot ∧
      (before triangleRoot paired).Nodup := by
  constructor
  · dsimp [Valid, paired, completeEdge, update, triangleRoot]
    decide
  constructor <;> decide

theorem paired_triangle_profile :
    ((project paired 0).map Fin.val, (project paired 1).map Fin.val,
      (project paired 2).map Fin.val) = ([1, 0], [1, 2, 0], [1, 2, 0]) ∧
    [steps (axes paired) 0, steps (axes paired) 1, steps (axes paired) 2] = [2, 3, 3] := by
  decide

theorem paired_closed_factor_walks : ∀ a,
    FactorWalk completeEdge a (triangleRoot a) (project paired a) ∧
      advance (triangleRoot a) (project paired a) = triangleRoot a :=
  (closed_valid_iff completeEdge triangleRoot paired).mp
    ⟨paired_triangles_valid_simple.1, paired_triangles_valid_simple.2.1⟩

#print axioms prism_valid_closed
#print axioms prism_departures_distinct
#print axioms prism_full_replay_repeats
#print axioms colliding_same_queues
#print axioms colliding_closed_walk_not_cycle
#print axioms closure_not_edges
#print axioms paired_triangles_valid_simple
#print axioms paired_triangle_profile
#print axioms paired_closed_factor_walks

end ECC.ClosedControls
