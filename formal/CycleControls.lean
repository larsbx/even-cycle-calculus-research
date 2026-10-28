import CycleTrace
import ClosedControls

namespace ECC.CycleControls
open ECC.CollisionBridge ECC.EventShuffle ECC.ClosedWalk ECC.EventControls
open ECC.ClosedControls ECC.CycleTrace

theorem prism_is_cycle :
    CycleEmbedding (by decide : 0 < prism.length) prismEdge (trace origin prism) :=
  (closed_cycle_iff prismEdge origin prism (by decide) prism_valid_closed.2).mpr
    ⟨by decide, prism_departures_distinct, prism_valid_closed.1⟩

theorem paired_is_cycle :
    CycleEmbedding (by decide : 0 < paired.length) completeEdge (trace triangleRoot paired) :=
  (closed_cycle_iff completeEdge triangleRoot paired (by decide)
    paired_triangles_valid_simple.2.1).mpr
      ⟨by decide, paired_triangles_valid_simple.2.2, paired_triangles_valid_simple.1⟩

theorem colliding_is_not_cycle :
    ¬ CycleEmbedding (by decide : 0 < colliding.length) prismEdge (trace origin colliding) := by
  intro h
  have hi := (closed_cycle_iff prismEdge origin colliding (by decide)
    colliding_closed_walk_not_cycle.2.1).mp h
  exact colliding_closed_walk_not_cycle.2.2 hi.2.1

theorem invalid_closed_trace_not_cycle :
    ¬ CycleEmbedding (by decide : 0 < jumping.length) prismEdge (trace origin jumping) := by
  intro h
  have hi := (closed_cycle_iff prismEdge origin jumping (by decide) closure_not_edges.1).mp h
  exact closure_not_edges.2 hi.2.2

/- An endpoint is not part of the departure trace. Changing just that endpoint
   can leave a valid modular cycle trace while breaking the event walk. -/
def openPrism : List (Event sizes) :=
  [⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨0, 3⟩, ⟨1, 0⟩, ⟨0, 1⟩]

theorem open_endpoint_same_trace : trace origin openPrism = trace origin prism := by
  funext t
  rfl

theorem closure_assumption_needed :
    CycleEmbedding (by decide : 0 < openPrism.length) prismEdge (trace origin openPrism) ∧
      ¬ Valid prismEdge origin openPrism ∧ finish origin openPrism ≠ origin := by
  constructor
  · rw [open_endpoint_same_trace]
    exact prism_is_cycle
  constructor
  · dsimp [Valid, openPrism, prismEdge, update, origin]
    decide
  · decide

def backtrack : List (Event sizes) := [⟨1, 1⟩, ⟨1, 0⟩]

theorem length_bound_needed :
    Valid prismEdge origin backtrack ∧ finish origin backtrack = origin ∧
      (before origin backtrack).Nodup ∧
      ¬ CycleEmbedding (by decide : 0 < backtrack.length) prismEdge (trace origin backtrack) := by
  constructor
  · dsimp [Valid, backtrack, prismEdge, update, origin]
    decide
  refine ⟨by decide, by decide, ?_⟩
  intro h
  exact (by decide : ¬ (3 ≤ backtrack.length)) h.1

#print axioms prism_is_cycle
#print axioms paired_is_cycle
#print axioms colliding_is_not_cycle
#print axioms invalid_closed_trace_not_cycle
#print axioms open_endpoint_same_trace
#print axioms closure_assumption_needed
#print axioms length_bound_needed

end ECC.CycleControls
