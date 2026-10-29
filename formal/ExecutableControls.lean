import ExecutableTrace
import CycleControls

namespace ECC.ExecutableControls
open ECC.CollisionBridge ECC.EventShuffle ECC.ClosedWalk ECC.EventControls
open ECC.ClosedControls ECC.CycleTrace ECC.ExecutableTrace

def fourPeriods (_ : Fin 2) : Nat := 4
theorem fourPositive (a : Fin 2) : 0 < fourPeriods a := Nat.zero_lt_succ 3
def prismTemplate (a : Fin 2) (i : Fin (fourPeriods a)) : Fin (sizes a) :=
  if h : a.val = 0 then ⟨i.val, by simp only [sizes, h, ite_true]; exact i.isLt⟩
  else ⟨i.val % 2, by simp only [sizes, h, ite_false]; exact Nat.mod_lt i.val (by decide : 0 < 2)⟩
def zeroPos {q : Nat} (_ : Fin q) : Nat := 0

theorem prism_literal_inputs :
    rawPatterns prismTemplate = [[0, 1, 2, 3], [0, 1, 0, 1]] ∧
    (axes prism).map Fin.val = [1, 0, 1, 0, 1, 0, 1, 0] ∧
    rawPos (zeroPos : Fin 2 → Nat) = [0, 0] := by decide

theorem prism_events_match : events fourPositive prismTemplate (axes prism) zeroPos = prism := by decide

theorem prism_collision_passes :
    ECC.distinct (ECC.vertices (rawPatterns prismTemplate) ((axes prism).map Fin.val)
      (rawPos (zeroPos : Fin 2 → Nat))) = true := by
  apply (executable_collision_iff fourPositive prismTemplate (axes prism) zeroPos).mpr
  rw [prism_events_match]
  have root_eq : read fourPositive prismTemplate zeroPos = origin := by
    funext a
    apply Fin.ext
    by_cases h : a.val = 0 <;> simp [ExecutableTrace.read, prismTemplate, zeroPos, origin, h]
  rw [root_eq]
  exact prism_departures_distinct

theorem colliding_shuffle_fails :
    events fourPositive prismTemplate (axes colliding) zeroPos = colliding ∧
    ECC.distinct (ECC.vertices (rawPatterns prismTemplate) ((axes colliding).map Fin.val)
      (rawPos (zeroPos : Fin 2 → Nat))) = false := by decide

theorem trianglePositive (a : Fin 3) : 0 < triangleSizes a := by
  dsimp [triangleSizes]
  split <;> decide
def triangleTemplate (a : Fin 3) (i : Fin (triangleSizes a)) : Fin (triangleSizes a) := i

theorem paired_literal_inputs_and_events :
    rawPatterns triangleTemplate = [[0, 1], [0, 1, 2], [0, 1, 2]] ∧
    (axes paired).map Fin.val = [0, 1, 0, 1, 2, 1, 2, 2] ∧
    events trianglePositive triangleTemplate (axes paired) zeroPos = paired := by decide

theorem paired_collision_passes :
    ECC.distinct (ECC.vertices (rawPatterns triangleTemplate) ((axes paired).map Fin.val)
      (rawPos (zeroPos : Fin 3 → Nat))) = true := by
  apply (executable_collision_iff trianglePositive triangleTemplate (axes paired) zeroPos).mpr
  rw [paired_literal_inputs_and_events.2.2]
  exact paired_triangles_valid_simple.2.2

theorem profile_counts_give_closure :
    finish (ExecutableTrace.read fourPositive prismTemplate zeroPos)
        (events fourPositive prismTemplate (axes prism) zeroPos) =
      ExecutableTrace.read fourPositive prismTemplate zeroPos ∧
    finish (ExecutableTrace.read trianglePositive triangleTemplate zeroPos)
        (events trianglePositive triangleTemplate (axes paired) zeroPos) =
      ExecutableTrace.read trianglePositive triangleTemplate zeroPos := by
  constructor
  · exact closure_if_periods_divide_steps fourPositive prismTemplate (axes prism) zeroPos (by decide)
  · exact closure_if_periods_divide_steps trianglePositive triangleTemplate (axes paired) zeroPos (by decide)

/- The raw recursion is total via defaults. The bridge does not interpret
   an empty template or an out-of-range axis as legitimate coordinate data. -/
theorem malformed_default_controls :
    ECC.vertices [[]] [0, 0] [0] = [[0], [0]] ∧
    ECC.vertices [[0, 1]] [1] [0] = [[0]] ∧
    ECC.distinct (ECC.vertices [[0, 1]] [1] [0]) = true ∧
    (1 : Nat) ∉ List.range 1 := by decide

#print axioms prism_literal_inputs
#print axioms prism_events_match
#print axioms prism_collision_passes
#print axioms colliding_shuffle_fails
#print axioms paired_literal_inputs_and_events
#print axioms paired_collision_passes
#print axioms profile_counts_give_closure
#print axioms malformed_default_controls

end ECC.ExecutableControls
