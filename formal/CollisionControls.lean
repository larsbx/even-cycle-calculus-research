import CollisionBridge

namespace ECC.CollisionControls
open ECC.CollisionBridge

def SquareEdge (u v : Fin 4) : Prop :=
  (u.val + 1) % 4 = v.val ∨ (v.val + 1) % 4 = u.val

def FoldSquare (u : Fin 4) : Fin 2 := ⟨u.val % 2, Nat.mod_lt _ (by decide)⟩
def SquareShape (t : Fin 4) : Vertex (fun _ : Fin 1 => 4) := fun _ => t
def FoldedShape (t : Fin 4) : Vertex (fun _ : Fin 1 => 2) :=
  Decode (fun _ => FoldSquare) (SquareShape t)

/- A graph homomorphism from C4 to K2 preserves all selected edges. -/
theorem fold_edges_preserved :
    ∀ u v, SquareEdge u v → FoldSquare u ≠ FoldSquare v := by
  unfold SquareEdge
  decide

theorem square_is_cycle :
    CycleEmbedding (by decide : 0 < 4) (fun _ : Fin 1 => SquareEdge) SquareShape := by
  refine ⟨by decide, ?_, ?_⟩
  · intro s t h
    exact congrFun h 0
  · unfold CartesianAdj CoordinateStep SquareShape SquareEdge Next
    decide

/- Nevertheless the decoded closed traversal repeats vertices 0 and 2. -/
theorem folded_trace_not_injective : ¬ TraceInjective FoldedShape := by
  intro h
  have bad : (0 : Fin 4) = 2 := h 0 2 (by
    funext a
    change FoldSquare (0 : Fin 4) = FoldSquare (2 : Fin 4)
    decide)
  exact (by decide : (0 : Fin 4) ≠ 2) bad

def UnusedShape (_ : Fin 1) : Vertex (fun _ : Fin 1 => 2) := fun _ => 0
def IdentityAssignment (_ : Fin 1) (label : Fin 2) : Fin 3 := ⟨label.val, by omega⟩
def OtherAssignment (_ : Fin 1) (label : Fin 2) : Fin 3 :=
  if label.val = 0 then 0 else 2

/- Both assignments are injective, but an unvisited label cannot be recovered. -/
theorem unseen_assignments_injective :
    FactorInjective IdentityAssignment ∧ FactorInjective OtherAssignment := by
  unfold FactorInjective
  decide

theorem unseen_assignments_same_trace :
    (fun t => Decode IdentityAssignment (UnusedShape t)) =
      (fun t => Decode OtherAssignment (UnusedShape t)) := by
  funext t a
  rfl

theorem unseen_assignments_differ : IdentityAssignment ≠ OtherAssignment := by
  intro h
  have bad := congrFun (congrFun h 0) 1
  exact (by decide : IdentityAssignment 0 1 ≠ OtherAssignment 0 1) bad

#print axioms fold_edges_preserved
#print axioms square_is_cycle
#print axioms folded_trace_not_injective
#print axioms unseen_assignments_injective
#print axioms unseen_assignments_same_trace
#print axioms unseen_assignments_differ

end ECC.CollisionControls
