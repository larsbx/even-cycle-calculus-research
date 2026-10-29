import NormalizedPattern

namespace ECC.NormalizedControls
open ECC.NormalizedPattern ECC.RankCompression

def fourTrace (k t : Fin 4) : Fin 10 :=
  match k.val, t.val with
  | 0, 0 => 8 | 0, 1 => 2 | 0, 2 => 8 | 0, _ => 2
  | 1, 0 => 9 | 1, 1 => 3 | 1, 2 => 9 | 1, _ => 7
  | 2, 0 => 9 | 2, 1 => 3 | 2, 2 => 7 | 2, _ => 3
  | _, 0 => 4 | _, 1 => 8 | _, 2 => 2 | _, _ => 6

theorem four_normalized_words :
    ([0, 1, 2, 3] : List (Fin 4)).map (fun k => word (fourTrace k)) =
      [ECC.A, ECC.B, ECC.C, ECC.D] := by decide

theorem four_patterns_once : ∀ k : Fin 4,
    word (fourTrace k) ∈ ECC.patterns 4 ∧ (ECC.patterns 4).count (word (fourTrace k)) = 1 := by
  have hp : ∀ k : Fin 4, Proper (fourTrace k) := by unfold Proper; decide
  exact fun k => ⟨normalized_mem_patterns _ (hp k), normalized_occurs_once _ (hp k)⟩

def triangleTrace (t : Fin 3) : Fin 10 := match t.val with
  | 0 => 8 | 1 => 2 | _ => 5

theorem odd_triangle_normalization : word triangleTrace = ECC.T ∧
    (ECC.patterns 3).count (word triangleTrace) = 1 :=
  ⟨by decide, normalized_occurs_once _ (by unfold Proper; decide)⟩

def bowtieTrace (t : Fin 6) : Fin 10 := match t.val with
  | 0 => 8 | 1 => 2 | 2 => 5 | 3 => 8 | 4 => 9 | _ => 1

theorem repeated_projection_allowed : word bowtieTrace = [0, 1, 2, 0, 3, 4] ∧
    (ECC.patterns 6).count (word bowtieTrace) = 1 :=
  ⟨by decide, normalized_occurs_once _ (by unfold Proper; decide)⟩

def relabeledTrace (t : Fin 4) : Fin 7 := match t.val with
  | 0 => 3 | 1 => 0 | 2 => 3 | _ => 6

theorem equal_pattern_relabeling : word (fourTrace 1) = word relabeledTrace :=
  word_eq_of_equality _ _ (by decide)

def stutterTrace (t : Fin 4) : Fin 10 := match t.val with
  | 0 => 8 | 1 => 8 | 2 => 2 | _ => 5

theorem adjacent_collapse_rejected : word stutterTrace ∉ ECC.patterns 4 := by
  intro h
  have hp := (normalized_mem_iff_proper stutterTrace).mp h
  exact hp.1 (0 : Fin 3) rfl

def closingTrace (t : Fin 4) : Fin 10 := match t.val with
  | 0 => 8 | 1 => 2 | 2 => 5 | _ => 8

theorem closing_collapse_rejected : word closingTrace ∉ ECC.patterns 4 := by
  intro h
  have hp := (normalized_mem_iff_proper closingTrace).mp h
  exact hp.2 rfl

theorem assignment_reconstruction : (positions (fourTrace 1)).length = 3 ∧
    (List.ofFn fun t => decode (fourTrace 1) (encode (fourTrace 1) t)) = List.ofFn (fourTrace 1) := by
  constructor
  · decide
  · apply congrArg List.ofFn
    funext t
    exact decode_encode _ t

theorem selected_step_controls :
    (∀ i j, SelectedStep (fourTrace 1) i j → decode (fourTrace 1) i ≠ decode (fourTrace 1) j) ∧
    (∀ i, ¬ SelectedStep (fourTrace 1) i i) := by
  constructor
  · exact selected_step_preserved (fourTrace 1) (· ≠ ·) (by decide)
  · exact selected_loopless (fourTrace 1) (· ≠ ·) (fun _ h => h rfl) (by decide)

/- In K10, the two wedge leaves have an extra edge. The assignment remains
   valid although that edge is not a selected quotient step in either direction. -/
theorem noninduced_extra_edge : ∃ i j : Fin (positions (fourTrace 1)).length,
    decode (fourTrace 1) i ≠ decode (fourTrace 1) j ∧
      ¬ SelectedStep (fourTrace 1) i j ∧ ¬ SelectedStep (fourTrace 1) j i := by
  refine ⟨⟨1, by decide⟩, ⟨2, by decide⟩, by decide, ?_, ?_⟩ <;>
    unfold SelectedStep <;> decide

#print axioms four_normalized_words
#print axioms four_patterns_once
#print axioms odd_triangle_normalization
#print axioms repeated_projection_allowed
#print axioms equal_pattern_relabeling
#print axioms adjacent_collapse_rejected
#print axioms closing_collapse_rejected
#print axioms assignment_reconstruction
#print axioms selected_step_controls
#print axioms noninduced_extra_edge

end ECC.NormalizedControls
