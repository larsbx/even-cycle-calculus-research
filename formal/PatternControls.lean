import PatternGenerator

namespace ECC.PatternControls
open ECC.PatternGenerator

theorem four_patterns_exact : ECC.patterns 4 = [ECC.A, ECC.B, ECC.C, ECC.D] := by decide

theorem bounded_inventory_sizes :
    ([0, 1, 2, 3, 4, 5, 6].map fun n => (ECC.patterns n).length) =
      [0, 0, 1, 1, 4, 11, 41] := by decide

theorem motif_words_occur_once :
    (ECC.patterns 5).count [0, 1, 2, 3, 4] = 1 ∧
    (ECC.patterns 6).count [0, 1, 2, 0, 3, 4] = 1 := by
  constructor
  · exact (patterns_nodup 5).count_of_mem (by decide)
  · exact (patterns_nodup 6).count_of_mem (by decide)

theorem adjacent_collision_rejected : [0, 1, 1, 2] ∉ ECC.patterns 4 := by decide

theorem closing_collision_rejected : [0, 1, 2, 0] ∉ ECC.patterns 4 := by decide

theorem skipped_label_rejected : [0, 2, 1, 2] ∉ ECC.patterns 4 := by decide

theorem nonzero_first_rejected : [1, 0, 1, 0] ∉ ECC.patterns 4 := by decide

#print axioms four_patterns_exact
#print axioms bounded_inventory_sizes
#print axioms motif_words_occur_once
#print axioms adjacent_collision_rejected
#print axioms closing_collision_rejected
#print axioms skipped_label_rejected
#print axioms nonzero_first_rejected

end ECC.PatternControls
