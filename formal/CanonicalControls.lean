import CanonicalTrace

namespace ECC.CanonicalControls
open ECC.CanonicalTrace

def word (t : Fin 5) : Fin 3 :=
  if t.val = 0 then 0 else if t.val = 1 then 1 else
  if t.val = 2 then 0 else if t.val = 3 then 2 else 1

theorem first_positions :
    ((List.finRange 5).map fun t => (first word t).val) = [0, 1, 0, 3, 1] := by decide

/- First positions and restricted-growth ordinal labels are distinct encodings. -/
theorem positions_are_not_ordinals : (first word (3 : Fin 5)).val ≠ (word 3).val := by decide

def collapse (label : Fin 3) : Fin 2 := if label.val = 1 then 1 else 0

theorem noninjective_relabel_changes_first :
    first (fun t => collapse (word t)) (3 : Fin 5) ≠ first word 3 := by decide

#print axioms first_positions
#print axioms positions_are_not_ordinals
#print axioms noninjective_relabel_changes_first

end ECC.CanonicalControls
