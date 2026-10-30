import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem edge_cell_3_0 : countFrom 8 [3, 0] [3, 2, 2, 1] [A, E, E, E] = 88 := by decide +kernel
theorem edge_cell_3_1 : countFrom 8 [3, 1] [4, 1, 2, 1] [A, E, E, E] = 22 := by decide +kernel
theorem edge_cell_3_2 : countFrom 8 [3, 2] [4, 2, 1, 1] [A, E, E, E] = 22 := by decide +kernel
theorem edge_cell_3_3 : countFrom 8 [3, 3] [4, 2, 2, 0] [A, E, E, E] = 0 := by decide +kernel

theorem edge_row_3 : row [4, 2, 2, 2] [A, E, E, E] 3 = [88, 22, 22, 0] := by
  change [countFrom 8 [3, 0] [3, 2, 2, 1] [A, E, E, E],
    countFrom 8 [3, 1] [4, 1, 2, 1] [A, E, E, E],
    countFrom 8 [3, 2] [4, 2, 1, 1] [A, E, E, E],
    countFrom 8 [3, 3] [4, 2, 2, 0] [A, E, E, E]] = [88, 22, 22, 0]
  rw [edge_cell_3_0, edge_cell_3_1, edge_cell_3_2, edge_cell_3_3]

#print axioms edge_cell_3_0
#print axioms edge_cell_3_1
#print axioms edge_cell_3_2
#print axioms edge_cell_3_3
#print axioms edge_row_3
end ECC.TenCycle
