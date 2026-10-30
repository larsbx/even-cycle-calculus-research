import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem edge_cell_2_0 : countFrom 8 [2, 0] [3, 2, 1, 2] [A, E, E, E] = 88 := by decide +kernel
theorem edge_cell_2_1 : countFrom 8 [2, 1] [4, 1, 1, 2] [A, E, E, E] = 22 := by decide +kernel
theorem edge_cell_2_2 : countFrom 8 [2, 2] [4, 2, 0, 2] [A, E, E, E] = 0 := by decide +kernel
theorem edge_cell_2_3 : countFrom 8 [2, 3] [4, 2, 1, 1] [A, E, E, E] = 22 := by decide +kernel

theorem edge_row_2 : row [4, 2, 2, 2] [A, E, E, E] 2 = [88, 22, 0, 22] := by
  change [countFrom 8 [2, 0] [3, 2, 1, 2] [A, E, E, E],
    countFrom 8 [2, 1] [4, 1, 1, 2] [A, E, E, E],
    countFrom 8 [2, 2] [4, 2, 0, 2] [A, E, E, E],
    countFrom 8 [2, 3] [4, 2, 1, 1] [A, E, E, E]] = [88, 22, 0, 22]
  rw [edge_cell_2_0, edge_cell_2_1, edge_cell_2_2, edge_cell_2_3]

#print axioms edge_cell_2_0
#print axioms edge_cell_2_1
#print axioms edge_cell_2_2
#print axioms edge_cell_2_3
#print axioms edge_row_2
end ECC.TenCycle
