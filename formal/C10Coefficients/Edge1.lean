import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem edge_cell_1_0 : countFrom 8 [1, 0] [3, 1, 2, 2] [A, E, E, E] = 88 := by decide +kernel
theorem edge_cell_1_1 : countFrom 8 [1, 1] [4, 0, 2, 2] [A, E, E, E] = 0 := by decide +kernel
theorem edge_cell_1_2 : countFrom 8 [1, 2] [4, 1, 1, 2] [A, E, E, E] = 22 := by decide +kernel
theorem edge_cell_1_3 : countFrom 8 [1, 3] [4, 1, 2, 1] [A, E, E, E] = 22 := by decide +kernel

theorem edge_row_1 : row [4, 2, 2, 2] [A, E, E, E] 1 = [88, 0, 22, 22] := by
  change [countFrom 8 [1, 0] [3, 1, 2, 2] [A, E, E, E],
    countFrom 8 [1, 1] [4, 0, 2, 2] [A, E, E, E],
    countFrom 8 [1, 2] [4, 1, 1, 2] [A, E, E, E],
    countFrom 8 [1, 3] [4, 1, 2, 1] [A, E, E, E]] = [88, 0, 22, 22]
  rw [edge_cell_1_0, edge_cell_1_1, edge_cell_1_2, edge_cell_1_3]

#print axioms edge_cell_1_0
#print axioms edge_cell_1_1
#print axioms edge_cell_1_2
#print axioms edge_cell_1_3
#print axioms edge_row_1
end ECC.TenCycle
