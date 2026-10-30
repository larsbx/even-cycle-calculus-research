import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem edge_cell_0_0 : countFrom 8 [0, 0] [2, 2, 2, 2] [A, E, E, E] = 0 := by decide +kernel
theorem edge_cell_0_1 : countFrom 8 [0, 1] [3, 1, 2, 2] [A, E, E, E] = 88 := by decide +kernel
theorem edge_cell_0_2 : countFrom 8 [0, 2] [3, 2, 1, 2] [A, E, E, E] = 88 := by decide +kernel
theorem edge_cell_0_3 : countFrom 8 [0, 3] [3, 2, 2, 1] [A, E, E, E] = 88 := by decide +kernel

theorem edge_row_0 : row [4, 2, 2, 2] [A, E, E, E] 0 = [0, 88, 88, 88] := by
  change [countFrom 8 [0, 0] [2, 2, 2, 2] [A, E, E, E],
    countFrom 8 [0, 1] [3, 1, 2, 2] [A, E, E, E],
    countFrom 8 [0, 2] [3, 2, 1, 2] [A, E, E, E],
    countFrom 8 [0, 3] [3, 2, 2, 1] [A, E, E, E]] = [0, 88, 88, 88]
  rw [edge_cell_0_0, edge_cell_0_1, edge_cell_0_2, edge_cell_0_3]

#print axioms edge_cell_0_0
#print axioms edge_cell_0_1
#print axioms edge_cell_0_2
#print axioms edge_cell_0_3
#print axioms edge_row_0
end ECC.TenCycle
