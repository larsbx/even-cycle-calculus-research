import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem square_cell_1_0 : countFrom 8 [1, 0] [3, 1, 2, 2] [D, E, E, E] = 798 := by decide +kernel
theorem square_cell_1_1 : countFrom 8 [1, 1] [4, 0, 2, 2] [D, E, E, E] = 0 := by decide +kernel
theorem square_cell_1_2 : countFrom 8 [1, 2] [4, 1, 1, 2] [D, E, E, E] = 432 := by decide +kernel
theorem square_cell_1_3 : countFrom 8 [1, 3] [4, 1, 2, 1] [D, E, E, E] = 432 := by decide +kernel

theorem square_row_1 : row [4, 2, 2, 2] [D, E, E, E] 1 = [798, 0, 432, 432] := by
  change [countFrom 8 [1, 0] [3, 1, 2, 2] [D, E, E, E],
    countFrom 8 [1, 1] [4, 0, 2, 2] [D, E, E, E],
    countFrom 8 [1, 2] [4, 1, 1, 2] [D, E, E, E],
    countFrom 8 [1, 3] [4, 1, 2, 1] [D, E, E, E]] = [798, 0, 432, 432]
  rw [square_cell_1_0, square_cell_1_1, square_cell_1_2, square_cell_1_3]

#print axioms square_cell_1_0
#print axioms square_cell_1_1
#print axioms square_cell_1_2
#print axioms square_cell_1_3
#print axioms square_row_1
end ECC.TenCycle
