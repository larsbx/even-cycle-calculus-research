import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem square_cell_2_0 : countFrom 8 [2, 0] [3, 2, 1, 2] [D, E, E, E] = 798 := by decide +kernel
theorem square_cell_2_1 : countFrom 8 [2, 1] [4, 1, 1, 2] [D, E, E, E] = 432 := by decide +kernel
theorem square_cell_2_2 : countFrom 8 [2, 2] [4, 2, 0, 2] [D, E, E, E] = 0 := by decide +kernel
theorem square_cell_2_3 : countFrom 8 [2, 3] [4, 2, 1, 1] [D, E, E, E] = 432 := by decide +kernel

theorem square_row_2 : row [4, 2, 2, 2] [D, E, E, E] 2 = [798, 432, 0, 432] := by
  change [countFrom 8 [2, 0] [3, 2, 1, 2] [D, E, E, E],
    countFrom 8 [2, 1] [4, 1, 1, 2] [D, E, E, E],
    countFrom 8 [2, 2] [4, 2, 0, 2] [D, E, E, E],
    countFrom 8 [2, 3] [4, 2, 1, 1] [D, E, E, E]] = [798, 432, 0, 432]
  rw [square_cell_2_0, square_cell_2_1, square_cell_2_2, square_cell_2_3]

#print axioms square_cell_2_0
#print axioms square_cell_2_1
#print axioms square_cell_2_2
#print axioms square_cell_2_3
#print axioms square_row_2
end ECC.TenCycle
