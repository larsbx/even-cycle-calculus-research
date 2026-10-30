import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem square_cell_3_0 : countFrom 8 [3, 0] [3, 2, 2, 1] [D, E, E, E] = 798 := by decide +kernel
theorem square_cell_3_1 : countFrom 8 [3, 1] [4, 1, 2, 1] [D, E, E, E] = 432 := by decide +kernel
theorem square_cell_3_2 : countFrom 8 [3, 2] [4, 2, 1, 1] [D, E, E, E] = 432 := by decide +kernel
theorem square_cell_3_3 : countFrom 8 [3, 3] [4, 2, 2, 0] [D, E, E, E] = 0 := by decide +kernel

theorem square_row_3 : row [4, 2, 2, 2] [D, E, E, E] 3 = [798, 432, 432, 0] := by
  change [countFrom 8 [3, 0] [3, 2, 2, 1] [D, E, E, E],
    countFrom 8 [3, 1] [4, 1, 2, 1] [D, E, E, E],
    countFrom 8 [3, 2] [4, 2, 1, 1] [D, E, E, E],
    countFrom 8 [3, 3] [4, 2, 2, 0] [D, E, E, E]] = [798, 432, 432, 0]
  rw [square_cell_3_0, square_cell_3_1, square_cell_3_2, square_cell_3_3]

#print axioms square_cell_3_0
#print axioms square_cell_3_1
#print axioms square_cell_3_2
#print axioms square_cell_3_3
#print axioms square_row_3
end ECC.TenCycle
