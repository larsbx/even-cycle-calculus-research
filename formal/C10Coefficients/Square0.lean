import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem square_cell_0_0 : countFrom 8 [0, 0] [2, 2, 2, 2] [D, E, E, E] = 930 := by decide +kernel
theorem square_cell_0_1 : countFrom 8 [0, 1] [3, 1, 2, 2] [D, E, E, E] = 798 := by decide +kernel
theorem square_cell_0_2 : countFrom 8 [0, 2] [3, 2, 1, 2] [D, E, E, E] = 798 := by decide +kernel
theorem square_cell_0_3 : countFrom 8 [0, 3] [3, 2, 2, 1] [D, E, E, E] = 798 := by decide +kernel

theorem square_row_0 : row [4, 2, 2, 2] [D, E, E, E] 0 = [930, 798, 798, 798] := by
  change [countFrom 8 [0, 0] [2, 2, 2, 2] [D, E, E, E],
    countFrom 8 [0, 1] [3, 1, 2, 2] [D, E, E, E],
    countFrom 8 [0, 2] [3, 2, 1, 2] [D, E, E, E],
    countFrom 8 [0, 3] [3, 2, 2, 1] [D, E, E, E]] = [930, 798, 798, 798]
  rw [square_cell_0_0, square_cell_0_1, square_cell_0_2, square_cell_0_3]

#print axioms square_cell_0_0
#print axioms square_cell_0_1
#print axioms square_cell_0_2
#print axioms square_cell_0_3
#print axioms square_row_0
end ECC.TenCycle
