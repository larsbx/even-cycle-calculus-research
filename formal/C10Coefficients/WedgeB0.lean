import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem wedge_B_cell_0_0 : countFrom 8 [0, 0] [2, 2, 2, 2] [B, E, E, E] = 0 := by decide +kernel
theorem wedge_B_cell_0_1 : countFrom 8 [0, 1] [3, 1, 2, 2] [B, E, E, E] = 438 := by decide +kernel
theorem wedge_B_cell_0_2 : countFrom 8 [0, 2] [3, 2, 1, 2] [B, E, E, E] = 438 := by decide +kernel
theorem wedge_B_cell_0_3 : countFrom 8 [0, 3] [3, 2, 2, 1] [B, E, E, E] = 438 := by decide +kernel

theorem wedge_B_row_0 : row [4, 2, 2, 2] [B, E, E, E] 0 = [0, 438, 438, 438] := by
  change [countFrom 8 [0, 0] [2, 2, 2, 2] [B, E, E, E],
    countFrom 8 [0, 1] [3, 1, 2, 2] [B, E, E, E],
    countFrom 8 [0, 2] [3, 2, 1, 2] [B, E, E, E],
    countFrom 8 [0, 3] [3, 2, 2, 1] [B, E, E, E]] = [0, 438, 438, 438]
  rw [wedge_B_cell_0_0, wedge_B_cell_0_1, wedge_B_cell_0_2, wedge_B_cell_0_3]

#print axioms wedge_B_cell_0_0
#print axioms wedge_B_cell_0_1
#print axioms wedge_B_cell_0_2
#print axioms wedge_B_cell_0_3
#print axioms wedge_B_row_0
end ECC.TenCycle
