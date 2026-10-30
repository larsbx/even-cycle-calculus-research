import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem wedge_B_cell_1_0 : countFrom 8 [1, 0] [3, 1, 2, 2] [B, E, E, E] = 252 := by decide +kernel
theorem wedge_B_cell_1_1 : countFrom 8 [1, 1] [4, 0, 2, 2] [B, E, E, E] = 0 := by decide +kernel
theorem wedge_B_cell_1_2 : countFrom 8 [1, 2] [4, 1, 1, 2] [B, E, E, E] = 82 := by decide +kernel
theorem wedge_B_cell_1_3 : countFrom 8 [1, 3] [4, 1, 2, 1] [B, E, E, E] = 82 := by decide +kernel

theorem wedge_B_row_1 : row [4, 2, 2, 2] [B, E, E, E] 1 = [252, 0, 82, 82] := by
  change [countFrom 8 [1, 0] [3, 1, 2, 2] [B, E, E, E],
    countFrom 8 [1, 1] [4, 0, 2, 2] [B, E, E, E],
    countFrom 8 [1, 2] [4, 1, 1, 2] [B, E, E, E],
    countFrom 8 [1, 3] [4, 1, 2, 1] [B, E, E, E]] = [252, 0, 82, 82]
  rw [wedge_B_cell_1_0, wedge_B_cell_1_1, wedge_B_cell_1_2, wedge_B_cell_1_3]

#print axioms wedge_B_cell_1_0
#print axioms wedge_B_cell_1_1
#print axioms wedge_B_cell_1_2
#print axioms wedge_B_cell_1_3
#print axioms wedge_B_row_1
end ECC.TenCycle
