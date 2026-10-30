import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem wedge_B_cell_2_0 : countFrom 8 [2, 0] [3, 2, 1, 2] [B, E, E, E] = 252 := by decide +kernel
theorem wedge_B_cell_2_1 : countFrom 8 [2, 1] [4, 1, 1, 2] [B, E, E, E] = 82 := by decide +kernel
theorem wedge_B_cell_2_2 : countFrom 8 [2, 2] [4, 2, 0, 2] [B, E, E, E] = 0 := by decide +kernel
theorem wedge_B_cell_2_3 : countFrom 8 [2, 3] [4, 2, 1, 1] [B, E, E, E] = 82 := by decide +kernel

theorem wedge_B_row_2 : row [4, 2, 2, 2] [B, E, E, E] 2 = [252, 82, 0, 82] := by
  change [countFrom 8 [2, 0] [3, 2, 1, 2] [B, E, E, E],
    countFrom 8 [2, 1] [4, 1, 1, 2] [B, E, E, E],
    countFrom 8 [2, 2] [4, 2, 0, 2] [B, E, E, E],
    countFrom 8 [2, 3] [4, 2, 1, 1] [B, E, E, E]] = [252, 82, 0, 82]
  rw [wedge_B_cell_2_0, wedge_B_cell_2_1, wedge_B_cell_2_2, wedge_B_cell_2_3]

#print axioms wedge_B_cell_2_0
#print axioms wedge_B_cell_2_1
#print axioms wedge_B_cell_2_2
#print axioms wedge_B_cell_2_3
#print axioms wedge_B_row_2
end ECC.TenCycle
