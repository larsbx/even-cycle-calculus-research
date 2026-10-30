import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem wedge_B_cell_3_0 : countFrom 8 [3, 0] [3, 2, 2, 1] [B, E, E, E] = 252 := by decide +kernel
theorem wedge_B_cell_3_1 : countFrom 8 [3, 1] [4, 1, 2, 1] [B, E, E, E] = 82 := by decide +kernel
theorem wedge_B_cell_3_2 : countFrom 8 [3, 2] [4, 2, 1, 1] [B, E, E, E] = 82 := by decide +kernel
theorem wedge_B_cell_3_3 : countFrom 8 [3, 3] [4, 2, 2, 0] [B, E, E, E] = 0 := by decide +kernel

theorem wedge_B_row_3 : row [4, 2, 2, 2] [B, E, E, E] 3 = [252, 82, 82, 0] := by
  change [countFrom 8 [3, 0] [3, 2, 2, 1] [B, E, E, E],
    countFrom 8 [3, 1] [4, 1, 2, 1] [B, E, E, E],
    countFrom 8 [3, 2] [4, 2, 1, 1] [B, E, E, E],
    countFrom 8 [3, 3] [4, 2, 2, 0] [B, E, E, E]] = [252, 82, 82, 0]
  rw [wedge_B_cell_3_0, wedge_B_cell_3_1, wedge_B_cell_3_2, wedge_B_cell_3_3]

#print axioms wedge_B_cell_3_0
#print axioms wedge_B_cell_3_1
#print axioms wedge_B_cell_3_2
#print axioms wedge_B_cell_3_3
#print axioms wedge_B_row_3
end ECC.TenCycle
