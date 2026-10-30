import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem wedge_C_cell_3_0 : countFrom 8 [3, 0] [3, 2, 2, 1] [C, E, E, E] = 438 := by decide +kernel
theorem wedge_C_cell_3_1 : countFrom 8 [3, 1] [4, 1, 2, 1] [C, E, E, E] = 230 := by decide +kernel
theorem wedge_C_cell_3_2 : countFrom 8 [3, 2] [4, 2, 1, 1] [C, E, E, E] = 230 := by decide +kernel
theorem wedge_C_cell_3_3 : countFrom 8 [3, 3] [4, 2, 2, 0] [C, E, E, E] = 0 := by decide +kernel

theorem wedge_C_row_3 : row [4, 2, 2, 2] [C, E, E, E] 3 = [438, 230, 230, 0] := by
  change [countFrom 8 [3, 0] [3, 2, 2, 1] [C, E, E, E],
    countFrom 8 [3, 1] [4, 1, 2, 1] [C, E, E, E],
    countFrom 8 [3, 2] [4, 2, 1, 1] [C, E, E, E],
    countFrom 8 [3, 3] [4, 2, 2, 0] [C, E, E, E]] = [438, 230, 230, 0]
  rw [wedge_C_cell_3_0, wedge_C_cell_3_1, wedge_C_cell_3_2, wedge_C_cell_3_3]

#print axioms wedge_C_cell_3_0
#print axioms wedge_C_cell_3_1
#print axioms wedge_C_cell_3_2
#print axioms wedge_C_cell_3_3
#print axioms wedge_C_row_3
end ECC.TenCycle
