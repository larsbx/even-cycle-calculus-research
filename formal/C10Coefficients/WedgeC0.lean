import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem wedge_C_cell_0_0 : countFrom 8 [0, 0] [2, 2, 2, 2] [C, E, E, E] = 558 := by decide +kernel
theorem wedge_C_cell_0_1 : countFrom 8 [0, 1] [3, 1, 2, 2] [C, E, E, E] = 252 := by decide +kernel
theorem wedge_C_cell_0_2 : countFrom 8 [0, 2] [3, 2, 1, 2] [C, E, E, E] = 252 := by decide +kernel
theorem wedge_C_cell_0_3 : countFrom 8 [0, 3] [3, 2, 2, 1] [C, E, E, E] = 252 := by decide +kernel

theorem wedge_C_row_0 : row [4, 2, 2, 2] [C, E, E, E] 0 = [558, 252, 252, 252] := by
  change [countFrom 8 [0, 0] [2, 2, 2, 2] [C, E, E, E],
    countFrom 8 [0, 1] [3, 1, 2, 2] [C, E, E, E],
    countFrom 8 [0, 2] [3, 2, 1, 2] [C, E, E, E],
    countFrom 8 [0, 3] [3, 2, 2, 1] [C, E, E, E]] = [558, 252, 252, 252]
  rw [wedge_C_cell_0_0, wedge_C_cell_0_1, wedge_C_cell_0_2, wedge_C_cell_0_3]

#print axioms wedge_C_cell_0_0
#print axioms wedge_C_cell_0_1
#print axioms wedge_C_cell_0_2
#print axioms wedge_C_cell_0_3
#print axioms wedge_C_row_0
end ECC.TenCycle
