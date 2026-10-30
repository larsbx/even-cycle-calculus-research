import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem paired_triangle_cell_0_0 : countFrom 8 [0, 0] [1, 3, 2, 2] [T, T, E, E] = 620 := by decide +kernel
theorem paired_triangle_cell_0_1 : countFrom 8 [0, 1] [2, 2, 2, 2] [T, T, E, E] = 1290 := by decide +kernel
theorem paired_triangle_cell_0_2 : countFrom 8 [0, 2] [2, 3, 1, 2] [T, T, E, E] = 926 := by decide +kernel
theorem paired_triangle_cell_0_3 : countFrom 8 [0, 3] [2, 3, 2, 1] [T, T, E, E] = 926 := by decide +kernel

theorem paired_triangle_row_0 : row [3, 3, 2, 2] [T, T, E, E] 0 = [620, 1290, 926, 926] := by
  change [countFrom 8 [0, 0] [1, 3, 2, 2] [T, T, E, E],
    countFrom 8 [0, 1] [2, 2, 2, 2] [T, T, E, E],
    countFrom 8 [0, 2] [2, 3, 1, 2] [T, T, E, E],
    countFrom 8 [0, 3] [2, 3, 2, 1] [T, T, E, E]] = [620, 1290, 926, 926]
  rw [paired_triangle_cell_0_0, paired_triangle_cell_0_1, paired_triangle_cell_0_2, paired_triangle_cell_0_3]

#print axioms paired_triangle_cell_0_0
#print axioms paired_triangle_cell_0_1
#print axioms paired_triangle_cell_0_2
#print axioms paired_triangle_cell_0_3
#print axioms paired_triangle_row_0
end ECC.TenCycle
