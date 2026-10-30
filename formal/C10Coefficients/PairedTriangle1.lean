import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem paired_triangle_cell_1_0 : countFrom 8 [1, 0] [2, 2, 2, 2] [T, T, E, E] = 1290 := by decide +kernel
theorem paired_triangle_cell_1_1 : countFrom 8 [1, 1] [3, 1, 2, 2] [T, T, E, E] = 620 := by decide +kernel
theorem paired_triangle_cell_1_2 : countFrom 8 [1, 2] [3, 2, 1, 2] [T, T, E, E] = 926 := by decide +kernel
theorem paired_triangle_cell_1_3 : countFrom 8 [1, 3] [3, 2, 2, 1] [T, T, E, E] = 926 := by decide +kernel

theorem paired_triangle_row_1 : row [3, 3, 2, 2] [T, T, E, E] 1 = [1290, 620, 926, 926] := by
  change [countFrom 8 [1, 0] [2, 2, 2, 2] [T, T, E, E],
    countFrom 8 [1, 1] [3, 1, 2, 2] [T, T, E, E],
    countFrom 8 [1, 2] [3, 2, 1, 2] [T, T, E, E],
    countFrom 8 [1, 3] [3, 2, 2, 1] [T, T, E, E]] = [1290, 620, 926, 926]
  rw [paired_triangle_cell_1_0, paired_triangle_cell_1_1, paired_triangle_cell_1_2, paired_triangle_cell_1_3]

#print axioms paired_triangle_cell_1_0
#print axioms paired_triangle_cell_1_1
#print axioms paired_triangle_cell_1_2
#print axioms paired_triangle_cell_1_3
#print axioms paired_triangle_row_1
end ECC.TenCycle
