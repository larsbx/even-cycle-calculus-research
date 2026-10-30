import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem paired_triangle_cell_2_0 : countFrom 8 [2, 0] [2, 3, 1, 2] [T, T, E, E] = 926 := by decide +kernel
theorem paired_triangle_cell_2_1 : countFrom 8 [2, 1] [3, 2, 1, 2] [T, T, E, E] = 926 := by decide +kernel
theorem paired_triangle_cell_2_2 : countFrom 8 [2, 2] [3, 3, 0, 2] [T, T, E, E] = 0 := by decide +kernel
theorem paired_triangle_cell_2_3 : countFrom 8 [2, 3] [3, 3, 1, 1] [T, T, E, E] = 656 := by decide +kernel

theorem paired_triangle_row_2 : row [3, 3, 2, 2] [T, T, E, E] 2 = [926, 926, 0, 656] := by
  change [countFrom 8 [2, 0] [2, 3, 1, 2] [T, T, E, E],
    countFrom 8 [2, 1] [3, 2, 1, 2] [T, T, E, E],
    countFrom 8 [2, 2] [3, 3, 0, 2] [T, T, E, E],
    countFrom 8 [2, 3] [3, 3, 1, 1] [T, T, E, E]] = [926, 926, 0, 656]
  rw [paired_triangle_cell_2_0, paired_triangle_cell_2_1, paired_triangle_cell_2_2, paired_triangle_cell_2_3]

#print axioms paired_triangle_cell_2_0
#print axioms paired_triangle_cell_2_1
#print axioms paired_triangle_cell_2_2
#print axioms paired_triangle_cell_2_3
#print axioms paired_triangle_row_2
end ECC.TenCycle
