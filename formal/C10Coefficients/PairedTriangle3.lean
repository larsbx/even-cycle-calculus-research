import TenCycleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

theorem paired_triangle_cell_3_0 : countFrom 8 [3, 0] [2, 3, 2, 1] [T, T, E, E] = 926 := by decide +kernel
theorem paired_triangle_cell_3_1 : countFrom 8 [3, 1] [3, 2, 2, 1] [T, T, E, E] = 926 := by decide +kernel
theorem paired_triangle_cell_3_2 : countFrom 8 [3, 2] [3, 3, 1, 1] [T, T, E, E] = 656 := by decide +kernel
theorem paired_triangle_cell_3_3 : countFrom 8 [3, 3] [3, 3, 2, 0] [T, T, E, E] = 0 := by decide +kernel

theorem paired_triangle_row_3 : row [3, 3, 2, 2] [T, T, E, E] 3 = [926, 926, 656, 0] := by
  change [countFrom 8 [3, 0] [2, 3, 2, 1] [T, T, E, E],
    countFrom 8 [3, 1] [3, 2, 2, 1] [T, T, E, E],
    countFrom 8 [3, 2] [3, 3, 1, 1] [T, T, E, E],
    countFrom 8 [3, 3] [3, 3, 2, 0] [T, T, E, E]] = [926, 926, 656, 0]
  rw [paired_triangle_cell_3_0, paired_triangle_cell_3_1, paired_triangle_cell_3_2, paired_triangle_cell_3_3]

#print axioms paired_triangle_cell_3_0
#print axioms paired_triangle_cell_3_1
#print axioms paired_triangle_cell_3_2
#print axioms paired_triangle_cell_3_3
#print axioms paired_triangle_row_3
end ECC.TenCycle
