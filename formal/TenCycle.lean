import C10Coefficients.Edge0
import C10Coefficients.Edge1
import C10Coefficients.Edge2
import C10Coefficients.Edge3
import C10Coefficients.WedgeB0
import C10Coefficients.WedgeB1
import C10Coefficients.WedgeB2
import C10Coefficients.WedgeB3
import C10Coefficients.WedgeC0
import C10Coefficients.WedgeC1
import C10Coefficients.WedgeC2
import C10Coefficients.WedgeC3
import C10Coefficients.Square0
import C10Coefficients.Square1
import C10Coefficients.Square2
import C10Coefficients.Square3
import C10Coefficients.PairedTriangle0
import C10Coefficients.PairedTriangle1
import C10Coefficients.PairedTriangle2
import C10Coefficients.PairedTriangle3

namespace ECC.TenCycle

theorem edge_coefficient : kernelAt 10 [4, 2, 2, 2] [A, E, E, E] = 660 := by
  rw [split_4222]
  change (row [4, 2, 2, 2] [A, E, E, E] 0).sum +
    ((row [4, 2, 2, 2] [A, E, E, E] 1).sum +
    ((row [4, 2, 2, 2] [A, E, E, E] 2).sum + ((row [4, 2, 2, 2] [A, E, E, E] 3).sum + 0))) = 660
  rw [edge_row_0, edge_row_1, edge_row_2, edge_row_3]
  rfl

theorem wedge_B_coefficient : kernelAt 10 [4, 2, 2, 2] [B, E, E, E] = 2562 := by
  rw [split_4222]
  change (row [4, 2, 2, 2] [B, E, E, E] 0).sum +
    ((row [4, 2, 2, 2] [B, E, E, E] 1).sum +
    ((row [4, 2, 2, 2] [B, E, E, E] 2).sum + ((row [4, 2, 2, 2] [B, E, E, E] 3).sum + 0))) = 2562
  rw [wedge_B_row_0, wedge_B_row_1, wedge_B_row_2, wedge_B_row_3]
  rfl

theorem wedge_C_coefficient : kernelAt 10 [4, 2, 2, 2] [C, E, E, E] = 4008 := by
  rw [split_4222]
  change (row [4, 2, 2, 2] [C, E, E, E] 0).sum +
    ((row [4, 2, 2, 2] [C, E, E, E] 1).sum +
    ((row [4, 2, 2, 2] [C, E, E, E] 2).sum + ((row [4, 2, 2, 2] [C, E, E, E] 3).sum + 0))) = 4008
  rw [wedge_C_row_0, wedge_C_row_1, wedge_C_row_2, wedge_C_row_3]
  rfl

theorem square_coefficient : kernelAt 10 [4, 2, 2, 2] [D, E, E, E] = 8310 := by
  rw [split_4222]
  change (row [4, 2, 2, 2] [D, E, E, E] 0).sum +
    ((row [4, 2, 2, 2] [D, E, E, E] 1).sum +
    ((row [4, 2, 2, 2] [D, E, E, E] 2).sum + ((row [4, 2, 2, 2] [D, E, E, E] 3).sum + 0))) = 8310
  rw [square_row_0, square_row_1, square_row_2, square_row_3]
  rfl

theorem paired_triangle_coefficient : kernelAt 10 [3, 3, 2, 2] [T, T, E, E] = 12540 := by
  rw [split_3322]
  change (row [3, 3, 2, 2] [T, T, E, E] 0).sum +
    ((row [3, 3, 2, 2] [T, T, E, E] 1).sum +
    ((row [3, 3, 2, 2] [T, T, E, E] 2).sum + ((row [3, 3, 2, 2] [T, T, E, E] 3).sum + 0))) = 12540
  rw [paired_triangle_row_0, paired_triangle_row_1, paired_triangle_row_2, paired_triangle_row_3]
  rfl

theorem motif_coefficient_arithmetic :
    660 * 2 * 8 = 20 * 528 ∧
    (2562 + 4008) * 2 * 8 = 20 * 5256 ∧
    8310 * 8 * 8 = 20 * 26592 ∧
    12540 * 36 * 4 = 20 * 90288 := by decide

theorem rooted_wedge_categories_not_divisible :
    (2562 * 2 * 8) % 20 = 12 ∧ (4008 * 2 * 8) % 20 = 8 ∧
    ((2562 + 4008) * 2 * 8) % 20 = 0 := by decide

#print axioms edge_coefficient
#print axioms wedge_B_coefficient
#print axioms wedge_C_coefficient
#print axioms square_coefficient
#print axioms paired_triangle_coefficient
#print axioms motif_coefficient_arithmetic
#print axioms rooted_wedge_categories_not_divisible
end ECC.TenCycle
