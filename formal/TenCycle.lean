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

attribute [local irreducible] row kernelAt

def table (counts : List Nat) (patterns : List (List Nat)) : List (List Nat) :=
  (List.range 4).map fun a => row counts patterns a

theorem map_sum_table (counts : List Nat) (patterns : List (List Nat)) :
    ((List.range 4).map fun a => (row counts patterns a).sum).sum =
      ((table counts patterns).map List.sum).sum := by
  simp only [table, List.map_map, Function.comp_def]

theorem edge_table : table [4, 2, 2, 2] [A, E, E, E] = [[0, 88, 88, 88], [88, 0, 22, 22], [88, 22, 0, 22], [88, 22, 22, 0]] := by
  change [row [4, 2, 2, 2] [A, E, E, E] 0, row [4, 2, 2, 2] [A, E, E, E] 1,
    row [4, 2, 2, 2] [A, E, E, E] 2, row [4, 2, 2, 2] [A, E, E, E] 3] = [[0, 88, 88, 88], [88, 0, 22, 22], [88, 22, 0, 22], [88, 22, 22, 0]]
  rw [edge_row_0, edge_row_1, edge_row_2, edge_row_3]

theorem edge_coefficient : kernelAt 10 [4, 2, 2, 2] [A, E, E, E] = 660 :=
  (split_4222 [A, E, E, E]).trans ((map_sum_table [4, 2, 2, 2] [A, E, E, E]).trans
    ((congrArg (fun ts : List (List Nat) => (ts.map List.sum).sum) edge_table).trans (by decide)))

theorem wedge_B_table : table [4, 2, 2, 2] [B, E, E, E] = [[0, 438, 438, 438], [252, 0, 82, 82], [252, 82, 0, 82], [252, 82, 82, 0]] := by
  change [row [4, 2, 2, 2] [B, E, E, E] 0, row [4, 2, 2, 2] [B, E, E, E] 1,
    row [4, 2, 2, 2] [B, E, E, E] 2, row [4, 2, 2, 2] [B, E, E, E] 3] = [[0, 438, 438, 438], [252, 0, 82, 82], [252, 82, 0, 82], [252, 82, 82, 0]]
  rw [wedge_B_row_0, wedge_B_row_1, wedge_B_row_2, wedge_B_row_3]

theorem wedge_B_coefficient : kernelAt 10 [4, 2, 2, 2] [B, E, E, E] = 2562 :=
  (split_4222 [B, E, E, E]).trans ((map_sum_table [4, 2, 2, 2] [B, E, E, E]).trans
    ((congrArg (fun ts : List (List Nat) => (ts.map List.sum).sum) wedge_B_table).trans (by decide)))

theorem wedge_C_table : table [4, 2, 2, 2] [C, E, E, E] = [[558, 252, 252, 252], [438, 0, 230, 230], [438, 230, 0, 230], [438, 230, 230, 0]] := by
  change [row [4, 2, 2, 2] [C, E, E, E] 0, row [4, 2, 2, 2] [C, E, E, E] 1,
    row [4, 2, 2, 2] [C, E, E, E] 2, row [4, 2, 2, 2] [C, E, E, E] 3] = [[558, 252, 252, 252], [438, 0, 230, 230], [438, 230, 0, 230], [438, 230, 230, 0]]
  rw [wedge_C_row_0, wedge_C_row_1, wedge_C_row_2, wedge_C_row_3]

theorem wedge_C_coefficient : kernelAt 10 [4, 2, 2, 2] [C, E, E, E] = 4008 :=
  (split_4222 [C, E, E, E]).trans ((map_sum_table [4, 2, 2, 2] [C, E, E, E]).trans
    ((congrArg (fun ts : List (List Nat) => (ts.map List.sum).sum) wedge_C_table).trans (by decide)))

theorem square_table : table [4, 2, 2, 2] [D, E, E, E] = [[930, 798, 798, 798], [798, 0, 432, 432], [798, 432, 0, 432], [798, 432, 432, 0]] := by
  change [row [4, 2, 2, 2] [D, E, E, E] 0, row [4, 2, 2, 2] [D, E, E, E] 1,
    row [4, 2, 2, 2] [D, E, E, E] 2, row [4, 2, 2, 2] [D, E, E, E] 3] = [[930, 798, 798, 798], [798, 0, 432, 432], [798, 432, 0, 432], [798, 432, 432, 0]]
  rw [square_row_0, square_row_1, square_row_2, square_row_3]

theorem square_coefficient : kernelAt 10 [4, 2, 2, 2] [D, E, E, E] = 8310 :=
  (split_4222 [D, E, E, E]).trans ((map_sum_table [4, 2, 2, 2] [D, E, E, E]).trans
    ((congrArg (fun ts : List (List Nat) => (ts.map List.sum).sum) square_table).trans (by decide)))

theorem paired_triangle_table : table [3, 3, 2, 2] [T, T, E, E] = [[620, 1290, 926, 926], [1290, 620, 926, 926], [926, 926, 0, 656], [926, 926, 656, 0]] := by
  change [row [3, 3, 2, 2] [T, T, E, E] 0, row [3, 3, 2, 2] [T, T, E, E] 1,
    row [3, 3, 2, 2] [T, T, E, E] 2, row [3, 3, 2, 2] [T, T, E, E] 3] = [[620, 1290, 926, 926], [1290, 620, 926, 926], [926, 926, 0, 656], [926, 926, 656, 0]]
  rw [paired_triangle_row_0, paired_triangle_row_1, paired_triangle_row_2, paired_triangle_row_3]

theorem paired_triangle_coefficient : kernelAt 10 [3, 3, 2, 2] [T, T, E, E] = 12540 :=
  (split_3322 [T, T, E, E]).trans ((map_sum_table [3, 3, 2, 2] [T, T, E, E]).trans
    ((congrArg (fun ts : List (List Nat) => (ts.map List.sum).sum) paired_triangle_table).trans (by decide)))

theorem motif_coefficient_arithmetic :
    660 * 2 * 8 = 20 * 528 ∧
    (2562 + 4008) * 2 * 8 = 20 * 5256 ∧
    8310 * 8 * 8 = 20 * 26592 ∧
    12540 * 36 * 4 = 20 * 90288 := by decide

theorem rooted_wedge_categories_not_divisible :
    (2562 * 2 * 8) % 20 = 12 ∧ (4008 * 2 * 8) % 20 = 8 ∧
    ((2562 + 4008) * 2 * 8) % 20 = 0 := by decide

#print axioms map_sum_table
#print axioms edge_table
#print axioms wedge_B_table
#print axioms wedge_C_table
#print axioms square_table
#print axioms paired_triangle_table
#print axioms edge_coefficient
#print axioms wedge_B_coefficient
#print axioms wedge_C_coefficient
#print axioms square_coefficient
#print axioms paired_triangle_coefficient
#print axioms motif_coefficient_arithmetic
#print axioms rooted_wedge_categories_not_divisible
end ECC.TenCycle
