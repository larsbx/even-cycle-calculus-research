import Std

/- Finite coefficient certificates only. The general graph/projection bijection
   is proved in prose, not formalized here. No native_decide or added axioms. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC

def words : Nat → List Nat → List (List Nat)
  | 0, counts => if counts.all (· == 0) then [[]] else []
  | n+1, counts => (List.range counts.length).flatMap fun a =>
      if counts[a]! == 0 then [] else
        (words n (counts.modify a (· - 1))).map (a :: ·)

def vertices (patterns : List (List Nat)) : List Nat → List Nat → List (List Nat)
  | [], _ => []
  | a :: rest, at =>
      let v := (List.range patterns.length).map fun b =>
        let p := patterns[b]!
        p[at[b]! % p.length]!
      v :: vertices patterns rest (at.modify a (· + 1))

def distinct : List (List Nat) → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && distinct xs

def kernel (counts : List Nat) (patterns : List (List Nat)) : Nat :=
  ((words 8 counts).filter fun w =>
    distinct (vertices patterns w (List.replicate patterns.length 0))).length

def E : List Nat := [0, 1]
def T : List Nat := [0, 1, 2]
def A : List Nat := [0, 1, 0, 1]
def B : List Nat := [0, 1, 0, 2]
def C : List Nat := [0, 1, 2, 1]
def D : List Nat := [0, 1, 2, 3]

theorem paired_triangle_coefficient : kernel [2, 3, 3] [E, T, T] = 312 := by decide
theorem four_step_coefficients :
    [kernel [4, 2, 2] [A, E, E], kernel [4, 2, 2] [B, E, E],
     kernel [4, 2, 2] [C, E, E], kernel [4, 2, 2] [D, E, E]] =
    [4, 44, 76, 204] := by decide
theorem two_four_step_coefficients :
    ([A, B, C, D].map fun p =>
      [A, B, C, D].map fun q => kernel [4, 4] [p, q]) =
    [[0, 0, 0, 2], [0, 2, 5, 15], [0, 5, 8, 25], [2, 15, 25, 62]] := by decide

#print axioms paired_triangle_coefficient
#print axioms four_step_coefficients
#print axioms two_four_step_coefficients

end ECC
