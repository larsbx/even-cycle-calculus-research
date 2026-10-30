import Shuffle

/- Exact prefix decomposition for the proposed c10 support-four certificates.
   The original c8 kernel and receipt are unchanged. These reductions use the
   same literal word generator and collision test at length ten. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.TenCycle

def kernelAt (n : Nat) (counts : List Nat) (patterns : List (List Nat)) : Nat :=
  ((words n counts).filter fun w =>
    distinct (vertices patterns w (List.replicate patterns.length 0))).length

def countFrom (n : Nat) (pre counts : List Nat) (patterns : List (List Nat)) : Nat :=
  ((words n counts).filter fun w =>
    distinct (vertices patterns (pre ++ w) (List.replicate patterns.length 0))).length

theorem countFrom_succ (n : Nat) (pre counts : List Nat) (patterns : List (List Nat)) :
    countFrom (n+1) pre counts patterns =
      ((List.range counts.length).map fun a =>
        if counts[a]! == 0 then 0 else
          countFrom n (pre ++ [a]) (counts.modify a (· - 1)) patterns).sum := by
  simp only [countFrom, words, List.filter_flatMap, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro a ha
  split
  · rfl
  · simp only [List.filter_map, List.length_map, List.append_assoc, List.cons_append,
      List.nil_append]
    rfl

def row (counts : List Nat) (patterns : List (List Nat)) (a : Nat) : List Nat :=
  (List.range 4).map fun b => countFrom 8 [a, b]
    ((counts.modify a (· - 1)).modify b (· - 1)) patterns

theorem split_4222 (p : List (List Nat)) :
    kernelAt 10 [4, 2, 2, 2] p =
    ((List.range 4).map fun a => (row [4, 2, 2, 2] p a).sum).sum := by
  change countFrom 10 [] [4, 2, 2, 2] p = _
  rw [countFrom_succ]
  change countFrom 9 [0] [3, 2, 2, 2] p +
    (countFrom 9 [1] [4, 1, 2, 2] p +
    (countFrom 9 [2] [4, 2, 1, 2] p +
    (countFrom 9 [3] [4, 2, 2, 1] p + 0))) = _
  rw [countFrom_succ, countFrom_succ, countFrom_succ, countFrom_succ]
  rfl

theorem split_3322 (p : List (List Nat)) :
    kernelAt 10 [3, 3, 2, 2] p =
    ((List.range 4).map fun a => (row [3, 3, 2, 2] p a).sum).sum := by
  change countFrom 10 [] [3, 3, 2, 2] p = _
  rw [countFrom_succ]
  change countFrom 9 [0] [2, 3, 2, 2] p +
    (countFrom 9 [1] [3, 2, 2, 2] p +
    (countFrom 9 [2] [3, 3, 1, 2] p +
    (countFrom 9 [3] [3, 3, 2, 1] p + 0))) = _
  rw [countFrom_succ, countFrom_succ, countFrom_succ, countFrom_succ]
  rfl


#print axioms countFrom_succ
#print axioms split_4222
#print axioms split_3322

/- Keep rewriting from normalizing a different ground count while matching a
   prefix certificate. The proof kernel still unfolds this definition when
   checking decide +kernel; no opaque axiom is introduced. -/
attribute [irreducible] countFrom
end ECC.TenCycle
