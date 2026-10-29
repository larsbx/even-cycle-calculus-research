import WordGenerator

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ECC.WordControls
open ECC.WordGenerator ECC.EventShuffle

def prismWord : List Nat := [1, 0, 1, 0, 1, 0, 1, 0]
def pairedWord : List Nat := [0, 1, 0, 1, 2, 1, 2, 2]

theorem profile_word_counts :
    [ECC.words 8 [6, 2], ECC.words 8 [3, 5], ECC.words 8 [4, 4],
      ECC.words 8 [4, 2, 2], ECC.words 8 [2, 3, 3], ECC.words 8 [2, 2, 2, 2]].map List.length =
    [28, 56, 70, 420, 560, 2520] := by decide

theorem zero_inventory_controls :
    ECC.words 0 [0, 0] = [[]] ∧ ECC.words 1 [0, 0] = [] ∧ ECC.words 0 [1] = [] := by decide

theorem wrong_multiplicity_rejected :
    [0, 0, 0, 0, 0, 0, 0, 0] ∉ ECC.words 8 [4, 4] := by decide

theorem illegal_axis_rejected :
    [0, 0, 0, 0, 1, 1, 1, 2] ∉ ECC.words 8 [4, 4] := by decide

theorem witnesses_occur_once :
    (ECC.words 8 [4, 4]).count prismWord = 1 ∧
    (ECC.words 8 [2, 3, 3]).count pairedWord = 1 := by
  constructor
  · exact (words_nodup 8 [4, 4]).count_of_mem (by decide)
  · exact (words_nodup 8 [2, 3, 3]).count_of_mem (by decide)

def typedPrism : List (Fin 2) :=
  lift prismWord (((mem_words_iff 8 [4, 4] prismWord).mp (by decide)).2.1)

theorem typed_lift_control : typedPrism.map Fin.val = prismWord ∧
    [steps typedPrism 0, steps typedPrism 1] = [4, 4] := by decide

theorem inconsistent_budget_rejected : ECC.words 7 [4, 4] = [] := by decide

#print axioms profile_word_counts
#print axioms zero_inventory_controls
#print axioms wrong_multiplicity_rejected
#print axioms illegal_axis_rejected
#print axioms witnesses_occur_once
#print axioms typed_lift_control
#print axioms inconsistent_budget_rejected

end ECC.WordControls
