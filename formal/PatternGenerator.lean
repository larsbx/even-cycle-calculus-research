import WordGenerator

/- Pointwise pre conditions for the literal restricted-growth generator. -/
namespace ECC.PatternGenerator
open ECC.WordGenerator

def Extension (pre tail : List Nat) : Prop :=
  ∀ i (hi : i < tail.length),
    tail[i] < (pre ++ tail.take i).foldl Nat.max 0 + 2 ∧
      tail[i] ≠ (pre ++ tail.take i).getLast!

theorem extension_nil (pre : List Nat) : Extension pre [] := by
  intro i hi
  exact False.elim (Nat.not_lt_zero _ hi)

theorem extension_cons_iff (pre : List Nat) (a : Nat) (tail : List Nat) :
    Extension pre (a :: tail) ↔
      (a < pre.foldl Nat.max 0 + 2 ∧ a ≠ pre.getLast!) ∧
        Extension (pre ++ [a]) tail := by
  constructor
  · intro h
    constructor
    · have h0 := h 0 (Nat.zero_lt_succ tail.length)
      change a < (pre ++ []).foldl Nat.max 0 + 2 ∧ a ≠ (pre ++ []).getLast! at h0
      simpa only [List.append_nil] using h0
    · intro i hi
      simpa only [List.getElem_cons_succ, List.take_succ_cons, List.append_assoc,
        List.singleton_append] using h (i + 1) (Nat.succ_lt_succ hi)
  · rintro ⟨hhead, htail⟩ i hi
    cases i with
    | zero => simpa only [List.getElem_cons_zero, List.take_zero, List.append_nil] using hhead
    | succ i =>
      simpa only [List.getElem_cons_succ, List.take_succ_cons, List.append_assoc,
        List.singleton_append] using htail i (Nat.lt_of_succ_lt_succ hi)

theorem mem_grow_zero (pre word : List Nat) :
    word ∈ ECC.growPatterns 0 pre ↔ word = pre ∧ pre.head! ≠ pre.getLast! := by
  simp only [ECC.growPatterns, bne_iff_ne]
  by_cases h : pre.head! ≠ pre.getLast!
  · rw [ite_eq_left h, List.mem_singleton]
    exact ⟨fun hw => ⟨hw, h⟩, fun hw => hw.1⟩
  · rw [ite_eq_right h]
    constructor
    · exact fun hm => False.elim (List.not_mem_nil hm)
    · exact fun hm => False.elim (h hm.2)

theorem mem_grow_succ (n : Nat) (pre word : List Nat) :
    word ∈ ECC.growPatterns (n + 1) pre ↔ ∃ a,
      a < pre.foldl Nat.max 0 + 2 ∧ a ≠ pre.getLast! ∧
      word ∈ ECC.growPatterns n (pre ++ [a]) := by
  simp only [ECC.growPatterns, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨a, ha, hm⟩
    by_cases h : a = pre.getLast!
    · simp only [beq_iff_eq, h, ite_true, List.not_mem_nil] at hm
    · exact ⟨a, ha, h, by simpa only [beq_iff_eq, ite_eq_right h] using hm⟩
  · rintro ⟨a, ha, h, hm⟩
    exact ⟨a, ha, by simpa only [beq_iff_eq, ite_eq_right h] using hm⟩

theorem mem_grow_iff (n : Nat) (pre word : List Nat) :
    word ∈ ECC.growPatterns n pre ↔ ∃ tail,
      word = pre ++ tail ∧ tail.length = n ∧ Extension pre tail ∧ word.head! ≠ word.getLast! := by
  induction n generalizing pre with
  | zero =>
    rw [mem_grow_zero]
    constructor
    · rintro ⟨hw, h⟩
      exact ⟨[], by simpa only [List.append_nil] using hw, rfl,
        extension_nil pre, by simpa only [hw] using h⟩
    · rintro ⟨tail, heq, hlen, _, hc⟩
      have ht := List.eq_nil_of_length_eq_zero hlen
      have hw : word = pre := by simpa only [ht, List.append_nil] using heq
      exact ⟨hw, by simpa only [hw] using hc⟩
  | succ n ih =>
    rw [mem_grow_succ]
    constructor
    · rintro ⟨a, ha, hn, hm⟩
      obtain ⟨tail, heq, hlen, hext, hc⟩ := (ih (pre ++ [a])).mp hm
      refine ⟨a :: tail, ?_, by simp only [List.length_cons, hlen],
        (extension_cons_iff pre a tail).mpr ⟨⟨ha, hn⟩, hext⟩, hc⟩
      simpa only [List.append_assoc, List.singleton_append] using heq
    · rintro ⟨tail, heq, hlen, hext, hc⟩
      cases tail with
      | nil => exact False.elim (Nat.noConfusion hlen)
      | cons a tail =>
        have hs := (extension_cons_iff pre a tail).mp hext
        refine ⟨a, hs.1.1, hs.1.2, (ih _).mpr ⟨tail, ?_, ?_, hs.2, hc⟩⟩
        · simpa only [List.append_assoc, List.singleton_append] using heq
        · exact Nat.add_right_cancel hlen

theorem grow_length (n : Nat) (pre word : List Nat) (h : word ∈ ECC.growPatterns n pre) :
    word.length = pre.length + n := by
  obtain ⟨tail, rfl, hlen, _, _⟩ := (mem_grow_iff n pre word).mp h
  simp only [List.length_append, hlen]

theorem grow_prefix (n : Nat) (pre word : List Nat) (h : word ∈ ECC.growPatterns n pre) :
    ∃ tail, word = pre ++ tail := by
  obtain ⟨tail, heq, _, _, _⟩ := (mem_grow_iff n pre word).mp h
  exact ⟨tail, heq⟩

theorem grow_branches_disjoint (n : Nat) (pre : List Nat) (a b : Nat) (hab : a ≠ b)
    (u v : List Nat) (hu : u ∈ ECC.growPatterns n (pre ++ [a]))
    (hv : v ∈ ECC.growPatterns n (pre ++ [b])) : u ≠ v := by
  obtain ⟨ut, hut⟩ := grow_prefix n _ u hu
  obtain ⟨vt, hvt⟩ := grow_prefix n _ v hv
  intro heq
  have same : pre ++ a :: ut = pre ++ b :: vt := by
    simpa only [List.append_assoc, List.singleton_append] using hut.symm.trans (heq.trans hvt)
  exact hab (List.cons.inj (List.append_cancel_left same)).1

def patternBranch (n : Nat) (pre : List Nat) (a : Nat) : List (List Nat) :=
  if a == pre.getLast! then [] else ECC.growPatterns n (pre ++ [a])

theorem pattern_branch_mem (n : Nat) (pre : List Nat) (a : Nat) (word : List Nat)
    (h : word ∈ patternBranch n pre a) : word ∈ ECC.growPatterns n (pre ++ [a]) := by
  unfold patternBranch at h
  split at h
  · exact False.elim (List.not_mem_nil h)
  · exact h

theorem pattern_branches_disjoint (n : Nat) (pre : List Nat) (a b : Nat) (hab : a ≠ b)
    (u v : List Nat) (hu : u ∈ patternBranch n pre a) (hv : v ∈ patternBranch n pre b) : u ≠ v :=
  grow_branches_disjoint n pre a b hab u v
    (pattern_branch_mem n pre a u hu) (pattern_branch_mem n pre b v hv)

theorem grow_nodup (n : Nat) (pre : List Nat) : (ECC.growPatterns n pre).Nodup := by
  induction n generalizing pre with
  | zero =>
    unfold ECC.growPatterns
    split <;> simp only [List.nodup_nil, List.nodup_cons, List.not_mem_nil, not_false_eq_true, and_self]
  | succ n ih =>
    change List.Pairwise (· ≠ ·)
      ((List.range (pre.foldl Nat.max 0 + 2)).flatMap (patternBranch n pre))
    rw [List.pairwise_flatMap]
    constructor
    · intro a _
      unfold patternBranch
      split
      · exact List.Pairwise.nil
      · exact ih _
    · exact (range_nodup_safe _).imp (fun {a b} hab =>
        fun u hu v hv => pattern_branches_disjoint n pre a b hab u v hu hv)

def CyclicPattern (word : List Nat) : Prop :=
  ∃ tail, word = 0 :: tail ∧ Extension [0] tail ∧ word.getLast! ≠ 0

theorem cyclic_starts_zero (word : List Nat) (h : CyclicPattern word) : word.head! = 0 := by
  obtain ⟨tail, rfl, _, _⟩ := h
  rfl

theorem cyclic_length_ge_two (word : List Nat) (h : CyclicPattern word) : 2 ≤ word.length := by
  obtain ⟨tail, hw, _, hc⟩ := h
  cases tail with
  | nil =>
    rw [hw] at hc
    exact False.elim (hc rfl)
  | cons a tail =>
    rw [hw, List.length_cons, List.length_cons]
    omega

theorem patterns_zero : ECC.patterns 0 = [] := by decide

theorem mem_patterns_iff (n : Nat) (word : List Nat) :
    word ∈ ECC.patterns n ↔ word.length = n ∧ CyclicPattern word := by
  cases n with
  | zero =>
    rw [patterns_zero]
    constructor
    · exact fun h => False.elim (List.not_mem_nil h)
    · rintro ⟨hlen, hc⟩
      have hge := cyclic_length_ge_two word hc
      rw [hlen] at hge
      exact False.elim (by omega)
  | succ n =>
    simp only [ECC.patterns, Nat.add_sub_cancel, mem_grow_iff]
    constructor
    · rintro ⟨tail, hw, hlen, hext, hc⟩
      have hw' : word = 0 :: tail := by simpa only [List.singleton_append] using hw
      refine ⟨by simp only [hw', List.length_cons, hlen], tail, hw', hext, ?_⟩
      have hhead : word.head! = 0 := by rw [hw']; rfl
      rw [hhead] at hc
      exact Ne.symm hc
    · rintro ⟨hlen, tail, hw, hext, hc⟩
      refine ⟨tail, by simpa only [List.singleton_append] using hw, ?_, hext, ?_⟩
      · exact Nat.add_right_cancel (by simpa only [hw, List.length_cons] using hlen)
      · have hhead : word.head! = 0 := by rw [hw]; rfl
        rw [hhead]
        exact Ne.symm hc

theorem patterns_nodup (n : Nat) : (ECC.patterns n).Nodup := grow_nodup (n - 1) [0]

#print axioms extension_nil
#print axioms extension_cons_iff
#print axioms mem_grow_zero
#print axioms mem_grow_succ
#print axioms mem_grow_iff
#print axioms grow_length
#print axioms grow_prefix
#print axioms grow_branches_disjoint
#print axioms pattern_branch_mem
#print axioms pattern_branches_disjoint
#print axioms grow_nodup
#print axioms cyclic_starts_zero
#print axioms cyclic_length_ge_two
#print axioms patterns_zero
#print axioms mem_patterns_iff
#print axioms patterns_nodup

end ECC.PatternGenerator
