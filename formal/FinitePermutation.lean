import MatchingLabels
namespace ECC.FinitePermutation
open MatchingLabels

theorem erase_mem_of_ne (xs : List Nat) (a b : Nat) (hab : a ≠ b) :
    a ∈ xs.erase b ↔ a ∈ xs := by
  induction xs with
  | nil => simp only [List.erase_nil, List.not_mem_nil]
  | cons c xs ih =>
    by_cases hcb : c = b
    · subst c
      simp only [List.erase_cons_head, List.mem_cons, hab, false_or]
    · simp only [List.erase_cons, beq_iff_eq, hcb, ↓reduceIte, List.mem_cons, ih]

theorem erase_self_not_mem (xs : List Nat) (hn : xs.Nodup) (a : Nat) : a ∉ xs.erase a := by
  induction xs with
  | nil => exact List.not_mem_nil
  | cons b xs ih =>
    have hx := List.nodup_cons.1 hn
    by_cases hba : b = a
    · subst b
      simpa only [List.erase_cons_head] using hx.1
    · simp only [List.erase_cons, beq_iff_eq, hba, ↓reduceIte, List.mem_cons]
      intro he
      rcases he with he | he
      · exact hba he.symm
      · exact ih hx.2 he

theorem perm_of_same_members (xs ys : List Nat) (hx : xs.Nodup) (hy : ys.Nodup)
    (hm : ∀ a, a ∈ xs ↔ a ∈ ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact List.Perm.refl _
    | cons a ys => exact False.elim (List.not_mem_nil ((hm a).2 List.mem_cons_self))
  | cons a xs ih =>
    have hxs := List.nodup_cons.1 hx
    have ha : a ∈ ys := (hm a).1 List.mem_cons_self
    have ht : ∀ b, b ∈ xs ↔ b ∈ ys.erase a := by
      intro b
      by_cases hba : b = a
      · subst b
        constructor
        · intro hb; exact False.elim (hxs.1 hb)
        · intro hb; exact False.elim (erase_self_not_mem ys hy a hb)
      · rw [erase_mem_of_ne ys b a hba]
        constructor
        · intro hb; exact (hm b).1 (List.mem_cons_of_mem a hb)
        · intro hb; exact (List.mem_cons.1 ((hm b).2 hb)).resolve_left hba
    exact ((ih _ hxs.2 (List.Nodup.erase a hy) ht).cons a).trans (head_perm ys a ha).symm

#print axioms erase_mem_of_ne
#print axioms erase_self_not_mem
#print axioms perm_of_same_members
end ECC.FinitePermutation
