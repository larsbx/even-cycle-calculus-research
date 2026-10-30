import Std
namespace ECC.FiniteCardinality

-- Removal of one member from a duplicate-free inventory, proved constructively.
theorem remove_length {A : Type} [DecidableEq A] (ys : List A) (hys : ys.Nodup)
    (a : A) (ha : a ∈ ys) :
    (ys.filter (fun b => decide (b ≠ a))).length + 1 = ys.length := by
  induction ys with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons b ys ih =>
    have hn := List.nodup_cons.1 hys
    by_cases hb : b = a
    · subst b
      have hf : ys.filter (fun b => decide (b ≠ a)) = ys := by
        apply List.filter_eq_self.2
        intro b hb
        exact decide_eq_true (fun he => hn.1 (he ▸ hb))
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ↓reduceIte, hf, List.length_cons]
    · have hm : a ∈ ys := (List.mem_cons.1 ha).resolve_left (Ne.symm hb)
      simp only [List.filter_cons, decide_eq_true hb, ↓reduceIte,
        List.length_cons]
      exact congrArg (· + 1) (ih hn.2 hm)

theorem same_members_length {A : Type} [DecidableEq A] (xs ys : List A)
    (hx : xs.Nodup) (hy : ys.Nodup) (he : ∀ a, a ∈ xs ↔ a ∈ ys) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons a ys => exact False.elim (List.not_mem_nil ((he a).2 List.mem_cons_self))
  | cons a xs ih =>
    have hxs := List.nodup_cons.1 hx
    have ha : a ∈ ys := (he a).1 List.mem_cons_self
    have ht : ∀ b, b ∈ xs ↔ b ∈ ys.filter (fun b => decide (b ≠ a)) := by
      intro b
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · intro hb
        exact ⟨(he b).1 (List.mem_cons_of_mem a hb), fun h => hxs.1 (h ▸ hb)⟩
      · rintro ⟨hb, hne⟩
        exact (List.mem_cons.1 ((he b).2 hb)).resolve_left hne
    have hl := ih _ hxs.2 (hy.filter _) ht
    simp only [List.length_cons]
    rw [hl]
    exact remove_length ys hy a ha

#print axioms remove_length
#print axioms same_members_length
end ECC.FiniteCardinality
