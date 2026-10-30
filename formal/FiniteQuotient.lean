import Std
namespace ECC.FiniteQuotient

-- A deterministic finite transversal for an equivalence relation.
def select {A : Type} (R : A → A → Prop) [DecidableRel R] : Nat → List A → List A
  | 0, _ => []
  | _+1, [] => []
  | k+1, a::xs => a :: select R k (xs.filter fun b => decide (¬ R a b))

theorem select_subset {A : Type} (R : A → A → Prop) [DecidableRel R]
    (k : Nat) (xs : List A) : ∀ a, a ∈ select R k xs → a ∈ xs := by
  induction k generalizing xs with
  | zero => simp [select]
  | succ k ih =>
    cases xs with
    | nil => simp [select]
    | cons b xs =>
      intro a ha
      rcases List.mem_cons.1 ha with he | he
      · exact List.mem_cons.2 (Or.inl he)
      · exact List.mem_cons_of_mem b (List.mem_filter.1 (ih _ _ he)).1

theorem select_covers {A : Type} (R : A → A → Prop) [DecidableRel R]
    (refl : ∀ a, R a a) (_trans : ∀ a b c, R a b → R b c → R a c)
    (k : Nat) (xs : List A) (hlen : xs.length ≤ k) :
    ∀ a, a ∈ xs → ∃ b, b ∈ select R k xs ∧ R b a := by
  induction k generalizing xs with
  | zero =>
    have he : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst xs
    simp
  | succ k ih =>
    cases xs with
    | nil => simp
    | cons b xs =>
      intro a ha
      by_cases hab : R b a
      · exact ⟨b, List.mem_cons_self, hab⟩
      · have hax : a ∈ xs := (List.mem_cons.1 ha).resolve_left (fun he => hab (he ▸ refl b))
        have hfilter : (xs.filter fun a => decide (¬ R b a)).length ≤ k := by
          have hf := List.length_filter_le (fun a => decide (¬ R b a)) xs
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨c, hc, hca⟩ := ih _ hfilter a (List.mem_filter.2 ⟨hax, decide_eq_true hab⟩)
        exact ⟨c, List.mem_cons_of_mem b hc, hca⟩

theorem select_separates {A : Type} (R : A → A → Prop) [DecidableRel R]
    (_symm : ∀ a b, R a b → R b a)
    (k : Nat) (xs : List A) :
    List.Pairwise (fun a b => ¬ R a b) (select R k xs) := by
  induction k generalizing xs with
  | zero => exact List.Pairwise.nil
  | succ k ih =>
    cases xs with
    | nil => exact List.Pairwise.nil
    | cons a xs =>
      apply List.Pairwise.cons
      · intro b hb
        exact of_decide_eq_true (List.mem_filter.1 (select_subset R k _ b hb)).2
      · exact ih _

theorem select_nodup {A : Type} (R : A → A → Prop) [DecidableRel R]
    (refl : ∀ a, R a a) (symm : ∀ a b, R a b → R b a)
    (k : Nat) (xs : List A) : (select R k xs).Nodup :=
  List.Pairwise.imp (fun {a b} h => fun (he : a = b) => h (he ▸ refl a))
    (select_separates R symm k xs)

theorem select_unique {A : Type} (R : A → A → Prop) [DecidableRel R]
    (symm : ∀ a b, R a b → R b a) (k : Nat) (xs : List A)
    (a b : A) (ha : a ∈ select R k xs) (hb : b ∈ select R k xs)
    (hab : R a b) : a = b := by
  have hpair := select_separates R symm k xs
  have h := List.pairwise_iff_getElem.1 hpair
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 ha
  obtain ⟨j, hj, hf⟩ := List.mem_iff_getElem.1 hb
  by_cases hij : i < j
  · exact False.elim (h i j hi hj hij (he ▸ hf ▸ hab))
  · by_cases hji : j < i
    · exact False.elim (h j i hj hi hji (hf ▸ he ▸ symm a b hab))
    · have heq : i = j := Nat.le_antisymm (Nat.le_of_not_gt hji) (Nat.le_of_not_gt hij)
      subst j
      exact he.symm.trans hf

#print axioms select_subset
#print axioms select_covers
#print axioms select_separates
#print axioms select_nodup
#print axioms select_unique
end ECC.FiniteQuotient
