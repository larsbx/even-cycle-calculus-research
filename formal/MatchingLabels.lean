import Std

/- Independent choose-a-head proof of labeled matching multiplicity.
   This does not use ECC.words, kernels/repeated_edge.py or its matching recursion. -/
namespace ECC.MatchingLabels

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

def labels : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | n+1, xs => xs.flatMap fun a => (labels n (xs.erase a)).map (a :: ·)

theorem erase_length (xs : List Nat) (a : Nat) (ha : a ∈ xs) :
    (xs.erase a).length = xs.length - 1 := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons b xs ih =>
    by_cases h : b = a
    · subst b
      simp only [List.erase_cons_head, List.length_cons, Nat.add_sub_cancel]
    · have hm : a ∈ xs := (List.mem_cons.1 ha).resolve_left (Ne.symm h)
      simp only [List.erase_cons, beq_iff_eq, h, ↓reduceIte, List.length_cons]
      rw [ih hm]
      have hp : 0 < xs.length := List.length_pos_of_mem hm
      omega

theorem head_perm (xs : List Nat) (a : Nat) (ha : a ∈ xs) :
    xs.Perm (a :: xs.erase a) := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons b xs ih =>
    by_cases h : b = a
    · subst b
      rw [List.erase_cons_head]
    · have hm : a ∈ xs := (List.mem_cons.1 ha).resolve_left (Ne.symm h)
      simp only [List.erase_cons, beq_iff_eq, h, ↓reduceIte]
      exact ((ih hm).cons b).trans (List.Perm.swap a b _)

theorem labels_membership (n : Nat) (xs ys : List Nat) (hlen : xs.length = n) :
    ys ∈ labels n xs ↔ ys.Perm xs := by
  induction n generalizing xs ys with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero hlen
    subst xs
    simp [labels]
  | succ n ih =>
    simp only [labels, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a, ha, zs, hz, rfl⟩
      have he : (xs.erase a).length = n := by rw [erase_length xs a ha, hlen]; exact Nat.add_sub_cancel n 1
      exact (((ih _ _ he).1 hz).cons a).trans (head_perm xs a ha).symm
    · intro hp
      cases ys with
      | nil =>
        have he := hp.length_eq
        rw [List.length_nil, hlen] at he
        exact False.elim (Nat.noConfusion he)
      | cons a zs =>
        have ha : a ∈ xs := hp.mem_iff.1 List.mem_cons_self
        have hz : zs.Perm (xs.erase a) := (hp.trans (head_perm xs a ha)).cons_inv
        have he : (xs.erase a).length = n := by rw [erase_length xs a ha, hlen]; exact Nat.add_sub_cancel n 1
        exact ⟨a, ha, zs, (ih _ _ he).2 hz, rfl⟩

theorem flatMap_constant_length {A B : Type} (xs : List A) (f : A → List B) (k : Nat)
    (h : ∀ a, a ∈ xs → (f a).length = k) :
    (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem a hb))]
    simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem labels_length (n : Nat) (xs : List Nat) (hlen : xs.length = n) :
    (labels n xs).length = factorial n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    simp only [labels]
    rw [flatMap_constant_length xs _ (factorial n), hlen]
    · rfl
    · intro a ha
      rw [List.length_map]
      apply ih
      rw [erase_length xs a ha, hlen]
      exact Nat.add_sub_cancel n 1

theorem prefix_nodup (a : Nat) (xs : List (List Nat)) (h : xs.Nodup) :
    (xs.map (a :: ·)).Nodup := by
  induction h with
  | nil => simp
  | @cons x xs hx hxs ih =>
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hm
    obtain ⟨y, hy, he⟩ := List.mem_map.1 hm
    have heq : y = x := (List.cons.inj he).2
    subst y
    exact hx x hy rfl

theorem labels_nodup (n : Nat) (xs : List Nat) (hx : xs.Nodup) :
    (labels n xs).Nodup := by
  induction n generalizing xs with
  | zero => simp [labels]
  | succ n ih =>
    change List.Pairwise (· ≠ ·) (xs.flatMap _)
    rw [List.pairwise_flatMap]
    constructor
    · intro a _
      exact prefix_nodup a _ (ih _ (List.Nodup.erase a hx))
    · exact hx.imp (fun {a b} hab => by
        intro u hu v hv he
        obtain ⟨ut, _, heu⟩ := List.mem_map.1 hu
        obtain ⟨vt, _, hev⟩ := List.mem_map.1 hv
        exact hab (List.cons.inj (heu.trans (he.trans hev.symm))).1)

#print axioms erase_length
#print axioms head_perm
#print axioms labels_membership
#print axioms flatMap_constant_length
#print axioms labels_length
#print axioms prefix_nodup
#print axioms labels_nodup
end ECC.MatchingLabels
