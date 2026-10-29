import Std

/- Canonical coordinate extraction by a bounded first-occurrence scan.
   No unbounded search, choice of representatives, or graph-counting axiom. -/
namespace ECC.CanonicalTrace

def scan {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (target : α) : (k : Nat) → k ≤ m → Fin (m+1)
  | 0, _ => 0
  | k+1, hk =>
      let previous := scan v target k (by omega)
      if v previous = target then previous else ⟨k+1, by omega⟩

theorem scan_spec {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (target : α) (k : Nat) (hk : k ≤ m) :
    (scan v target k hk).val ≤ k ∧
    (∀ j, j.val < (scan v target k hk).val → v j ≠ target) ∧
    (v (scan v target k hk) ≠ target → (scan v target k hk).val = k) := by
  induction k with
  | zero =>
    refine ⟨by simp [scan], ?_, ?_⟩
    · intro j hj
      simp [scan] at hj
    · intro _
      rfl
  | succ k ih =>
    have hprev : k ≤ m := by omega
    have previous := ih hprev
    simp only [scan]
    split
    · rename_i heq
      exact ⟨by omega, previous.2.1, fun hne => False.elim (hne heq)⟩
    · rename_i hne
      have last := previous.2.2 hne
      refine ⟨by simp, ?_, fun _ => rfl⟩
      intro j hj heq
      change j.val < k+1 at hj
      by_cases hjk : j.val < k
      · exact previous.2.1 j (by omega) heq
      · have same : j = scan v target k hprev := Fin.ext (by omega)
        exact hne (same ▸ heq)

def first {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t : Fin (m+1)) : Fin (m+1) :=
  scan v (v t) t.val (by omega)

theorem first_le {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t : Fin (m+1)) : (first v t).val ≤ t.val :=
  (scan_spec v (v t) t.val (by omega)).1

theorem first_value {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t : Fin (m+1)) : v (first v t) = v t := by
  by_cases h : v (first v t) = v t
  · exact h
  · have same := (scan_spec v (v t) t.val (by omega)).2.2 h
    have ht : first v t = t := Fin.ext same
    exact False.elim (h (congrArg v ht))

theorem first_minimal {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t s : Fin (m+1)) (h : v s = v t) :
    (first v t).val ≤ s.val := by
  have noEarlier := (scan_spec v (v t) t.val (by omega)).2.1
  by_cases hs : s.val < (first v t).val
  · exact False.elim (noEarlier s hs h)
  · omega

theorem first_eq_of_value_eq {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (s t : Fin (m+1)) (h : v s = v t) :
    first v s = first v t := by
  have left := first_minimal v s (first v t) ((first_value v t).trans h.symm)
  have right := first_minimal v t (first v s) ((first_value v s).trans h)
  exact Fin.ext (Nat.le_antisymm left right)

theorem first_eq_iff {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (s t : Fin (m+1)) :
    first v s = first v t ↔ v s = v t := by
  constructor
  · intro h
    exact (first_value v s).symm.trans ((congrArg v h).trans (first_value v t))
  · exact first_eq_of_value_eq v s t

theorem first_idempotent {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t : Fin (m+1)) :
    first v (first v t) = first v t :=
  first_eq_of_value_eq v _ _ (first_value v t)

abbrev Representative {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) := {r : Fin (m+1) // first v r = r}

def extract {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t : Fin (m+1)) : Representative v :=
  ⟨first v t, first_idempotent v t⟩

def realize {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (r : Representative v) : α := v r.val

theorem realize_extract {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t : Fin (m+1)) :
    realize v (extract v t) = v t := first_value v t

theorem extract_representative {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (r : Representative v) : extract v r.val = r := by
  apply Subtype.ext
  exact r.property

theorem realize_injective {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (r s : Representative v)
    (h : realize v r = realize v s) : r = s := by
  apply Subtype.ext
  have same := first_eq_of_value_eq v r.val s.val h
  exact r.property.symm.trans (same.trans s.property)

theorem first_injective_relabeling {α β : Type} [DecidableEq α] [DecidableEq β]
    {m : Nat} (v : Fin (m+1) → α) (f : α → β)
    (hf : ∀ u w, f u = f w → u = w) (t : Fin (m+1)) :
    first (fun s => f (v s)) t = first v t := by
  have left := first_minimal (fun s => f (v s)) t (first v t)
    (congrArg f (first_value v t))
  have right := first_minimal v t (first (fun s => f (v s)) t)
    (hf _ _ (first_value (fun s => f (v s)) t))
  exact Fin.ext (Nat.le_antisymm left right)

theorem first_equality_relation {α β : Type} [DecidableEq α] [DecidableEq β]
    {m : Nat} (v : Fin (m+1) → α) (w : Fin (m+1) → β)
    (sameEquality : ∀ s t, v s = v t ↔ w s = w t) (t : Fin (m+1)) :
    first v t = first w t := by
  have left := first_minimal v t (first w t)
    ((sameEquality _ _).2 (first_value w t))
  have right := first_minimal w t (first v t)
    ((sameEquality _ _).1 (first_value v t))
  exact Fin.ext (Nat.le_antisymm left right)

theorem normalized_shape_recovered {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (shape : Fin (m+1) → Fin (m+1))
    (normalized : ∀ t, first shape t = shape t)
    (sameEquality : ∀ s t, v s = v t ↔ shape s = shape t) :
    first v = shape := by
  funext t
  exact (first_equality_relation v shape sameEquality t).trans (normalized t)

theorem canonical_shape_unique {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (shape other : Fin (m+1) → Fin (m+1))
    (normalized : ∀ t, first shape t = shape t)
    (otherNormalized : ∀ t, first other t = other t)
    (sameEquality : ∀ s t, v s = v t ↔ shape s = shape t)
    (otherEquality : ∀ s t, v s = v t ↔ other s = other t) : shape = other :=
  (normalized_shape_recovered v shape normalized sameEquality).symm.trans
    (normalized_shape_recovered v other otherNormalized otherEquality)

theorem extract_surjective {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (r : Representative v) : ∃ t, extract v t = r :=
  ⟨r.val, extract_representative v r⟩

#print axioms scan_spec
#print axioms first_le
#print axioms first_value
#print axioms first_minimal
#print axioms first_eq_of_value_eq
#print axioms first_eq_iff
#print axioms first_idempotent
#print axioms realize_extract
#print axioms extract_representative
#print axioms realize_injective
#print axioms first_injective_relabeling
#print axioms first_equality_relation
#print axioms normalized_shape_recovered
#print axioms canonical_shape_unique
#print axioms extract_surjective

end ECC.CanonicalTrace
