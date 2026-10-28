import CanonicalTrace

/- Finite order-preserving compression of first-occurrence representatives.
   This is not yet deletion of stationary steps or a cycle/shuffle bijection. -/
namespace ECC.RankCompression
open ECC.CanonicalTrace

def positions {α : Type} [DecidableEq α] {m : Nat} (v : Fin (m+1) → α) :=
  (List.finRange (m+1)).filter fun r => decide (first v r = r)

theorem positions_mem_iff {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (r : Fin (m+1)) :
    r ∈ positions v ↔ first v r = r := by
  simp [positions, List.mem_finRange]

theorem positions_nodup {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) : (positions v).Nodup :=
  List.Pairwise.filter _ (List.nodup_finRange (m+1))

theorem positions_sorted {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) : (positions v).Pairwise (· < ·) :=
  List.Pairwise.filter _ (List.pairwise_lt_finRange (m+1))

def rank {α : Type} [DecidableEq α] {m : Nat} (v : Fin (m+1) → α)
    (r : Representative v) : Fin (positions v).length :=
  ⟨(positions v).idxOf r.val,
    by
      -- Use the constructive equality instance rather than an order-derived one.
      letI : EquivBEq (Fin (m+1)) :=
        equivBEq_of_iff_apply_eq (fun x : Fin (m+1) => x) (fun _ _ => beq_iff_eq)
      exact List.idxOf_lt_length_of_mem ((positions_mem_iff v r.val).2 r.property)⟩

def unrank {α : Type} [DecidableEq α] {m : Nat} (v : Fin (m+1) → α)
    (i : Fin (positions v).length) : Representative v :=
  ⟨(positions v)[i.val], (positions_mem_iff v _).1 (List.getElem_mem i.isLt)⟩

theorem unrank_rank {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (r : Representative v) : unrank v (rank v r) = r := by
  apply Subtype.ext
  exact List.getElem_idxOf (rank v r).isLt

theorem rank_unrank {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (i : Fin (positions v).length) : rank v (unrank v i) = i := by
  apply Fin.ext
  exact (positions_nodup v).idxOf_getElem i.val i.isLt

theorem rank_injective {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (r s : Representative v) (h : rank v r = rank v s) : r = s :=
  (unrank_rank v r).symm.trans ((congrArg (unrank v) h).trans (unrank_rank v s))

theorem unrank_injective {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (i j : Fin (positions v).length) (h : unrank v i = unrank v j) : i = j :=
  (rank_unrank v i).symm.trans ((congrArg (rank v) h).trans (rank_unrank v j))

theorem rank_lt_implies {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (r s : Representative v)
    (h : (rank v r).val < (rank v s).val) : r.val.val < s.val.val := by
  have ordered := (positions_sorted v).rel_getElem_of_lt (rank v r).isLt (rank v s).isLt h
  change (positions v)[(positions v).idxOf r.val]'(rank v r).isLt <
    (positions v)[(positions v).idxOf s.val]'(rank v s).isLt at ordered
  rw [List.getElem_idxOf (rank v r).isLt, List.getElem_idxOf (rank v s).isLt] at ordered
  exact Fin.lt_def.mp ordered

theorem rank_lt_iff {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (r s : Representative v) :
    (rank v r).val < (rank v s).val ↔ r.val.val < s.val.val := by
  constructor
  · exact rank_lt_implies v r s
  · intro h
    by_cases hr : (rank v r).val < (rank v s).val
    · exact hr
    · have neq : (rank v r).val ≠ (rank v s).val := by
        intro heq
        have same := rank_injective v r s (Fin.ext heq)
        have hv := congrArg (fun x : Representative v => x.val.val) same
        omega
      have reversed : (rank v s).val < (rank v r).val := by omega
      have bad := rank_lt_implies v s r reversed
      omega

def encode {α : Type} [DecidableEq α] {m : Nat} (v : Fin (m+1) → α)
    (t : Fin (m+1)) : Fin (positions v).length := rank v (extract v t)

def decode {α : Type} [DecidableEq α] {m : Nat} (v : Fin (m+1) → α)
    (i : Fin (positions v).length) : α := realize v (unrank v i)

theorem decode_encode {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t : Fin (m+1)) : decode v (encode v t) = v t := by
  unfold decode encode
  rw [unrank_rank]
  exact realize_extract v t

theorem encode_representative {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (i : Fin (positions v).length) :
    encode v (unrank v i).val = i := by
  unfold encode
  rw [extract_representative, rank_unrank]

theorem encode_surjective {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (i : Fin (positions v).length) : ∃ t, encode v t = i :=
  ⟨(unrank v i).val, encode_representative v i⟩

theorem decode_injective {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (i j : Fin (positions v).length)
    (h : decode v i = decode v j) : i = j :=
  unrank_injective v i j (realize_injective v _ _ h)

theorem encode_eq_iff {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (s t : Fin (m+1)) : encode v s = encode v t ↔ v s = v t := by
  constructor
  · intro h
    exact (decode_encode v s).symm.trans ((congrArg (decode v) h).trans (decode_encode v t))
  · intro h
    apply congrArg (rank v)
    apply Subtype.ext
    exact first_eq_of_value_eq v s t h

/- Every smaller ordinal has already appeared, not merely been allocated. -/
theorem initial_segment_seen {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t : Fin (m+1)) (i : Fin (positions v).length)
    (h : i.val < (encode v t).val) :
    ∃ s, s.val < t.val ∧ encode v s = i := by
  have hr : (rank v (unrank v i)).val < (rank v (extract v t)).val := by
    simpa only [rank_unrank, encode] using h
  have earlier := (rank_lt_iff v (unrank v i) (extract v t)).1 hr
  have bound := first_le v t
  refine ⟨(unrank v i).val, ?_, encode_representative v i⟩
  change (unrank v i).val.val < (first v t).val at earlier
  omega

theorem encode_zero {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) : (encode v 0).val = 0 := by
  by_cases h : (encode v 0).val = 0
  · exact h
  · have pos : 0 < (encode v 0).val := by omega
    have bound := (encode v 0).isLt
    obtain ⟨s, hs, _⟩ := initial_segment_seen v 0 ⟨0, by omega⟩ pos
    change s.val < 0 at hs
    omega

theorem predecessor_seen {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t : Fin (m+1)) (h : 0 < (encode v t).val) :
    ∃ s, s.val < t.val ∧ (encode v s).val + 1 = (encode v t).val := by
  have bound := (encode v t).isLt
  let i : Fin (positions v).length := ⟨(encode v t).val - 1, by omega⟩
  obtain ⟨s, hs, heq⟩ := initial_segment_seen v t i (by dsimp [i]; omega)
  refine ⟨s, hs, ?_⟩
  have hv := congrArg Fin.val heq
  dsimp [i] at hv
  omega

theorem fold_max_bounds (xs : List Nat) (initial : Nat) :
    initial ≤ xs.foldl Nat.max initial ∧ ∀ x ∈ xs, x ≤ xs.foldl Nat.max initial := by
  induction xs generalizing initial with
  | nil => simp
  | cons a xs ih =>
    have tail := ih (Nat.max initial a)
    refine ⟨Nat.le_trans (Nat.le_max_left initial a) tail.1, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with heq | hx
    · subst x
      exact Nat.le_trans (Nat.le_max_right initial a) tail.1
    · exact tail.2 x hx

def prefixLabels {α : Type} [DecidableEq α] {m : Nat} (v : Fin (m+1) → α)
    (t : Fin (m+1)) : List Nat :=
  (List.finRange t.val).map fun s => (encode v ⟨s.val, by omega⟩).val

theorem append_bound {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t : Fin (m+1)) :
    (encode v t).val ≤ (prefixLabels v t).foldl Nat.max 0 + 1 := by
  by_cases zero : (encode v t).val = 0
  · omega
  · have positive : 0 < (encode v t).val := by omega
    obtain ⟨s, hs, heq⟩ := predecessor_seen v t positive
    have member : (encode v s).val ∈ prefixLabels v t := by
      apply List.mem_map.2
      exact ⟨⟨s.val, hs⟩, List.mem_finRange _, rfl⟩
    have bound := (fold_max_bounds (prefixLabels v t) 0).2 _ member
    omega

/- This is the literal candidate-label range used by growPatterns in Shuffle.lean. -/
theorem enumerator_label_allowed {α : Type} [DecidableEq α] {m : Nat}
    (v : Fin (m+1) → α) (t : Fin (m+1)) :
    (encode v t).val ∈ List.range ((prefixLabels v t).foldl Nat.max 0 + 2) := by
  apply List.mem_range.2
  have bound := append_bound v t
  omega

#print axioms positions_mem_iff
#print axioms positions_nodup
#print axioms positions_sorted
#print axioms unrank_rank
#print axioms rank_unrank
#print axioms rank_injective
#print axioms unrank_injective
#print axioms rank_lt_implies
#print axioms rank_lt_iff
#print axioms decode_encode
#print axioms encode_representative
#print axioms encode_surjective
#print axioms decode_injective
#print axioms encode_eq_iff
#print axioms initial_segment_seen
#print axioms encode_zero
#print axioms predecessor_seen
#print axioms fold_max_bounds
#print axioms append_bound
#print axioms enumerator_label_allowed

end ECC.RankCompression
