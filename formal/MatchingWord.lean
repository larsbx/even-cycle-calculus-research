import ResolutionMatching
import MatchingLabels

namespace ECC.MatchingWord
open ResolutionMatching MatchingLabels

def endpoints (r : Nat) : List (End r) :=
  (List.ofFn (fun i : Fin 4 => Sum.inl i)) ++
    (List.ofFn (fun i : Fin r => i)).flatMap (fun i => [Sum.inr (i, false), Sum.inr (i, true)])

theorem mem_endpoints {r} (e : End r) : e ∈ endpoints r := by
  cases e with
  | inl i => exact List.mem_append_left _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  | inr p =>
    cases p with
    | mk i b =>
      apply List.mem_append_right
      apply List.mem_flatMap.2
      refine ⟨i, List.mem_ofFn.2 ⟨i, rfl⟩, ?_⟩
      cases b <;> simp

def read {r L} (M : Matching r L) (p : Fin L) : End r :=
  ((endpoints r).find? fun e => M.pos e == p.val).getD (.inl 0)

theorem pos_read {r L} (M : Matching r L) (p : Fin L) : M.pos (read M p) = p.val := by
  unfold read
  cases h : (endpoints r).find? (fun e => M.pos e == p.val) with
  | none =>
    have hn := List.find?_eq_none.1 h
    obtain ⟨e, he⟩ := M.cover p.val p.isLt
    exact False.elim (hn e (mem_endpoints e) (beq_iff_eq.2 he))
  | some e =>
    change M.pos e = p.val
    exact beq_iff_eq.1 (List.find?_some (p := fun e => M.pos e == p.val) h)

theorem read_pos {r L} (M : Matching r L) (e : End r) :
    read M ⟨M.pos e, M.bound e⟩ = e := M.injective _ _ (pos_read M _)

def endpointLabel {r} (xs : List Nat) : End r → Nat
  | .inl _ => 0
  | .inr (i, _) => xs[i.val]! + 1

def word {r L} (M : Matching r L) (xs : List Nat) (p : Fin L) : Nat :=
  endpointLabel xs (read M p)

theorem word_at_endpoint {r L} (M : Matching r L) (xs : List Nat) (e : End r) :
    word M xs ⟨M.pos e, M.bound e⟩ = endpointLabel xs e := by
  simp only [word, read_pos]

theorem word_labels_recovered {r L} (M : Matching r L) (xs ys : List Nat)
    (hx : xs.length = r) (hy : ys.length = r) (he : word M xs = word M ys) : xs = ys := by
  apply List.ext_getElem (hx.trans hy.symm)
  intro i hi hj
  have hir : i < r := hx ▸ hi
  have h := congrFun he ⟨M.pos (.inr (⟨i, hir⟩, false)), M.bound _⟩
  simp only [word_at_endpoint, endpointLabel, getElem!_pos xs i hi, getElem!_pos ys i hj] at h
  exact Nat.add_right_cancel h

def words {r L} (M : Matching r L) : List (Fin L → Nat) :=
  (labels r (List.range r)).map (word M)

theorem words_length {r L} (M : Matching r L) :
    (words M).length = factorial r := by
  rw [words, List.length_map]
  exact labels_length r _ (List.length_range (n := r))

theorem words_nodup {r L} (M : Matching r L) : (words M).Nodup := by
  unfold words
  change List.Pairwise (· ≠ ·) (List.map (word M) (labels r (List.range r)))
  rw [List.pairwise_map]
  have hr : (List.range r).Nodup :=
    by
      apply List.nodup_iff_eq_of_getElem_eq.2
      intro i j hi hj he
      simpa only [List.getElem_range] using he
  apply List.Pairwise.imp_of_mem (p := labels_nodup r _ hr)
  intro xs ys hx hy hne he
  have hpx := (labels_membership r _ _ (List.length_range (n := r))).1 hx
  have hpy := (labels_membership r _ _ (List.length_range (n := r))).1 hy
  exact hne (word_labels_recovered M xs ys
    (hpx.length_eq.trans (List.length_range (n := r)))
    (hpy.length_eq.trans (List.length_range (n := r))) he)

theorem words_membership {r L} (M : Matching r L) (w : Fin L → Nat) :
    w ∈ words M ↔ ∃ xs, xs.Perm (List.range r) ∧ word M xs = w := by
  simp only [words, List.mem_map, labels_membership r _ _ (List.length_range (n := r))]

#print axioms mem_endpoints
#print axioms pos_read
#print axioms read_pos
#print axioms word_at_endpoint
#print axioms word_labels_recovered
#print axioms words_length
#print axioms words_nodup
#print axioms words_membership
end ECC.MatchingWord
