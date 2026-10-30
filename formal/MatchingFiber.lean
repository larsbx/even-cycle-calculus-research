import MatchingRelabel
import MotifTransport
import FiniteCardinality

namespace ECC.MatchingFiber
open OccurrenceMatching MatchingRelabel ResolutionMatching MatchingWord MatchingLabels

theorem range_nodup (r : Nat) : (List.range r).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.2
  intro i j hi hj he
  simpa only [List.getElem_range] using he

theorem label_bound {r} (xs : List Nat) (hp : xs.Perm (List.range r)) (j : Fin r) : xs[j.val]! < r := by
  have hj : j.val < xs.length := by rw [hp.length_eq, List.length_range]; exact j.isLt
  rw [getElem!_pos xs j.val hj]
  exact List.mem_range.1 (hp.mem_iff.1 (List.getElem_mem hj))

def permute {r} (xs : List Nat) (hp : xs.Perm (List.range r)) : Fin (r+1) → Fin (r+1) :=
  Fin.cases 0 (fun j => (⟨xs[j.val]!, label_bound xs hp j⟩ : Fin r).succ)

theorem permute_zero {r} (xs : List Nat) (hp : xs.Perm (List.range r)) : permute xs hp 0 = 0 := rfl

theorem permute_injective {r} (xs : List Nat) (hp : xs.Perm (List.range r))
    (a b : Fin (r+1)) (he : permute xs hp a = permute xs hp b) : a = b := by
  revert he
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases (fun _ => rfl) (fun j => ?_) b
    intro he
    simp only [permute, Fin.cases_zero, Fin.cases_succ] at he
    exact False.elim (Fin.succ_ne_zero _ he.symm)
  · refine Fin.cases ?_ (fun j => ?_) b
    · intro he
      simp only [permute, Fin.cases_zero, Fin.cases_succ] at he
      exact False.elim (Fin.succ_ne_zero _ he)
    · intro he
      simp only [permute, Fin.cases_succ] at he
      have hh := congrArg Fin.val (Fin.succ_inj.1 he)
      have hi : i.val < xs.length := by rw [hp.length_eq, List.length_range]; exact i.isLt
      have hj : j.val < xs.length := by rw [hp.length_eq, List.length_range]; exact j.isLt
      change xs[i.val]! = xs[j.val]! at hh
      rw [getElem!_pos xs i.val hi, getElem!_pos xs j.val hj] at hh
      have hidx := List.nodup_iff_eq_of_getElem_eq.1 (hp.nodup_iff.2 (range_nodup r)) i.val j.val hi hj hh
      exact congrArg Fin.succ (Fin.ext hidx)

theorem permute_surjective {r} (xs : List Nat) (hp : xs.Perm (List.range r)) (b : Fin (r+1)) :
    ∃ a, permute xs hp a = b := by
  refine Fin.cases ⟨0,rfl⟩ (fun j => ?_) b
  have hm : j.val ∈ xs := hp.mem_iff.2 (List.mem_range.2 j.isLt)
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
  have hir : i < r := by rw [← List.length_range (n := r), ← hp.length_eq]; exact hi
  refine ⟨(⟨i,hir⟩ : Fin r).succ, ?_⟩
  simp only [permute, Fin.cases_succ]
  apply congrArg Fin.succ
  apply Fin.ext
  change xs[i]! = j.val
  rw [getElem!_pos xs i hi]
  exact he

theorem permute_positions {r L} (w : Fin L → Fin (r+1))
    (xs : List Nat) (hp : xs.Perm (List.range r)) (a : Fin (r+1)) :
    positions (fun p => permute xs hp (w p)) (permute xs hp a) = positions w a := by
  apply sorted_unique _ _ (positions_sorted _ _) (positions_sorted _ _)
  intro p
  rw [mem_positions, mem_positions]
  exact ⟨permute_injective xs hp _ _, congrArg (permute xs hp)⟩

theorem permute_profile {r L} (w : Fin L → Fin (r+1)) (hw : Profile w)
    (xs : List Nat) (hp : xs.Perm (List.range r)) : Profile (fun p => permute xs hp (w p)) := by
  constructor
  · have he := permute_positions w xs hp 0
    rw [permute_zero] at he
    rw [he, hw.1]
  · intro j
    obtain ⟨a, ha⟩ := permute_surjective xs hp j.succ
    revert ha
    refine Fin.cases ?_ (fun i => ?_) a
    · intro he
      exact False.elim (Fin.succ_ne_zero j he.symm)
    · intro he
      rw [← he, permute_positions, hw.2 i]

theorem permute_same {r L} (w : Fin L → Fin (r+1))
    (xs : List Nat) (hp : xs.Perm (List.range r)) : Same w (fun p => permute xs hp (w p)) := by
  constructor
  · intro p
    constructor
    · intro he
      change permute xs hp (w p) = 0
      rw [he, permute_zero]
    · intro he
      exact permute_injective xs hp _ _ he
  · intro p q
    exact ⟨congrArg (permute xs hp), permute_injective xs hp _ _⟩

theorem endpoint_permute {r} (xs : List Nat) (hp : xs.Perm (List.range r)) (e : End r) :
    endpointLabel xs e = (permute xs hp (axis e)).val := by
  cases e with
  | inl i => rfl
  | inr p => cases p with | mk j b => rfl

abbrev Labeling (r : Nat) := {xs : List Nat // xs ∈ labels r (List.range r)}

theorem labelingPerm {r} (xs : Labeling r) : xs.val.Perm (List.range r) :=
  (labels_membership r _ _ List.length_range).1 xs.property

def labeled {r L} (w : Fin L → Fin (r+1)) (xs : Labeling r) : Fin L → Fin (r+1) :=
  fun p => permute xs.val (labelingPerm xs) (w p)

def fiber {r L} (w : Fin L → Fin (r+1)) : List (Fin L → Fin (r+1)) :=
  (labels r (List.range r)).attach.map (labeled w)

theorem labeled_natural_word {r L} (w : Fin L → Fin (r+1)) (h : Profile w) (xs : Labeling r) :
    word (extract w h) xs.val = fun p => (labeled w xs p).val := by
  funext p
  exact (endpoint_permute xs.val (labelingPerm xs) _).trans
    (congrArg (fun a => (permute xs.val (labelingPerm xs) a).val) (read_axis w h p))

theorem labeled_injective {r L} (w : Fin L → Fin (r+1)) (h : Profile w)
    (xs ys : Labeling r) (he : labeled w xs = labeled w ys) : xs = ys := by
  apply Subtype.ext
  apply word_labels_recovered (extract w h) xs.val ys.val
    ((labelingPerm xs).length_eq.trans List.length_range)
    ((labelingPerm ys).length_eq.trans List.length_range)
  exact (labeled_natural_word w h xs).trans
    ((congrArg (fun v p => (v p).val) he).trans (labeled_natural_word w h ys).symm)

theorem fiber_length {r L} (w : Fin L → Fin (r+1)) : (fiber w).length = factorial r := by
  rw [fiber, List.length_map, List.length_attach]
  exact labels_length r _ List.length_range

theorem attach_nodup {A : Type} (xs : List A) (hn : xs.Nodup) : xs.attach.Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.2
  intro i j hi hj he
  have hi' : i < xs.length := by simpa only [List.length_attach] using hi
  have hj' : j < xs.length := by simpa only [List.length_attach] using hj
  apply List.nodup_iff_eq_of_getElem_eq.1 hn i j hi' hj'
  have hv := congrArg Subtype.val he
  simpa only [List.getElem_attach] using hv

theorem fiber_nodup {r L} (w : Fin L → Fin (r+1)) (h : Profile w) : (fiber w).Nodup := by
  unfold fiber
  change List.Pairwise (· ≠ ·) ((labels r (List.range r)).attach.map (labeled w))
  rw [List.pairwise_map]
  exact (attach_nodup _ (labels_nodup r _ (range_nodup r))).imp
    (fun {xs ys} hne he => hne (labeled_injective w h xs ys he))

theorem fiber_membership {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) :
    v ∈ fiber w ↔ Profile v ∧ Same w v := by
  constructor
  · intro hv
    obtain ⟨xs, _, rfl⟩ := List.mem_map.1 hv
    exact ⟨permute_profile w h xs.val (labelingPerm xs), permute_same w xs.val (labelingPerm xs)⟩
  · rintro ⟨hv, hs⟩
    obtain ⟨xs, hp, he⟩ := (words_membership _ _).1 (same_in_fixed_fiber w v h hv hs)
    let x : Labeling r := ⟨xs, (labels_membership r _ _ List.length_range).2 hp⟩
    apply List.mem_map.2
    refine ⟨x, List.mem_attach _ x, ?_⟩
    funext p
    apply Fin.ext
    have hn := congrFun ((labeled_natural_word w h x).symm.trans he) p
    exact hn

#print axioms range_nodup
#print axioms label_bound
#print axioms permute_zero
#print axioms permute_injective
#print axioms permute_surjective
#print axioms permute_positions
#print axioms permute_profile
#print axioms permute_same
#print axioms endpoint_permute
#print axioms labelingPerm
#print axioms labeled_natural_word
#print axioms labeled_injective
#print axioms fiber_length
#print axioms attach_nodup
#print axioms fiber_nodup
#print axioms fiber_membership
end ECC.MatchingFiber
