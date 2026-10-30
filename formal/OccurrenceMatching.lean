import MatchingWord

namespace ECC.OccurrenceMatching
open ResolutionMatching MatchingWord

-- Literal finite words, with occurrence counts rather than a supplied matching.
def positions {L q} (w : Fin L → Fin q) (a : Fin q) : List (Fin L) :=
  (List.ofFn (fun p : Fin L => p)).filter fun p => w p == a

def Profile {r L} (w : Fin L → Fin (r+1)) : Prop :=
  (positions w 0).length = 4 ∧ ∀ j : Fin r, (positions w j.succ).length = 2

instance {r L} (w : Fin L → Fin (r+1)) : Decidable (Profile w) :=
  inferInstanceAs (Decidable ((positions w 0).length = 4 ∧ ∀ j : Fin r,
    (positions w j.succ).length = 2))

theorem mem_positions {L q} (w : Fin L → Fin q) (a : Fin q) (p : Fin L) :
    p ∈ positions w a ↔ w p = a := by
  simp only [positions, List.mem_filter, beq_iff_eq]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨List.mem_ofFn.2 ⟨p, rfl⟩, h⟩

theorem positions_nodup {L q} (w : Fin L → Fin q) (a : Fin q) :
    (positions w a).Nodup := by
  have hn : (List.ofFn (fun p : Fin L => p)).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.2
    intro i j hi hj he
    have heq : (⟨i, by simpa only [List.length_ofFn] using hi⟩ : Fin L) =
        ⟨j, by simpa only [List.length_ofFn] using hj⟩ := by
      simpa only [List.getElem_ofFn] using he
    exact congrArg Fin.val heq
  exact hn.filter _

theorem positions_sorted {L q} (w : Fin L → Fin q) (a : Fin q) :
    List.Pairwise (fun p q => p.val < q.val) (positions w a) := by
  have hs : List.Pairwise (fun p q : Fin L => p.val < q.val)
      (List.ofFn (fun p : Fin L => p)) := by
    apply List.pairwise_iff_getElem.2
    intro i j hi hj hij
    simpa only [List.getElem_ofFn] using hij
  exact hs.filter _

def occurrence {L q} (w : Fin L → Fin q) (a : Fin q) (i : Nat)
    (hi : i < (positions w a).length) : Fin L := (positions w a)[i]

theorem at_label {L q} (w : Fin L → Fin q) (a : Fin q) (i hi) :
    w (occurrence w a i hi) = a :=
  (mem_positions w a _).1 (List.getElem_mem hi)

theorem at_injective {L q} (w : Fin L → Fin q) (a : Fin q)
    (i j : Nat) (hi : i < (positions w a).length) (hj : j < (positions w a).length)
    (he : occurrence w a i hi = occurrence w a j hj) : i = j :=
  List.nodup_iff_eq_of_getElem_eq.1 (positions_nodup w a) i j hi hj he

theorem at_strict {L q} (w : Fin L → Fin q) (a : Fin q)
    (i j : Nat) (hi : i < (positions w a).length) (hj : j < (positions w a).length)
    (hij : i < j) : (occurrence w a i hi).val < (occurrence w a j hj).val :=
  List.pairwise_iff_getElem.1 (positions_sorted w a) i j hi hj hij

def axis {r} : End r → Fin (r+1)
  | .inl _ => 0
  | .inr (j, _) => j.succ

def slot {r} : End r → Nat
  | .inl i => i.val
  | .inr (_, b) => if b then 1 else 0

theorem slot_bound {r L} (w : Fin L → Fin (r+1)) (h : Profile w) (e : End r) :
    slot e < (positions w (axis e)).length := by
  cases e with
  | inl i => simpa only [slot, axis, h.1] using i.isLt
  | inr p => cases p with | mk j b => cases b <;> simp only [slot, axis, h.2 j] <;> decide

def event {r L} (w : Fin L → Fin (r+1)) (h : Profile w) (e : End r) : Fin L :=
  occurrence w (axis e) (slot e) (slot_bound w h e)

theorem event_label {r L} (w : Fin L → Fin (r+1)) (h : Profile w) (e : End r) :
    w (event w h e) = axis e := at_label w _ _ _

theorem event_injective {r L} (w : Fin L → Fin (r+1)) (h : Profile w)
    (e f : End r) (he : event w h e = event w h f) : e = f := by
  have ha : axis e = axis f := (event_label w h e).symm.trans
    ((congrArg w he).trans (event_label w h f))
  cases e with
  | inl i =>
    cases f with
    | inl j =>
      have hij := at_injective w 0 i.val j.val (slot_bound w h (.inl i))
        (slot_bound w h (.inl j)) he
      exact congrArg Sum.inl (Fin.ext hij)
    | inr p =>
      have hn := congrArg Fin.val ha
      simp only [axis, Fin.val_zero, Fin.val_succ] at hn
      omega
  | inr p =>
    cases p with
    | mk i b =>
      cases f with
      | inl j =>
        have hn := congrArg Fin.val ha
        simp only [axis, Fin.val_zero, Fin.val_succ] at hn
        omega
      | inr p =>
        cases p with
        | mk j c =>
          have hij : i = j := Fin.succ_inj.1 ha
          subst j
          have hs := at_injective w i.succ (slot (.inr (i,b))) (slot (.inr (i,c)))
            (slot_bound w h _) (slot_bound w h _) he
          have hbc : b = c := by
            cases b <;> cases c <;> (try simp only [slot, ↓reduceIte] at hs) <;> first | rfl | contradiction
          subst c
          rfl

theorem event_cover {r L} (w : Fin L → Fin (r+1)) (h : Profile w) (p : Fin L) :
    ∃ e, event w h e = p := by
  have hm : p ∈ positions w (w p) := (mem_positions w _ _).2 rfl
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
  generalize ha : w p = a at hi he
  revert hi he
  refine Fin.cases ?_ (fun j => ?_) a
  · intro hi he
    have hi4 : i < 4 := h.1 ▸ hi
    exact ⟨.inl ⟨i, hi4⟩, he⟩
  · intro hi he
    have hi2 : i < 2 := h.2 j ▸ hi
    by_cases hz : i = 0
    · subst i
      exact ⟨.inr (j,false), he⟩
    · have ho : i = 1 := by omega
      subst i
      exact ⟨.inr (j,true), he⟩

def extract {r L} (w : Fin L → Fin (r+1)) (h : Profile w) : Matching r L where
  pos := fun e => (event w h e).val
  injective := fun e f he => event_injective w h e f (Fin.ext he)
  bound := fun e => (event w h e).isLt
  cover := by
    intro p hp
    obtain ⟨e, he⟩ := event_cover w h ⟨p,hp⟩
    exact ⟨e, congrArg Fin.val he⟩
  distinguished := ⟨at_strict w 0 0 1 _ _ (by decide),
    at_strict w 0 1 2 _ _ (by decide), at_strict w 0 2 3 _ _ (by decide)⟩
  rest := fun j => at_strict w j.succ 0 1 _ _ (by decide)

theorem read_axis {r L} (w : Fin L → Fin (r+1)) (h : Profile w) (p : Fin L) :
    axis (read (extract w h) p) = w p := by
  have he := pos_read (extract w h) p
  have hp : event w h (read (extract w h) p) = p := Fin.ext he
  exact (event_label w h _).symm.trans (congrArg w hp)

theorem range_endpoint_label {r} (e : End r) :
    endpointLabel (List.range r) e = (axis e).val := by
  cases e with
  | inl i => rfl
  | inr p =>
    cases p with
    | mk i b =>
      simp only [endpointLabel, axis, Fin.val_succ,
        getElem!_pos (List.range r) i.val (by simpa only [List.length_range] using i.isLt),
        List.getElem_range]

theorem reconstruct_word {r L} (w : Fin L → Fin (r+1)) (h : Profile w) :
    word (extract w h) (List.range r) = fun p => (w p).val := by
  funext p
  exact (range_endpoint_label (read (extract w h) p)).trans (congrArg Fin.val (read_axis w h p))

theorem original_in_fixed_matching_fiber {r L} (w : Fin L → Fin (r+1)) (h : Profile w) :
    (fun p => (w p).val) ∈ words (extract w h) := by
  apply (words_membership _ _).2
  exact ⟨List.range r, List.Perm.refl _, reconstruct_word w h⟩

def vertex {r L} (M : Matching r L) (e : End r) : Fin L := ⟨M.pos e, M.bound e⟩

def traceLabels {r L} (M : Matching r L) (p : Fin L) : Fin (r+1) := axis (read M p)

def fiberEnds {r} (a : Fin (r+1)) : List (End r) :=
  Fin.cases (List.ofFn (fun i : Fin 4 => Sum.inl i))
    (fun j => [Sum.inr (j,false), Sum.inr (j,true)]) a

theorem mem_fiberEnds {r} (a : Fin (r+1)) (e : End r) :
    e ∈ fiberEnds a ↔ axis e = a := by
  refine Fin.cases ?_ (fun j => ?_) a
  · cases e with
    | inl i =>
      constructor
      · intro _; rfl
      · intro _; exact List.mem_ofFn.2 ⟨i,rfl⟩
    | inr p =>
      cases p with
      | mk j b =>
        constructor
        · intro hm
          obtain ⟨i, hi⟩ := List.mem_ofFn.1 hm
          cases hi
        · intro he
          exact False.elim (Fin.succ_ne_zero j he)
  · cases e with
    | inl i =>
      constructor
      · intro hm
        rcases List.mem_cons.1 hm with he | he
        · cases he
        · rcases List.mem_cons.1 he with he | he
          · cases he
          · exact False.elim (List.not_mem_nil he)
      · intro he
        exact False.elim (Fin.succ_ne_zero j he.symm)
    | inr p =>
      cases p with
      | mk k b =>
        constructor
        · intro hm
          rcases List.mem_cons.1 hm with he | he
          · exact congrArg Fin.succ (congrArg Prod.fst (Sum.inr.inj he))
          · rcases List.mem_cons.1 he with he | he
            · exact congrArg Fin.succ (congrArg Prod.fst (Sum.inr.inj he))
            · exact False.elim (List.not_mem_nil he)
        · intro he
          have hj : k = j := Fin.succ_inj.1 he
          subst k
          cases b
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ List.mem_cons_self

def expected {r L} (M : Matching r L) (a : Fin (r+1)) : List (Fin L) :=
  (fiberEnds a).map (vertex M)

theorem mem_expected {r L} (M : Matching r L) (a : Fin (r+1)) (p : Fin L) :
    p ∈ expected M a ↔ traceLabels M p = a := by
  constructor
  · intro hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
    simpa only [traceLabels, vertex, read_pos] using (mem_fiberEnds a e).1 he
  · intro hp
    apply List.mem_map.2
    refine ⟨read M p, (mem_fiberEnds a _).2 hp, ?_⟩
    exact Fin.ext (pos_read M p)

theorem distinguished_strict {r L} (M : Matching r L) (i j : Fin 4) (hij : i.val < j.val) :
    M.pos (.inl i) < M.pos (.inl j) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by have := i.isLt; omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by have := j.isLt; omega
  have ho := M.distinguished
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;>
    (try simp only [Fin.val_zero, Fin.val_one] at hij) <;>
    first | exact ho.1 | exact ho.2.1 | exact ho.2.2 | omega

theorem expected_sorted {r L} (M : Matching r L) (a : Fin (r+1)) :
    List.Pairwise (fun p q => p.val < q.val) (expected M a) := by
  refine Fin.cases ?_ (fun j => ?_) a
  · change List.Pairwise (fun p q => p.val < q.val)
      ((List.ofFn (fun i : Fin 4 => Sum.inl i)).map (vertex M))
    rw [List.map_ofFn]
    apply List.pairwise_iff_getElem.2
    intro i j hi hj hij
    simp only [List.getElem_ofFn]
    exact distinguished_strict M ⟨i,by simpa only [List.length_ofFn] using hi⟩
      ⟨j,by simpa only [List.length_ofFn] using hj⟩ hij
  · change List.Pairwise (fun p q => p.val < q.val)
      [vertex M (.inr (j,false)), vertex M (.inr (j,true))]
    exact List.Pairwise.cons
      (fun p hp => (List.mem_singleton.1 hp) ▸ M.rest j)
      (List.Pairwise.cons (fun _ hp => False.elim (List.not_mem_nil hp)) List.Pairwise.nil)

theorem head_le {L} (a : Fin L) (xs : List (Fin L))
    (hs : List.Pairwise (fun p q => p.val < q.val) (a::xs))
    (b : Fin L) (hb : b ∈ a::xs) : a.val ≤ b.val := by
  rcases List.mem_cons.1 hb with he | he
  · exact Nat.le_of_eq (congrArg Fin.val he.symm)
  · exact Nat.le_of_lt ((List.pairwise_cons.1 hs).1 b he)

-- Sorted occurrence inventories are uniquely determined by their members.
theorem sorted_unique {L} (xs ys : List (Fin L))
    (hx : List.Pairwise (fun p q => p.val < q.val) xs)
    (hy : List.Pairwise (fun p q => p.val < q.val) ys)
    (hm : ∀ p, p ∈ xs ↔ p ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b ys => exact False.elim (List.not_mem_nil ((hm b).2 List.mem_cons_self))
  | cons a xs ih =>
    cases ys with
    | nil => exact False.elim (List.not_mem_nil ((hm a).1 List.mem_cons_self))
    | cons b ys =>
      have hab : a = b := Fin.ext (Nat.le_antisymm
        (head_le a xs hx b ((hm b).2 List.mem_cons_self))
        (head_le b ys hy a ((hm a).1 List.mem_cons_self)))
      subst b
      apply congrArg (a :: ·)
      apply ih _ (List.pairwise_cons.1 hx).2 (List.pairwise_cons.1 hy).2
      intro p
      constructor
      · intro hp
        have hn : p ≠ a := by
          intro he
          have hlt := (List.pairwise_cons.1 hx).1 p hp
          exact Nat.lt_irrefl a.val (he ▸ hlt)
        exact (List.mem_cons.1 ((hm p).1 (List.mem_cons_of_mem a hp))).resolve_left hn
      · intro hp
        have hn : p ≠ a := by
          intro he
          have hlt := (List.pairwise_cons.1 hy).1 p hp
          exact Nat.lt_irrefl a.val (he ▸ hlt)
        exact (List.mem_cons.1 ((hm p).2 (List.mem_cons_of_mem a hp))).resolve_left hn

theorem positions_traceLabels {r L} (M : Matching r L) (a : Fin (r+1)) :
    positions (traceLabels M) a = expected M a := by
  apply sorted_unique _ _ (positions_sorted _ _) (expected_sorted M a)
  intro p
  exact (mem_positions _ a p).trans (mem_expected M a p).symm

theorem traceLabels_profile {r L} (M : Matching r L) : Profile (traceLabels M) := by
  constructor
  · rw [positions_traceLabels]
    simp only [expected, fiberEnds, Fin.cases_zero, List.length_map, List.length_ofFn]
  · intro j
    rw [positions_traceLabels]
    rfl

theorem extract_traceLabels_pos {r L} (M : Matching r L) (e : End r) :
    (extract (traceLabels M) (traceLabels_profile M)).pos e = M.pos e := by
  change ((positions (traceLabels M) (axis e))[slot e]'(slot_bound (traceLabels M) (traceLabels_profile M) e)).val = M.pos e
  simp only [positions_traceLabels, expected]
  cases e with
  | inl i =>
    simp only [axis, fiberEnds, Fin.cases_zero, slot, List.getElem_map,
      List.getElem_ofFn, vertex]
  | inr p =>
    cases p with
    | mk j b =>
      cases b <;> simp only [axis, fiberEnds, Fin.cases_succ, slot, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.map_nil, List.getElem_cons_zero, List.getElem_cons_succ, vertex]

theorem matching_ext {r L} (M N : Matching r L) (hp : ∀ e, M.pos e = N.pos e) : M = N := by
  cases M with
  | mk m mi mb mc md mr =>
    cases N with
    | mk n ni nb nc nd nr =>
      have he : m = n := funext hp
      cases he
      rfl

theorem extract_traceLabels {r L} (M : Matching r L) :
    extract (traceLabels M) (traceLabels_profile M) = M :=
  matching_ext _ _ (extract_traceLabels_pos M)

theorem traceLabels_extract {r L} (w : Fin L → Fin (r+1)) (h : Profile w) :
    traceLabels (extract w h) = w := by
  funext p
  exact read_axis w h p

#print axioms matching_ext
#print axioms extract_traceLabels
#print axioms traceLabels_extract
#print axioms mem_fiberEnds
#print axioms mem_expected
#print axioms distinguished_strict
#print axioms expected_sorted
#print axioms head_le
#print axioms sorted_unique
#print axioms positions_traceLabels
#print axioms traceLabels_profile
#print axioms extract_traceLabels_pos
#print axioms mem_positions
#print axioms positions_nodup
#print axioms positions_sorted
#print axioms at_label
#print axioms at_injective
#print axioms at_strict
#print axioms slot_bound
#print axioms event_label
#print axioms event_injective
#print axioms event_cover
#print axioms extract
#print axioms read_axis
#print axioms range_endpoint_label
#print axioms reconstruct_word
#print axioms original_in_fixed_matching_fiber
end ECC.OccurrenceMatching
