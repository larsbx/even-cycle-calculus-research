import ExecutableTrace

/- Exact multiplicity and uniqueness for the literal finite axis-word generator. -/
namespace ECC.WordGenerator
open ECC.ExecutableTrace

def Matches (counts word : List Nat) : Prop :=
  (∀ a, a ∈ word → a < counts.length) ∧
    ∀ a (ha : a < counts.length), word.count a = counts[a]

theorem matches_nil_iff (counts : List Nat) :
    Matches counts [] ↔ counts.all (· == 0) = true := by
  simp only [Matches, List.not_mem_nil, false_implies, implies_true, true_and, List.count_nil]
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact beq_iff_eq.mpr (h i hi).symm
  · intro h a ha
    exact (beq_iff_eq.mp (h counts[a] (List.getElem_mem ha))).symm

theorem matches_cons_iff (counts : List Nat) (a : Nat) (word : List Nat) :
    Matches counts (a :: word) ↔
      a < counts.length ∧ 0 < counts[a]! ∧ Matches (counts.modify a (· - 1)) word := by
  constructor
  · intro h
    have ha := h.1 a List.mem_cons_self
    have hcount := h.2 a ha
    simp only [List.count_cons_self] at hcount
    have hp : 0 < counts[a]! := by rw [getElem!_pos counts a ha]; omega
    refine ⟨ha, hp, ?_, ?_⟩
    · intro b hb
      simpa only [List.length_modify] using h.1 b (List.mem_cons_of_mem a hb)
    · intro b hb
      have hb' : b < counts.length := by simpa only [List.length_modify] using hb
      rw [get_modify_safe (· - 1) counts a b hb']
      by_cases heq : a = b
      · subst b
        simp only [eq_self, ite_true]
        omega
      · rw [ite_eq_right heq]
        simpa only [List.count_cons_of_ne heq] using h.2 b hb'
  · rintro ⟨ha, hp, htail⟩
    refine ⟨?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · simpa only [List.length_modify] using htail.1 b hb
    · intro b hb
      have hc := htail.2 b (by simpa only [List.length_modify] using hb)
      rw [get_modify_safe (· - 1) counts a b hb] at hc
      by_cases heq : a = b
      · subst b
        simp only [eq_self, ite_true] at hc
        simp only [List.count_cons_self]
        rw [getElem!_pos counts a ha] at hp
        omega
      · simpa only [List.count_cons_of_ne heq, ite_eq_right heq] using hc

theorem mem_words_zero (counts word : List Nat) :
    word ∈ ECC.words 0 counts ↔ word = [] ∧ Matches counts [] := by
  rw [matches_nil_iff]
  by_cases h : counts.all (· == 0) = true <;> simp [ECC.words, h]

theorem mem_words_succ (n : Nat) (counts word : List Nat) :
    word ∈ ECC.words (n + 1) counts ↔ ∃ a tail,
      a < counts.length ∧ 0 < counts[a]! ∧
      tail ∈ ECC.words n (counts.modify a (· - 1)) ∧ word = a :: tail := by
  simp only [ECC.words, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨a, ha, hm⟩
    by_cases hz : counts[a]! = 0
    · simp only [beq_iff_eq, hz, ite_true, List.not_mem_nil] at hm
    · have hm' : word ∈ (ECC.words n (counts.modify a (· - 1))).map (a :: ·) := by
        simpa only [beq_iff_eq, ite_eq_right hz] using hm
      obtain ⟨tail, ht, heq⟩ := List.mem_map.mp hm'
      exact ⟨a, tail, ha, Nat.pos_of_ne_zero hz, ht, heq.symm⟩
  · rintro ⟨a, tail, ha, hp, ht, rfl⟩
    refine ⟨a, ha, ?_⟩
    have hz : counts[a]! ≠ 0 := Nat.ne_of_gt hp
    simp only [beq_iff_eq, ite_eq_right hz]
    exact List.mem_map.mpr ⟨tail, ht, rfl⟩

theorem mem_words_iff (n : Nat) (counts word : List Nat) :
    word ∈ ECC.words n counts ↔ word.length = n ∧ Matches counts word := by
  induction n generalizing counts word with
  | zero =>
    rw [mem_words_zero]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, h⟩
    · rintro ⟨hlen, h⟩
      have he := List.eq_nil_of_length_eq_zero hlen
      exact ⟨he, by simpa only [he] using h⟩
  | succ n ih =>
    rw [mem_words_succ]
    constructor
    · rintro ⟨a, tail, ha, hp, ht, rfl⟩
      have h := (ih _ _).mp ht
      exact ⟨by simp only [List.length_cons, h.1], (matches_cons_iff _ _ _).mpr ⟨ha, hp, h.2⟩⟩
    · rintro ⟨hlen, h⟩
      cases word with
      | nil => exact False.elim (Nat.noConfusion hlen)
      | cons a tail =>
        have hs := (matches_cons_iff counts a tail).mp h
        refine ⟨a, tail, hs.1, hs.2.1, (ih _ _).mpr ⟨?_, hs.2.2⟩, rfl⟩
        simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen

theorem range_nodup_safe (q : Nat) : (List.range q).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj heq
  simpa only [List.getElem_range] using heq

theorem prefix_nodup (a : Nat) (ws : List (List Nat)) (h : ws.Nodup) :
    (ws.map (a :: ·)).Nodup :=
  h.map (a :: ·) (fun _ _ hne heq => hne (List.cons.inj heq).2)

def branch (n : Nat) (counts : List Nat) (a : Nat) : List (List Nat) :=
  if counts[a]! == 0 then [] else (ECC.words n (counts.modify a (· - 1))).map (a :: ·)

theorem branch_head (n : Nat) (counts : List Nat) (a : Nat) (word : List Nat)
    (h : word ∈ branch n counts a) : ∃ tail, word = a :: tail := by
  unfold branch at h
  split at h
  · exact False.elim (List.not_mem_nil h)
  · obtain ⟨tail, _, heq⟩ := List.mem_map.mp h
    exact ⟨tail, heq.symm⟩

theorem branches_disjoint (n : Nat) (counts : List Nat) (a b : Nat) (hab : a ≠ b)
    (u v : List Nat) (hu : u ∈ branch n counts a) (hv : v ∈ branch n counts b) : u ≠ v := by
  obtain ⟨ut, rfl⟩ := branch_head n counts a u hu
  obtain ⟨vt, rfl⟩ := branch_head n counts b v hv
  exact fun heq => hab (List.cons.inj heq).1

theorem words_nodup (n : Nat) (counts : List Nat) : (ECC.words n counts).Nodup := by
  induction n generalizing counts with
  | zero =>
    unfold ECC.words
    split <;> simp only [List.nodup_nil, List.nodup_cons, List.not_mem_nil, not_false_eq_true, and_self]
  | succ n ih =>
    change List.Pairwise (· ≠ ·) ((List.range counts.length).flatMap (branch n counts))
    rw [List.pairwise_flatMap]
    constructor
    · intro a _
      unfold branch
      split
      · exact List.Pairwise.nil
      · exact prefix_nodup a _ (ih _)
    · exact (range_nodup_safe counts.length).imp (fun {a b} hab =>
        fun u hu v hv => branches_disjoint n counts a b hab u v hu hv)

theorem accepted_nodup (n : Nat) (counts : List Nat) (accept : List Nat → Bool) :
    ((ECC.words n counts).filter accept).Nodup := (words_nodup n counts).filter accept

theorem mem_accepted_iff (n : Nat) (counts word : List Nat) (accept : List Nat → Bool) :
    word ∈ (ECC.words n counts).filter accept ↔
      word.length = n ∧ Matches counts word ∧ accept word = true := by
  rw [List.mem_filter, mem_words_iff]
  exact and_assoc

def lift {q : Nat} : (word : List Nat) → (∀ a, a ∈ word → a < q) → List (Fin q)
  | [], _ => []
  | a :: tail, h => ⟨a, h a List.mem_cons_self⟩ ::
      lift tail (fun b hb => h b (List.mem_cons_of_mem a hb))

theorem map_lift {q : Nat} (word : List Nat) (h : ∀ a, a ∈ word → a < q) :
    (lift word h).map Fin.val = word := by
  induction word with
  | nil => rfl
  | cons a tail ih =>
    change a :: (lift tail _).map Fin.val = a :: tail
    rw [ih]

theorem steps_eq_raw_count {q : Nat} (word : List (Fin q)) (a : Fin q) :
    ECC.EventShuffle.steps word a = (word.map Fin.val).count a.val := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    by_cases h : b = a
    · subst b
      simp [ECC.EventShuffle.steps, ih]
    · have hv : b.val ≠ a.val := fun heq => h (Fin.ext heq)
      simp [ECC.EventShuffle.steps, h, List.count_cons_of_ne hv, ih]

theorem generated_typed_axes (n : Nat) (counts word : List Nat) (h : word ∈ ECC.words n counts) :
    ∃ typed : List (Fin counts.length), typed.map Fin.val = word ∧
      ∀ a : Fin counts.length, ECC.EventShuffle.steps typed a = counts[a.val] := by
  have hm := ((mem_words_iff n counts word).mp h).2
  refine ⟨lift word hm.1, map_lift word hm.1, ?_⟩
  intro a
  rw [steps_eq_raw_count, map_lift]
  exact hm.2 a.val a.isLt

theorem kernel_membership_iff (counts : List Nat) (patterns : List (List Nat)) (word : List Nat) :
    word ∈ (ECC.words 8 counts).filter (fun w =>
      ECC.distinct (ECC.vertices patterns w (List.replicate patterns.length 0))) ↔
    word.length = 8 ∧ Matches counts word ∧
      ECC.distinct (ECC.vertices patterns word (List.replicate patterns.length 0)) = true :=
  mem_accepted_iff 8 counts word _

theorem kernel_words_nodup (counts : List Nat) (patterns : List (List Nat)) :
    ((ECC.words 8 counts).filter (fun w =>
      ECC.distinct (ECC.vertices patterns w (List.replicate patterns.length 0)))).Nodup :=
  accepted_nodup 8 counts _

#print axioms matches_nil_iff
#print axioms matches_cons_iff
#print axioms mem_words_zero
#print axioms mem_words_succ
#print axioms mem_words_iff
#print axioms range_nodup_safe
#print axioms prefix_nodup
#print axioms branch_head
#print axioms branches_disjoint
#print axioms words_nodup
#print axioms accepted_nodup
#print axioms mem_accepted_iff
#print axioms map_lift
#print axioms steps_eq_raw_count
#print axioms generated_typed_axes
#print axioms kernel_membership_iff
#print axioms kernel_words_nodup

end ECC.WordGenerator
