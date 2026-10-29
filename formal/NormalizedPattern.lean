import RankCompression
import PatternGenerator

/- Canonical ordinal words belong to the literal cyclic-pattern inventory. -/
namespace ECC.NormalizedPattern
open ECC.RankCompression ECC.PatternGenerator

def word {m N : Nat} (v : Fin (m + 1) → Fin N) : List Nat :=
  List.ofFn fun t => (ECC.RankCompression.encode v t).val

def tailWord {m N : Nat} (v : Fin (m + 1) → Fin N) : List Nat :=
  List.ofFn fun t : Fin m => (ECC.RankCompression.encode v t.succ).val

def Proper {m N : Nat} (v : Fin (m + 1) → Fin N) : Prop :=
  (∀ t : Fin m, v t.castSucc ≠ v t.succ) ∧ v (Fin.last m) ≠ v 0

theorem word_length {m N : Nat} (v : Fin (m + 1) → Fin N) : (word v).length = m + 1 :=
  List.length_ofFn

theorem tail_length {m N : Nat} (v : Fin (m + 1) → Fin N) : (tailWord v).length = m :=
  List.length_ofFn

theorem word_split {m N : Nat} (v : Fin (m + 1) → Fin N) : word v = 0 :: tailWord v := by
  unfold word tailWord
  rw [List.ofFn_succ, encode_zero]

theorem prefix_labels_eq_take {m N : Nat} (v : Fin (m + 1) → Fin N) (t : Fin (m + 1)) :
    prefixLabels v t = (word v).take t.val := by
  apply List.ext_getElem
  · simp [prefixLabels, word, Nat.min_eq_left (Nat.le_of_lt t.isLt)]
  · intro i hi hj
    simp only [prefixLabels, List.getElem_map, List.finRange, List.getElem_ofFn,
      List.getElem_take, word]

theorem word_take_last {m N : Nat} (v : Fin (m + 1) → Fin N) (i : Nat) (hi : i < m + 1) :
    ((word v).take (i + 1)).getLast! = (encode v ⟨i, hi⟩).val := by
  have hlen : ((word v).take (i + 1)).length = i + 1 :=
    List.length_take_of_le (by rw [word_length]; omega)
  rw [List.getLast!_eq_getElem!, hlen, Nat.add_sub_cancel]
  rw [getElem!_pos _ i (by rw [hlen]; omega)]
  simp only [List.getElem_take, word, List.getElem_ofFn]

theorem word_last {m N : Nat} (v : Fin (m + 1) → Fin N) :
    (word v).getLast! = (encode v (Fin.last m)).val := by
  rw [List.getLast!_eq_getElem!, word_length, Nat.add_sub_cancel]
  rw [getElem!_pos _ m (by rw [word_length]; omega)]
  simp only [word, List.getElem_ofFn]
  rfl

theorem initial_prefix {m N : Nat} (v : Fin (m + 1) → Fin N) (i : Nat) :
    [0] ++ (tailWord v).take i = (word v).take (i + 1) := by
  rw [word_split]
  rfl

theorem normalized_extension {m N : Nat} (v : Fin (m + 1) → Fin N)
    (hadj : ∀ t : Fin m, v t.castSucc ≠ v t.succ) : Extension [0] (tailWord v) := by
  intro i hi
  have him : i < m := by rwa [tail_length] at hi
  let t : Fin (m + 1) := ⟨i + 1, by omega⟩
  have hvalue : (tailWord v)[i] = (encode v t).val := by
    simp only [tailWord, List.getElem_ofFn]
    rfl
  have hbound := append_bound v t
  rw [prefix_labels_eq_take] at hbound
  have hpre : [0] ++ (tailWord v).take i = (word v).take t.val := initial_prefix v i
  refine ⟨?_, ?_⟩
  · rw [hvalue, hpre]
    omega
  · rw [hvalue, initial_prefix, word_take_last v i (by omega)]
    intro heq
    have same : encode v t = encode v (⟨i, by omega⟩ : Fin (m + 1)) := Fin.ext heq
    have original := (encode_eq_iff v _ _).mp same
    exact hadj ⟨i, him⟩ original.symm

theorem normalized_closing {m N : Nat} (v : Fin (m + 1) → Fin N)
    (hclose : v (Fin.last m) ≠ v 0) : (word v).getLast! ≠ 0 := by
  rw [word_last]
  intro heq
  have hs : encode v (Fin.last m) = encode v 0 := Fin.ext (heq.trans (encode_zero v).symm)
  exact hclose ((encode_eq_iff v _ _).mp hs)

theorem normalized_cyclic {m N : Nat} (v : Fin (m + 1) → Fin N) (h : Proper v) :
    CyclicPattern (word v) :=
  ⟨tailWord v, word_split v, normalized_extension v h.1, normalized_closing v h.2⟩

theorem normalized_mem_patterns {m N : Nat} (v : Fin (m + 1) → Fin N) (h : Proper v) :
    word v ∈ ECC.patterns (m + 1) :=
  (mem_patterns_iff (m + 1) (word v)).mpr ⟨word_length v, normalized_cyclic v h⟩

theorem normalized_occurs_once {m N : Nat} (v : Fin (m + 1) → Fin N) (h : Proper v) :
    (ECC.patterns (m + 1)).count (word v) = 1 :=
  (patterns_nodup (m + 1)).count_of_mem (normalized_mem_patterns v h)

theorem proper_of_normalized_cyclic {m N : Nat} (v : Fin (m + 1) → Fin N)
    (h : CyclicPattern (word v)) : Proper v := by
  obtain ⟨tail, hw, hext, hc⟩ := h
  have ht : tail = tailWord v := (List.cons.inj (hw.symm.trans (word_split v))).2
  subst tail
  constructor
  · intro t heq
    have hp := hext t.val (by rw [tail_length]; exact t.isLt)
    have hcur : (tailWord v)[t.val]'(by rw [tail_length]; exact t.isLt) = (encode v t.succ).val := by
      simp only [tailWord, List.getElem_ofFn]
    have hprev : ([0] ++ (tailWord v).take t.val).getLast! = (encode v t.castSucc).val := by
      rw [initial_prefix, word_take_last v t.val (by omega)]
      rfl
    rw [hcur, hprev] at hp
    exact hp.2 (congrArg Fin.val ((encode_eq_iff v _ _).mpr heq)).symm
  · intro heq
    rw [word_last] at hc
    have hv := congrArg Fin.val ((encode_eq_iff v _ _).mpr heq)
    exact hc (hv.trans (encode_zero v))

theorem normalized_mem_iff_proper {m N : Nat} (v : Fin (m + 1) → Fin N) :
    word v ∈ ECC.patterns (m + 1) ↔ Proper v := by
  constructor
  · intro h
    exact proper_of_normalized_cyclic v ((mem_patterns_iff _ _).mp h).2
  · exact normalized_mem_patterns v

theorem positions_same_equality {m N M : Nat} (v : Fin (m + 1) → Fin N)
    (w : Fin (m + 1) → Fin M) (heq : ∀ s t, v s = v t ↔ w s = w t) :
    positions v = positions w := by
  unfold positions
  apply congrArg (fun p : Fin (m + 1) → Bool => (List.finRange (m + 1)).filter p)
  funext t
  rw [ECC.CanonicalTrace.first_equality_relation v w heq t]

theorem word_eq_of_equality {m N M : Nat} (v : Fin (m + 1) → Fin N)
    (w : Fin (m + 1) → Fin M) (heq : ∀ s t, v s = v t ↔ w s = w t) : word v = word w := by
  unfold word
  apply congrArg List.ofFn
  funext t
  change (positions v).idxOf (ECC.CanonicalTrace.first v t) =
    (positions w).idxOf (ECC.CanonicalTrace.first w t)
  rw [positions_same_equality v w heq, ECC.CanonicalTrace.first_equality_relation v w heq t]

theorem word_lookup_eq_iff {m N : Nat} (v : Fin (m + 1) → Fin N) (s t : Fin (m + 1)) :
    (word v)[s.val]'(by rw [word_length]; exact s.isLt) =
      (word v)[t.val]'(by rw [word_length]; exact t.isLt) ↔ v s = v t := by
  simp only [word, List.getElem_ofFn]
  constructor
  · exact fun h => (encode_eq_iff v s t).mp (Fin.ext h)
  · exact fun h => congrArg Fin.val ((encode_eq_iff v s t).mpr h)

theorem word_eq_iff_equality {m N M : Nat} (v : Fin (m + 1) → Fin N)
    (w : Fin (m + 1) → Fin M) : word v = word w ↔ ∀ s t, v s = v t ↔ w s = w t := by
  constructor
  · intro h s t
    have hs : (word v)[s.val]'(by rw [word_length]; exact s.isLt) =
        (word w)[s.val]'(by rw [word_length]; exact s.isLt) := List.getElem_of_eq h _
    have ht : (word v)[t.val]'(by rw [word_length]; exact t.isLt) =
        (word w)[t.val]'(by rw [word_length]; exact t.isLt) := List.getElem_of_eq h _
    rw [← word_lookup_eq_iff v s t, ← word_lookup_eq_iff w s t, hs, ht]
  · exact word_eq_of_equality v w

theorem assignment_unique {m N : Nat} (v : Fin (m + 1) → Fin N)
    (g : Fin (positions v).length → Fin N) (hg : ∀ t, g (encode v t) = v t) : g = decode v := by
  funext label
  obtain ⟨t, ht⟩ := encode_surjective v label
  rw [← ht, hg, decode_encode]

theorem canonical_factorization {m N : Nat} (v : Fin (m + 1) → Fin N) (h : Proper v) :
    ∃ (r : Nat) (p : Fin (m + 1) → Fin r) (f : Fin r → Fin N),
      (List.ofFn fun t => (p t).val) ∈ ECC.patterns (m + 1) ∧
      (∀ t, f (p t) = v t) ∧ (∀ i j, f i = f j → i = j) ∧
      (∀ label, ∃ t, p t = label) ∧
      (∀ g : Fin r → Fin N, (∀ t, g (p t) = v t) → g = f) :=
  ⟨(positions v).length, encode v, decode v, normalized_mem_patterns v h,
    decode_encode v, decode_injective v, encode_surjective v, assignment_unique v⟩

def SelectedStep {m N : Nat} (v : Fin (m + 1) → Fin N)
    (i j : Fin (positions v).length) : Prop :=
  ∃ t, encode v t = i ∧
    encode v (ECC.CollisionBridge.Next (Nat.zero_lt_succ m) t) = j

theorem selected_step_preserved {m N : Nat} (v : Fin (m + 1) → Fin N)
    (edge : Fin N → Fin N → Prop)
    (hwalk : ∀ t, edge (v t) (v (ECC.CollisionBridge.Next (Nat.zero_lt_succ m) t)))
    (i j : Fin (positions v).length) (hstep : SelectedStep v i j) :
    edge (decode v i) (decode v j) := by
  obtain ⟨t, rfl, rfl⟩ := hstep
  simpa only [decode_encode] using hwalk t

theorem selected_loopless {m N : Nat} (v : Fin (m + 1) → Fin N)
    (edge : Fin N → Fin N → Prop) (hloopless : ∀ x, ¬ edge x x)
    (hwalk : ∀ t, edge (v t) (v (ECC.CollisionBridge.Next (Nat.zero_lt_succ m) t))) :
    ∀ label, ¬ SelectedStep v label label := by
  intro label hstep
  exact hloopless _ (selected_step_preserved v edge hwalk label label hstep)

#print axioms word_length
#print axioms tail_length
#print axioms word_split
#print axioms prefix_labels_eq_take
#print axioms word_take_last
#print axioms word_last
#print axioms initial_prefix
#print axioms normalized_extension
#print axioms normalized_closing
#print axioms normalized_cyclic
#print axioms normalized_mem_patterns
#print axioms normalized_occurs_once
#print axioms proper_of_normalized_cyclic
#print axioms normalized_mem_iff_proper
#print axioms positions_same_equality
#print axioms word_eq_of_equality
#print axioms word_lookup_eq_iff
#print axioms word_eq_iff_equality
#print axioms assignment_unique
#print axioms canonical_factorization
#print axioms selected_step_preserved
#print axioms selected_loopless

end ECC.NormalizedPattern
