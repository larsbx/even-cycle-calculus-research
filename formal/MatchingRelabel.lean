import OccurrenceMatching
import FiniteQuotient
import FinitePermutation

namespace ECC.MatchingRelabel
open OccurrenceMatching ResolutionMatching MatchingWord MatchingLabels

-- Equal distinguished four-set and equal complementary endpoint pairs.
def Same {r L} (w v : Fin L → Fin (r+1)) : Prop :=
  (∀ p, w p = 0 ↔ v p = 0) ∧ ∀ p q, w p = w q ↔ v p = v q
instance {r L} (w v : Fin L → Fin (r+1)) : Decidable (Same w v) :=
  inferInstanceAs (Decidable ((∀ p, w p = 0 ↔ v p = 0) ∧ ∀ p q, w p = w q ↔ v p = v q))

theorem same_refl {r L} (w : Fin L → Fin (r+1)) : Same w w := ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩
theorem same_symm {r L} (w v : Fin L → Fin (r+1)) (h : Same w v) : Same v w :=
  ⟨fun p => (h.1 p).symm, fun p q => (h.2 p q).symm⟩
theorem same_trans {r L} (u v w : Fin L → Fin (r+1)) (h : Same u v) (k : Same v w) : Same u w :=
  ⟨fun p => (h.1 p).trans (k.1 p), fun p q => (h.2 p q).trans (k.2 p q)⟩

theorem profile_positive {r L} (w : Fin L → Fin (r+1)) (h : Profile w) (a : Fin (r+1)) :
    0 < (positions w a).length := by
  refine Fin.cases ?_ (fun j => ?_) a
  · rw [h.1]; decide
  · rw [h.2 j]; decide

def first {r L} (w : Fin L → Fin (r+1)) (h : Profile w) (a : Fin (r+1)) : Fin L :=
  occurrence w a 0 (profile_positive w h a)

theorem first_label {r L} (w : Fin L → Fin (r+1)) (h : Profile w) (a : Fin (r+1)) :
    w (first w h a) = a := at_label w a _ _

def rename {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (a : Fin (r+1)) : Fin (r+1) :=
  v (first w h a)

theorem rename_word {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hs : Same w v) (p : Fin L) :
    rename w v h (w p) = v p :=
  (hs.2 (first w h (w p)) p).1 (first_label w h (w p))

theorem rename_zero {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hs : Same w v) :
    rename w v h 0 = 0 := (hs.1 _).1 (first_label w h 0)

theorem rename_injective {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hs : Same w v)
    (a b : Fin (r+1)) (he : rename w v h a = rename w v h b) : a = b := by
  have hw := (hs.2 (first w h a) (first w h b)).2 he
  simpa only [first_label] using hw

theorem rename_surjective {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hv : Profile v)
    (hs : Same w v) (b : Fin (r+1)) : ∃ a, rename w v h a = b := by
  exact ⟨w (first v hv b), (rename_word w v h hs _).trans (first_label v hv b)⟩

def restRename {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (_hs : Same w v) (j : Fin r) : Fin r :=
  ⟨(rename w v h j.succ).val - 1, by
    have hb := (rename w v h j.succ).isLt
    have hj := j.isLt
    omega⟩

theorem restRename_succ {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hs : Same w v) (j : Fin r) :
    (restRename w v h hs j).succ = rename w v h j.succ := by
  have hn : rename w v h j.succ ≠ 0 := by
    intro he
    have hzero := rename_zero w v h hs
    exact Fin.succ_ne_zero j (rename_injective w v h hs _ _ (he.trans hzero.symm))
  have hp : 0 < (rename w v h j.succ).val := by
    have hz : (rename w v h j.succ).val ≠ 0 := fun he => hn (Fin.ext he)
    omega
  apply Fin.ext
  change (rename w v h j.succ).val - 1 + 1 = (rename w v h j.succ).val
  omega

theorem restRename_injective {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hs : Same w v)
    (i j : Fin r) (he : restRename w v h hs i = restRename w v h hs j) : i = j := by
  have hh := congrArg Fin.succ he
  rw [restRename_succ, restRename_succ] at hh
  exact Fin.succ_inj.1 (rename_injective w v h hs _ _ hh)

theorem restRename_surjective {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hv : Profile v)
    (hs : Same w v) (j : Fin r) : ∃ i, restRename w v h hs i = j := by
  obtain ⟨a, ha⟩ := rename_surjective w v h hv hs j.succ
  revert ha
  refine Fin.cases ?_ (fun i => ?_) a
  · intro he
    rw [rename_zero w v h hs] at he
    exact False.elim (Fin.succ_ne_zero j he.symm)
  · intro he
    exact ⟨i, Fin.succ_inj.1 ((restRename_succ w v h hs i).trans he)⟩

def renameLabels {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hs : Same w v) : List Nat :=
  List.ofFn fun j : Fin r => (restRename w v h hs j).val

theorem renameLabels_perm {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hv : Profile v)
    (hs : Same w v) : (renameLabels w v h hs).Perm (List.range r) := by
  have hn : (renameLabels w v h hs).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.2
    intro i j hi hj he
    have hi' : i < r := by simpa only [renameLabels, List.length_ofFn] using hi
    have hj' : j < r := by simpa only [renameLabels, List.length_ofFn] using hj
    have heq : restRename w v h hs ⟨i,hi'⟩ = restRename w v h hs ⟨j,hj'⟩ := by
      apply Fin.ext
      simpa only [renameLabels, List.getElem_ofFn] using he
    exact congrArg Fin.val (restRename_injective w v h hs _ _ heq)
  have hr : (List.range r).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.2
    intro i j hi hj he
    simpa only [List.getElem_range] using he
  apply FinitePermutation.perm_of_same_members _ _ hn hr
  intro b
  rw [List.mem_range]
  constructor
  · intro hb
    obtain ⟨j, hj⟩ := List.mem_ofFn.1 hb
    exact hj ▸ (restRename w v h hs j).isLt
  · intro hb
    obtain ⟨j, hj⟩ := restRename_surjective w v h hv hs ⟨b,hb⟩
    exact List.mem_ofFn.2 ⟨j, congrArg Fin.val hj⟩

theorem same_in_fixed_fiber {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hv : Profile v)
    (hs : Same w v) : (fun p => (v p).val) ∈ words (extract w h) := by
  apply (words_membership _ _).2
  refine ⟨renameLabels w v h hs, renameLabels_perm w v h hv hs, ?_⟩
  funext p
  have ha := read_axis w h p
  have he := rename_word w v h hs p
  rw [← ha] at he
  unfold word
  generalize hr : read (extract w h) p = e at *
  cases e with
  | inl i =>
    have hz : v p = 0 := he.symm.trans (rename_zero w v h hs)
    exact congrArg Fin.val hz.symm
  | inr pair =>
    cases pair with
    | mk j b =>
      have hp : j.val < (renameLabels w v h hs).length := by
        simpa only [renameLabels, List.length_ofFn] using j.isLt
      change (renameLabels w v h hs)[j.val]! + 1 = (v p).val
      rw [getElem!_pos (renameLabels w v h hs) j.val hp]
      simp only [renameLabels, List.getElem_ofFn]
      exact congrArg Fin.val ((restRename_succ w v h hs j).trans he)

theorem endpoint_zero {r} (xs : List Nat) (e : End r) :
    endpointLabel xs e = 0 ↔ axis e = 0 := by
  cases e with
  | inl i => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | inr p =>
    cases p with
    | mk j b =>
      constructor
      · intro he; exact False.elim (Nat.noConfusion he)
      · intro he; exact False.elim (Fin.succ_ne_zero j he)

theorem endpoint_equal {r} (xs : List Nat) (hx : xs.length = r) (hn : xs.Nodup) (e f : End r) :
    endpointLabel xs e = endpointLabel xs f ↔ axis e = axis f := by
  cases e with
  | inl i =>
    cases f with
    | inl j => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | inr p =>
      cases p with
      | mk j b =>
        constructor
        · intro he; exact False.elim (Nat.noConfusion he)
        · intro he; exact False.elim (Fin.succ_ne_zero j he.symm)
  | inr p =>
    cases p with
    | mk i b =>
      cases f with
      | inl j =>
        constructor
        · intro he; exact False.elim (Nat.noConfusion he)
        · intro he; exact False.elim (Fin.succ_ne_zero i he)
      | inr p =>
        cases p with
        | mk j c =>
          have hi : i.val < xs.length := hx ▸ i.isLt
          have hj : j.val < xs.length := hx ▸ j.isLt
          change xs[i.val]! + 1 = xs[j.val]! + 1 ↔ i.succ = j.succ
          rw [getElem!_pos xs i.val hi, getElem!_pos xs j.val hj]
          constructor
          · intro he
            have hv := List.nodup_iff_eq_of_getElem_eq.1 hn i.val j.val hi hj (Nat.add_right_cancel he)
            exact congrArg Fin.succ (Fin.ext hv)
          · intro he
            have hij := Fin.succ_inj.1 he
            subst j
            rfl

theorem fixed_fiber_same {r L} (w v : Fin L → Fin (r+1)) (h : Profile w)
    (hin : (fun p => (v p).val) ∈ words (extract w h)) : Same w v := by
  obtain ⟨xs, hxs, he⟩ := (words_membership _ _).1 hin
  have hx : xs.length = r := hxs.length_eq.trans List.length_range
  have hr : (List.range r).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.2
    intro i j hi hj hh
    simpa only [List.getElem_range] using hh
  have hn : xs.Nodup := hxs.nodup_iff.2 hr
  have hval : ∀ p, endpointLabel xs (read (extract w h) p) = (v p).val := congrFun he
  constructor
  · intro p
    constructor
    · intro hp
      have ha : axis (read (extract w h) p) = 0 := (read_axis w h p).trans hp
      have hz := (endpoint_zero xs _).2 ha
      exact Fin.ext ((hval p).symm.trans hz)
    · intro hp
      have hz : endpointLabel xs (read (extract w h) p) = 0 := (hval p).trans (congrArg Fin.val hp)
      exact (read_axis w h p).symm.trans ((endpoint_zero xs _).1 hz)
  · intro p q
    constructor
    · intro hpq
      have ha := (read_axis w h p).trans (hpq.trans (read_axis w h q).symm)
      have hb := (endpoint_equal xs hx hn _ _).2 ha
      exact Fin.ext ((hval p).symm.trans (hb.trans (hval q)))
    · intro hpq
      have hb : endpointLabel xs (read (extract w h) p) = endpointLabel xs (read (extract w h) q) :=
        (hval p).trans ((congrArg Fin.val hpq).trans (hval q).symm)
      exact (read_axis w h p).symm.trans (((endpoint_equal xs hx hn _ _).1 hb).trans (read_axis w h q))

theorem same_iff_fixed_fiber {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hv : Profile v) :
    Same w v ↔ (fun p => (v p).val) ∈ words (extract w h) :=
  ⟨same_in_fixed_fiber w v h hv, fixed_fiber_same w v h⟩

#print axioms endpoint_zero
#print axioms endpoint_equal
#print axioms fixed_fiber_same
#print axioms same_iff_fixed_fiber
#print axioms renameLabels_perm
#print axioms same_in_fixed_fiber
#print axioms same_refl
#print axioms same_symm
#print axioms same_trans
#print axioms profile_positive
#print axioms first_label
#print axioms rename_word
#print axioms rename_zero
#print axioms rename_injective
#print axioms rename_surjective
#print axioms restRename_succ
#print axioms restRename_injective
#print axioms restRename_surjective
end ECC.MatchingRelabel
