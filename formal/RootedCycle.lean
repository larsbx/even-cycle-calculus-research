import CollisionBridge

/- Distinct rooted directed representations of one finite injective trace.
   This file does not assert a cardinality theorem for an arbitrary graph's
   collection of ordinary cycles or classify the projection motifs. -/
namespace ECC.RootedCycle
open ECC.CollisionBridge

def forward {m : Nat} (r t : Fin m) : Fin m :=
  ⟨if r.val + t.val < m then r.val + t.val else r.val + t.val - m, by
    split <;> omega⟩

def backward {m : Nat} (r t : Fin m) : Fin m :=
  ⟨if t.val ≤ r.val then r.val - t.val else m + r.val - t.val, by
    split <;> omega⟩

def index {m : Nat} (p : Fin m × Bool) (t : Fin m) : Fin m :=
  if p.2 then forward p.1 t else backward p.1 t

def representation {m N : Nat} (v : Fin m → Fin N)
    (p : Fin m × Bool) : Fin m → Fin N := fun t => v (index p t)

theorem forward_zero {m : Nat} (hm : 0 < m) (r : Fin m) :
    forward r ⟨0, hm⟩ = r := by
  apply Fin.ext
  simp only [forward, Nat.add_zero, r.isLt, ↓reduceIte]

theorem backward_zero {m : Nat} (hm : 0 < m) (r : Fin m) :
    backward r ⟨0, hm⟩ = r := by
  apply Fin.ext
  simp only [backward, Nat.zero_le, ↓reduceIte, Nat.sub_zero]

theorem index_zero {m : Nat} (hm : 0 < m) (p : Fin m × Bool) :
    index p ⟨0, hm⟩ = p.1 := by
  simp only [index]
  split
  · exact forward_zero hm p.1
  · exact backward_zero hm p.1

theorem forward_injective {m : Nat} (r s t : Fin m)
    (h : forward r s = forward r t) : s = t := by
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [forward] at he
  split at he <;> split at he <;> omega

theorem backward_injective {m : Nat} (r s t : Fin m)
    (h : backward r s = backward r t) : s = t := by
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [backward] at he
  split at he <;> split at he <;> omega

theorem index_injective {m : Nat} (p : Fin m × Bool) (s t : Fin m)
    (h : index p s = index p t) : s = t := by
  unfold index at h
  split at h
  · exact forward_injective p.1 s t h
  · exact backward_injective p.1 s t h

theorem directions_distinct {m : Nat} (hm : 3 ≤ m) (r : Fin m) :
    forward r ⟨1, by omega⟩ ≠ backward r ⟨1, by omega⟩ := by
  intro h
  have he := congrArg Fin.val h
  simp only [forward, backward] at he
  split at he <;> split at he <;> omega

theorem next_val {m : Nat} (hm : 0 < m) (t : Fin m) :
    (Next hm t).val = if t.val + 1 < m then t.val + 1 else 0 := by
  by_cases ht : t.val + 1 < m
  · simp only [Next, ht, ↓reduceIte, Nat.mod_eq_of_lt ht]
  · have he : t.val + 1 = m := by omega
    simp only [Next, he, Nat.mod_self, Nat.lt_irrefl, ↓reduceIte]

theorem forward_next {m : Nat} (hm : 0 < m) (r t : Fin m) :
    forward r (Next hm t) = Next hm (forward r t) := by
  apply Fin.ext
  change (if r.val + (Next hm t).val < m then r.val + (Next hm t).val
    else r.val + (Next hm t).val - m) = (Next hm (forward r t)).val
  rw [next_val hm t, next_val hm (forward r t)]
  simp only [forward]
  repeat' split
  all_goals omega

theorem backward_next {m : Nat} (hm : 0 < m) (r t : Fin m) :
    backward r t = Next hm (backward r (Next hm t)) := by
  apply Fin.ext
  change (if t.val ≤ r.val then r.val - t.val else m + r.val - t.val) =
    (Next hm (backward r (Next hm t))).val
  rw [next_val hm (backward r (Next hm t))]
  simp only [backward]
  simp only [next_val hm t]
  repeat' split
  all_goals omega

theorem representation_edges {m N : Nat} (hm : 0 < m)
    (adj : Fin N → Fin N → Prop) (hsym : ∀ x y, adj x y → adj y x)
    (v : Fin m → Fin N) (he : ∀ t, adj (v t) (v (Next hm t)))
    (p : Fin m × Bool) :
    ∀ t, adj (representation v p t) (representation v p (Next hm t)) := by
  intro t
  unfold representation index
  split
  · simpa only [forward_next hm] using he (forward p.1 t)
  · have h := hsym _ _ (he (backward p.1 (Next hm t)))
    simpa only [← backward_next hm] using h

theorem representation_injective {m N : Nat} (v : Fin m → Fin N)
    (hv : ∀ s t, v s = v t → s = t) (p : Fin m × Bool) :
    ∀ s t, representation v p s = representation v p t → s = t := by
  intro s t h
  exact index_injective p s t (hv _ _ h)

theorem representation_parameters_unique {m N : Nat} (hm : 3 ≤ m)
    (v : Fin m → Fin N) (hv : ∀ s t, v s = v t → s = t)
    (p q : Fin m × Bool) (h : representation v p = representation v q) : p = q := by
  have hr : p.1 = q.1 := by
    have he := hv _ _ (congrFun h ⟨0, by omega⟩)
    simpa only [representation, index_zero] using he
  rcases p with ⟨r, b⟩
  rcases q with ⟨s, c⟩
  simp only at hr
  subst s
  cases b <;> cases c
  · rfl
  · have he := hv _ _ (congrFun h ⟨1, by omega⟩)
    exact False.elim (directions_distinct hm r he.symm)
  · have he := hv _ _ (congrFun h ⟨1, by omega⟩)
    exact False.elim (directions_distinct hm r he)
  · rfl

def parameter {m : Nat} (i : Fin (2*m)) : Fin m × Bool :=
  if hi : i.val < m then (⟨i.val, hi⟩, false)
  else (⟨i.val-m, by omega⟩, true)

theorem parameter_injective {m : Nat} (i j : Fin (2*m))
    (h : parameter i = parameter j) : i = j := by
  apply Fin.ext
  unfold parameter at h
  split at h <;> split at h
  · exact congrArg (fun p : Fin m × Bool => p.1.val) h
  · exact False.elim (Bool.noConfusion (congrArg Prod.snd h))
  · exact False.elim (Bool.noConfusion (congrArg Prod.snd h))
  · have he := congrArg (fun p : Fin m × Bool => p.1.val) h
    change i.val - m = j.val - m at he
    omega

theorem parameter_surjective {m : Nat} (p : Fin m × Bool) :
    ∃ i : Fin (2*m), parameter i = p := by
  rcases p with ⟨r, b⟩
  cases b
  · refine ⟨⟨r.val, by omega⟩, ?_⟩
    simp only [parameter, r.isLt, ↓reduceDIte]
  · refine ⟨⟨m+r.val, by omega⟩, ?_⟩
    have hn : ¬ m + r.val < m := by omega
    simp only [parameter, hn, ↓reduceDIte]
    apply Prod.ext
    · apply Fin.ext
      change m + r.val - m = r.val
      omega
    · rfl

def representations {m N : Nat} (v : Fin m → Fin N) : List (Fin m → Fin N) :=
  List.ofFn fun i : Fin (2*m) => representation v (parameter i)

theorem representations_length {m N : Nat} (v : Fin m → Fin N) :
    (representations v).length = 2*m := List.length_ofFn

theorem representations_nodup {m N : Nat} (hm : 3 ≤ m)
    (v : Fin m → Fin N) (hv : ∀ s t, v s = v t → s = t) :
    (representations v).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.2
  intro i j hi hj he
  have hi' : i < 2*m := by simpa only [representations_length] using hi
  have hj' : j < 2*m := by simpa only [representations_length] using hj
  have hr : representation v (parameter ⟨i, hi'⟩) =
      representation v (parameter ⟨j, hj'⟩) := by
    simpa only [representations, List.getElem_ofFn] using he
  exact congrArg Fin.val (parameter_injective _ _
    (representation_parameters_unique hm v hv _ _ hr))

theorem mem_representations_iff {m N : Nat} (v : Fin m → Fin N)
    (w : Fin m → Fin N) :
    w ∈ representations v ↔ ∃ p : Fin m × Bool, w = representation v p := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 h
    exact ⟨parameter i, hi.symm⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨i, hi⟩ := parameter_surjective p
    apply List.mem_ofFn.2
    exact ⟨i, congrArg (representation v) hi⟩

theorem eight_ten_representation_counts :
    (representations (fun t : Fin 8 => t)).Nodup ∧
    (representations (fun t : Fin 8 => t)).length = 16 ∧
    (representations (fun t : Fin 10 => t)).Nodup ∧
    (representations (fun t : Fin 10 => t)).length = 20 := by
  exact ⟨representations_nodup (by decide) _ (fun _ _ h => h),
    representations_length _, representations_nodup (by decide) _ (fun _ _ h => h),
    representations_length _⟩

theorem length_two_direction_control :
    ∀ t : Fin 2, representation (fun i : Fin 2 => i) (0, false) t =
      representation (fun i : Fin 2 => i) (0, true) t := by decide

def repeatedTrace (t : Fin 4) : Fin 2 := ⟨t.val % 2, Nat.mod_lt _ (by decide)⟩

theorem repeated_trace_rotation_control :
    ∀ t : Fin 4, representation repeatedTrace (0, true) t =
      representation repeatedTrace (2, true) t := by decide

theorem symmetry_control :
    let adj := fun x y : Fin 3 => y.val = (x.val + 1) % 3
    (∀ t : Fin 3, adj t (Next (by decide) t)) ∧
    ¬ adj (representation (fun i : Fin 3 => i) (0, false) 0)
      (representation (fun i : Fin 3 => i) (0, false) 1) := by decide

#print axioms forward_zero
#print axioms backward_zero
#print axioms index_zero
#print axioms forward_injective
#print axioms backward_injective
#print axioms index_injective
#print axioms directions_distinct
#print axioms next_val
#print axioms forward_next
#print axioms backward_next
#print axioms representation_edges
#print axioms representation_injective
#print axioms representation_parameters_unique
#print axioms parameter_injective
#print axioms parameter_surjective
#print axioms representations_length
#print axioms representations_nodup
#print axioms mem_representations_iff
#print axioms eight_ten_representation_counts
#print axioms length_two_direction_control
#print axioms repeated_trace_rotation_control
#print axioms symmetry_control

end ECC.RootedCycle
