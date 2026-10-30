import RootedCycle
import MatchingLabels
import FiniteCardinality
import FiniteQuotient
import MotifTransport

namespace ECC.GlobalCycleCount
open RootedCycle MatchingLabels

instance traceDecidableEq {L N} : DecidableEq (Fin L → Fin N) := fun f g =>
  decidable_of_iff (∀ t, f t = g t) ⟨fun h => funext h, fun h t => congrFun h t⟩

-- The group action is proved before using representatives of ordinary cycles.
theorem index_comp {m : Nat} (p q : Fin m × Bool) (t : Fin m) :
    index p (index q t) = index (index p q.1, p.2 == q.2) t := by
  rcases p with ⟨r, b⟩
  rcases q with ⟨s, c⟩
  cases b <;> cases c
  all_goals
    simp only [index]
    dsimp
    apply Fin.ext
    simp only [forward, backward]
    repeat' split
    all_goals try simp only [Fin.val_mk] at *
    all_goals omega

theorem representation_comp {m N} (v : Fin m → Fin N) (p q) :
    representation (representation v p) q =
      representation v (index p q.1, p.2 == q.2) := by
  funext t
  exact congrArg v (index_comp p q t)

theorem index_surjective {m : Nat} (p : Fin m × Bool) (t : Fin m) :
    ∃ s, index p s = t := by
  rcases p with ⟨r, b⟩
  cases b
  · refine ⟨backward r t, ?_⟩
    apply Fin.ext
    simp only [index, Bool.false_eq_true, ↓reduceIte, backward]
    repeat' split
    all_goals try simp only [Fin.val_mk] at *
    all_goals omega
  · refine ⟨backward t r, ?_⟩
    apply Fin.ext
    simp only [index, ↓reduceIte, forward, backward]
    repeat' split
    all_goals try simp only [Fin.val_mk] at *
    all_goals omega

def Orbit {L N} (u v : Fin L → Fin N) : Prop := ∃ p, v = representation u p

instance orbitDecidable {L N} (u v : Fin L → Fin N) : Decidable (Orbit u v) :=
  decidable_of_iff (v ∈ representations u) (mem_representations_iff u v)

theorem representation_identity {L N} (v : Fin L → Fin N) (hL : 0 < L) :
    representation v (⟨0, hL⟩, true) = v := by
  funext t
  have hi : forward ⟨0, hL⟩ t = t := by
    apply Fin.ext
    simp only [forward, Nat.zero_add, t.isLt, ↓reduceIte]
  exact congrArg v hi

theorem orbit_refl {L N} (hL : 0 < L) (v : Fin L → Fin N) : Orbit v v :=
  ⟨(⟨0, hL⟩, true), (representation_identity v hL).symm⟩

theorem orbit_trans {L N} (u v w : Fin L → Fin N) : Orbit u v → Orbit v w → Orbit u w := by
  rintro ⟨p, rfl⟩ ⟨q, rfl⟩
  exact ⟨(index p q.1, p.2 == q.2), representation_comp u p q⟩

theorem orbit_symm {L N} (hL : 0 < L) (u v : Fin L → Fin N) : Orbit u v → Orbit v u := by
  rintro ⟨p, rfl⟩
  obtain ⟨s, hs⟩ := index_surjective p ⟨0, hL⟩
  refine ⟨(s, p.2), ?_⟩
  rw [representation_comp, hs]
  have hb : (p.2 == p.2) = true := by cases p.2 <;> rfl
  rw [hb, representation_identity u hL]

-- Any complete, disjoint finite inventory of ordinary-cycle representatives
-- yields a global 2L quotient. Coverage and disjointness are explicit fields,
-- so this theorem cannot certify an incomplete sector inventory by itself.
structure Inventory (L N : Nat) where
  representatives : List (Fin L → Fin N)
  rooted : List (Fin L → Fin N)
  reps_nodup : representatives.Nodup
  rooted_nodup : rooted.Nodup
  simple : ∀ v, v ∈ representatives → ∀ s t, v s = v t → s = t
  complete : ∀ w, w ∈ rooted ↔ ∃ v, v ∈ representatives ∧ w ∈ representations v
  disjoint : ∀ u, u ∈ representatives → ∀ v, v ∈ representatives →
    u ≠ v → ∀ w, w ∈ representations u → w ∉ representations v

theorem global_rooted_count {L N} (hL : 3 ≤ L) (I : Inventory L N) :
    I.rooted.length = (2*L) * I.representatives.length := by
  have hn : (I.representatives.flatMap representations).Nodup := by
    change List.Pairwise (· ≠ ·) (I.representatives.flatMap representations)
    rw [List.pairwise_flatMap]
    constructor
    · intro v hv
      exact representations_nodup hL v (I.simple v hv)
    · apply List.Pairwise.imp_of_mem (p := I.reps_nodup)
      intro u v hu hv hne w hw z hz he
      subst z
      exact I.disjoint u hu v hv hne w hw hz
  have hp : I.rooted.length = (I.representatives.flatMap representations).length := by
    apply FiniteCardinality.same_members_length _ _ I.rooted_nodup hn
    intro w
    simpa only [List.mem_flatMap] using I.complete w
  calc
    I.rooted.length = (I.representatives.flatMap representations).length := hp
    _ = I.representatives.length * (2*L) :=
      flatMap_constant_length _ _ _ (fun _ _ => representations_length _)
    _ = (2*L) * I.representatives.length := Nat.mul_comm _ _

theorem ordinary_cycle_quotient {L N} (hL : 3 ≤ L) (I : Inventory L N) :
    I.rooted.length / (2*L) = I.representatives.length := by
  rw [global_rooted_count hL I, Nat.mul_comm]
  exact Nat.mul_div_cancel _ (by omega)

-- Every finite orbit-closed inventory now constructs its own transversal;
-- no representative coverage/disjointness hypotheses remain in this interface.
def fromRooted {L N} (hL : 3 ≤ L) (xs : List (Fin L → Fin N))
    (hn : xs.Nodup)
    (hs : ∀ v, v ∈ xs → ∀ s t, v s = v t → s = t)
    (hc : ∀ v, v ∈ xs → ∀ w, Orbit v w → w ∈ xs) : Inventory L N where
  representatives := FiniteQuotient.select Orbit xs.length xs
  rooted := xs
  reps_nodup := FiniteQuotient.select_nodup Orbit (orbit_refl (by omega))
    (orbit_symm (by omega)) _ _
  rooted_nodup := hn
  simple := fun v hv => hs v (FiniteQuotient.select_subset Orbit _ _ _ hv)
  complete := by
    intro w
    constructor
    · intro hw
      obtain ⟨v, hv, hvw⟩ := FiniteQuotient.select_covers Orbit (orbit_refl (by omega))
        orbit_trans xs.length xs (Nat.le_refl _) w hw
      exact ⟨v, hv, (mem_representations_iff v w).2 hvw⟩
    · rintro ⟨v, hv, hw⟩
      exact hc v (FiniteQuotient.select_subset Orbit _ _ _ hv) w
        ((mem_representations_iff v w).1 hw)
  disjoint := by
    intro u hu v hv hne w hwu hwv
    have hou := (mem_representations_iff u w).1 hwu
    have hov := (mem_representations_iff v w).1 hwv
    have huv := orbit_trans u w v hou (orbit_symm (by omega) v w hov)
    exact hne (FiniteQuotient.select_unique Orbit (orbit_symm (by omega)) _ _ u v hu hv huv)

theorem global_ordinary_count {L N} (hL : 3 ≤ L) (xs : List (Fin L → Fin N))
    (hn : xs.Nodup)
    (hs : ∀ v, v ∈ xs → ∀ s t, v s = v t → s = t)
    (hc : ∀ v, v ∈ xs → ∀ w, Orbit v w → w ∈ xs) :
    xs.length = (2*L) * (FiniteQuotient.select Orbit xs.length xs).length :=
  global_rooted_count hL (fromRooted hL xs hn hs hc)

def GraphTrace {L N} (hL : 0 < L) (edge : Fin N → Fin N → Bool)
    (v : Fin L → Fin N) : Prop :=
  (∀ s t, v s = v t → s = t) ∧
    ∀ t, edge (v t) (v (ECC.CollisionBridge.Next hL t)) = true

instance {L N} (hL : 0 < L) (edge : Fin N → Fin N → Bool) (v : Fin L → Fin N) :
    Decidable (GraphTrace hL edge v) :=
  inferInstanceAs (Decidable ((∀ s t, v s = v t → s = t) ∧
    ∀ t, edge (v t) (v (ECC.CollisionBridge.Next hL t)) = true))

def graphRooted {L N} (hL : 0 < L) (edge : Fin N → Fin N → Bool) :
    List (Fin L → Fin N) :=
  (MotifTransport.maps L N).filter fun v => decide (GraphTrace hL edge v)

theorem graph_rooted_membership {L N} (hL : 0 < L) (edge : Fin N → Fin N → Bool) (v) :
    v ∈ graphRooted hL edge ↔ GraphTrace hL edge v := by
  simp only [graphRooted, List.mem_filter, decide_eq_true_eq, MotifTransport.mem_maps, true_and]

def graphInventory {L N} (hL : 3 ≤ L) (edge : Fin N → Fin N → Bool)
    (hsym : ∀ x y, edge x y = true → edge y x = true) : Inventory L N :=
  fromRooted hL (graphRooted (by omega) edge)
    ((MotifTransport.maps_nodup L N).filter _)
    (fun v hv => ((graph_rooted_membership _ edge v).1 hv).1)
    (by
      intro v hv w hw
      have hgraph := (graph_rooted_membership _ edge v).1 hv
      obtain ⟨p, rfl⟩ := hw
      apply (graph_rooted_membership _ edge _).2
      exact ⟨representation_injective v hgraph.1 p,
        representation_edges _ (fun x y => edge x y = true) hsym v hgraph.2 p⟩)

-- A genuine all-graph quotient, with a fully enumerated finite rooted inventory
-- and a deterministic transversal. No supplied class inventory is assumed.
theorem graph_ordinary_count {L N} (hL : 3 ≤ L) (edge : Fin N → Fin N → Bool)
    (hsym : ∀ x y, edge x y = true → edge y x = true) :
    (graphRooted (L := L) (by omega) edge).length =
      (2*L) * (graphInventory hL edge hsym).representatives.length :=
  global_rooted_count hL (graphInventory hL edge hsym)

#print axioms graph_rooted_membership
#print axioms graphInventory
#print axioms graph_ordinary_count
#print axioms representation_identity
#print axioms orbit_refl
#print axioms orbit_trans
#print axioms orbit_symm
#print axioms fromRooted
#print axioms global_ordinary_count
#print axioms index_comp
#print axioms representation_comp
#print axioms index_surjective
#print axioms global_rooted_count
#print axioms ordinary_cycle_quotient
end ECC.GlobalCycleCount
