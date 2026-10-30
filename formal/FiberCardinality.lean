import MatchingLabels
import MotifTransport

namespace ECC.FiberCardinality
open MatchingLabels MotifTransport

-- Each coordinate has its own finite assignment type; this includes inactive
-- one-label coordinates and nonuniform finite host vertex sets.
def choices : {q : Nat} → {V : Fin q → Type} →
    ((a : Fin q) → List (V a)) → List ((a : Fin q) → V a)
  | 0, _, _ => [fun a => Fin.elim0 a]
  | _+1, _, xs => (xs 0).flatMap fun x =>
      (choices (fun a => xs a.succ)).map (Fin.cases x)

def size : {q : Nat} → (Fin q → Nat) → Nat
  | 0, _ => 1
  | _+1, n => n 0 * size (fun a => n a.succ)

theorem choices_length {q} {V : Fin q → Type} (xs : (a : Fin q) → List (V a)) :
    (choices xs).length = size (fun a => (xs a).length) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    unfold choices size
    rw [flatMap_constant_length _ _ (size (fun a => (xs a.succ).length))]
    intro a _
    rw [List.length_map, ih]

theorem choices_membership {q} {V : Fin q → Type}
    (xs : (a : Fin q) → List (V a)) (v : (a : Fin q) → V a) :
    v ∈ choices xs ↔ ∀ a, v a ∈ xs a := by
  induction q with
  | zero =>
    constructor
    · intro _ a; exact Fin.elim0 a
    · intro _
      have he : v = fun a => Fin.elim0 a := by funext a; exact Fin.elim0 a
      simp only [choices, List.mem_singleton, he]
  | succ q ih =>
    constructor
    · intro h
      obtain ⟨a, ha, hm⟩ := List.mem_flatMap.1 h
      obtain ⟨w, hw, he⟩ := List.mem_map.1 hm
      intro i
      subst v
      exact Fin.cases ha (fun j => (ih _ w).1 hw j) i
    · intro h
      apply List.mem_flatMap.2
      refine ⟨v 0, h 0, List.mem_map.2 ⟨fun a => v a.succ, (ih _ _).2 (fun a => h a.succ), ?_⟩⟩
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

theorem choices_nodup {q} {V : Fin q → Type} (xs : (a : Fin q) → List (V a))
    (hn : ∀ a, (xs a).Nodup) : (choices xs).Nodup := by
  induction q with
  | zero => simp only [choices, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self]
  | succ q ih =>
    change List.Pairwise (· ≠ ·) ((xs 0).flatMap _)
    rw [List.pairwise_flatMap]
    constructor
    · intro a _
      rw [List.pairwise_map]
      exact (ih _ (fun a => hn a.succ)).imp
        (fun {f g} h he => h (by funext i; exact congrFun he i.succ))
    · exact (hn 0).imp (fun {a b} hab => by
        intro f hf g hg he
        obtain ⟨u, _, hu⟩ := List.mem_map.1 hf
        obtain ⟨v, _, hv⟩ := List.mem_map.1 hg
        exact hab (congrFun (hu.trans (he.trans hv.symm)) 0))

theorem inactive_vertex_fiber (N : Nat) : (maps 1 N).length = N := by
  rw [maps_length, Nat.pow_one]

theorem edge_endpoint_choices (q : Nat) : (maps q 2).length = 2^q := maps_length q 2

-- Arithmetic assembly is conditional on the actual rooted inventory count.
-- This hcount must be supplied by matching/word and graph extraction bijections.
theorem repeated_edge_cancellation (r J C : Nat)
    (hcount : (2*(2*r+4))*C = 2^(r+1)*factorial r*J) :
    (2*r+4)*C = 2^r*factorial r*J := by
  have htwo : 2*((2*r+4)*C) = 2*(2^r*factorial r*J) := by
    calc
      _ = (2*(2*r+4))*C := by rw [Nat.mul_assoc]
      _ = 2^(r+1)*factorial r*J := hcount
      _ = _ := by rw [Nat.pow_succ]; ac_rfl
  exact Nat.eq_of_mul_eq_mul_left (by decide) htwo

theorem repeated_edge_formula (r J C : Nat)
    (hcount : (2*(2*r+4))*C = 2^(r+1)*factorial r*J) :
    C = (2^r*factorial r*J)/(2*r+4) := by
  rw [← repeated_edge_cancellation r J C hcount, Nat.mul_comm]
  exact (Nat.mul_div_cancel C (by omega)).symm

#print axioms choices_length
#print axioms choices_membership
#print axioms choices_nodup
#print axioms inactive_vertex_fiber
#print axioms edge_endpoint_choices
#print axioms repeated_edge_cancellation
#print axioms repeated_edge_formula
end ECC.FiberCardinality
