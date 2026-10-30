import UnlabeledMatchingData
import GlobalCycleCount
import FiberCardinality

namespace ECC.RepeatedEdgeAssembly
open MatchingLabels JointMatchingCount UnlabeledMatchingData

abbrev Input (r : Nat) := (Fin (2*r+4) → Fin (r+1)) × (Fin (r+1) → Fin 2)

-- The remaining hypothesis is now an actual trace-inventory correspondence,
-- with injectivity and membership, rather than the numerical hcount equation.
theorem transported_rooted_count {r N} (I : GlobalCycleCount.Inventory (2*r+4) N)
    (trace : Input r → (Fin (2*r+4) → Fin N))
    (hinj : ∀ x, x ∈ rootedInputs r → ∀ y, y ∈ rootedInputs r → trace x = trace y → x = y)
    (hmem : ∀ v, v ∈ I.rooted ↔ ∃ x, x ∈ rootedInputs r ∧ trace x = v) :
    I.rooted.length = (rootedInputs r).length := by
  have hn : ((rootedInputs r).map trace).Nodup := by
    change List.Pairwise (· ≠ ·) ((rootedInputs r).map trace)
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem (p := rootedInputs_nodup r)
    intro x y hx hy hne he
    exact hne (hinj x hx y hy he)
  have he : I.rooted.length = ((rootedInputs r).map trace).length := by
    apply FiniteCardinality.same_members_length _ _ I.rooted_nodup hn
    intro v
    simpa only [List.mem_map] using hmem v
  exact he.trans (List.length_map trace)

theorem formula_from_trace_transport {r N} (I : GlobalCycleCount.Inventory (2*r+4) N)
    (trace : Input r → (Fin (2*r+4) → Fin N))
    (hinj : ∀ x, x ∈ rootedInputs r → ∀ y, y ∈ rootedInputs r → trace x = trace y → x = y)
    (hmem : ∀ v, v ∈ I.rooted ↔ ∃ x, x ∈ rootedInputs r ∧ trace x = v) :
    I.representatives.length = (2^r * factorial r * jointMatchingCount r)/(2*r+4) := by
  have hcount : (2*(2*r+4))*I.representatives.length =
      2^(r+1)*factorial r*jointMatchingCount r :=
    (GlobalCycleCount.global_rooted_count (by omega) I).symm.trans
      ((transported_rooted_count I trace hinj hmem).trans (rootedInputs_length r))
  exact FiberCardinality.repeated_edge_formula r _ _ hcount

#print axioms transported_rooted_count
#print axioms formula_from_trace_transport
end ECC.RepeatedEdgeAssembly
