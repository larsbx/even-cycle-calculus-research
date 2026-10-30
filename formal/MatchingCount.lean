import MatchingFiber

namespace ECC.MatchingCount
open OccurrenceMatching MatchingRelabel MatchingFiber MatchingLabels

instance wordDecidableEq {L r} : DecidableEq (Fin L → Fin (r+1)) := fun f g =>
  decidable_of_iff (∀ p, f p = g p) ⟨fun h => funext h, fun h p => congrFun h p⟩

def inventory (r L : Nat) : List (Fin L → Fin (r+1)) :=
  (MotifTransport.maps L (r+1)).filter fun w => decide (Profile w)

theorem inventory_membership {r L} (w : Fin L → Fin (r+1)) :
    w ∈ inventory r L ↔ Profile w := by
  simp only [inventory, List.mem_filter, MotifTransport.mem_maps, decide_eq_true_eq, true_and]

def representatives (r L : Nat) : List (Fin L → Fin (r+1)) :=
  FiniteQuotient.select Same (inventory r L).length (inventory r L)

theorem representative_profile {r L} (w : Fin L → Fin (r+1)) (hw : w ∈ representatives r L) :
    Profile w := (inventory_membership w).1 (FiniteQuotient.select_subset Same _ _ w hw)

def J (r L : Nat) (accept : (Fin L → Fin (r+1)) → Bool) : Nat :=
  ((representatives r L).filter accept).length

-- Stability is only required on words of the specified profile. This generic
-- theorem is instantiated with the proved two-resolution predicate separately.
theorem matching_count {r L} (accept : (Fin L → Fin (r+1)) → Bool)
    (stable : ∀ w v, Profile w → Profile v → Same w v → accept w = accept v) :
    ((inventory r L).filter accept).length = factorial r * J r L accept := by
  let reps := (representatives r L).filter accept
  have hrep : ∀ w, w ∈ reps → Profile w := fun w hw =>
    representative_profile w (List.mem_filter.1 hw).1
  have hrn : reps.Nodup :=
    (FiniteQuotient.select_nodup Same same_refl (fun w v => same_symm w v)
      (inventory r L).length (inventory r L)).filter accept
  have hflat : (reps.flatMap fiber).Nodup := by
    change List.Pairwise (· ≠ ·) (reps.flatMap fiber)
    rw [List.pairwise_flatMap]
    constructor
    · intro w hw
      exact fiber_nodup w (hrep w hw)
    · apply List.Pairwise.imp_of_mem (p := hrn)
      intro w v hw hv hne a ha b hb he
      subst b
      have hwa := (fiber_membership w a (hrep w hw)).1 ha
      have hva := (fiber_membership v a (hrep v hv)).1 hb
      have hwv := same_trans w a v hwa.2 (same_symm v a hva.2)
      exact hne (FiniteQuotient.select_unique Same (fun w v => same_symm w v)
        (inventory r L).length (inventory r L) w v
        (List.mem_filter.1 hw).1 (List.mem_filter.1 hv).1 hwv)
  have hm : ∀ v, v ∈ (inventory r L).filter accept ↔ v ∈ reps.flatMap fiber := by
    intro v
    constructor
    · intro hv
      obtain ⟨hw, ha⟩ := List.mem_filter.1 hv
      have hp := (inventory_membership v).1 hw
      obtain ⟨w, hwr, hsame⟩ := FiniteQuotient.select_covers Same same_refl
        (fun u v w => same_trans u v w) (inventory r L).length (inventory r L)
        (Nat.le_refl _) v hw
      have hwp := representative_profile w hwr
      have hwaccept : accept w = true := (stable w v hwp hp hsame).trans ha
      apply List.mem_flatMap.2
      exact ⟨w, List.mem_filter.2 ⟨hwr,hwaccept⟩, (fiber_membership w v hwp).2 ⟨hp,hsame⟩⟩
    · intro hv
      obtain ⟨w, hw, hv⟩ := List.mem_flatMap.1 hv
      have hp := (fiber_membership w v (hrep w hw)).1 hv
      apply List.mem_filter.2
      exact ⟨(inventory_membership v).2 hp.1,
        (stable w v (hrep w hw) hp.1 hp.2).symm.trans (List.mem_filter.1 hw).2⟩
  calc
    _ = (reps.flatMap fiber).length := FiniteCardinality.same_members_length _ _
      ((MotifTransport.maps_nodup L (r+1)).filter _ |>.filter accept) hflat hm
    _ = reps.length * factorial r := flatMap_constant_length _ _ _ (fun w _ => fiber_length w)
    _ = factorial r * J r L accept := Nat.mul_comm _ _

#print axioms inventory_membership
#print axioms representative_profile
#print axioms matching_count
end ECC.MatchingCount
