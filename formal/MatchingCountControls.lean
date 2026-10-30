import UnlabeledMatchingData
namespace ECC.MatchingCountControls
open OccurrenceMatching MatchingRelabel MatchingFiber MatchingCount JointMatchingCount
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem small_profile_inventories :
    (inventory 0 4).length = 1 ∧ (inventory 1 6).length = 15 := by decide

theorem small_accepted_inventories :
    ((inventory 0 4).filter accepted).length = 0 ∧
    ((inventory 1 6).filter accepted).length = 0 := by decide

theorem small_joint_counts : jointMatchingCount 0 = 0 ∧ jointMatchingCount 1 = 0 := by
  have h0 := labeled_joint_count 0
  have h1 := labeled_joint_count 1
  rw [small_accepted_inventories.1] at h0
  rw [small_accepted_inventories.2] at h1
  simp only [MatchingLabels.factorial] at h0 h1
  constructor <;> omega

def w : Fin 8 → Fin 3 := fun p => #[0,1,0,2,0,1,0,2][p.val]!
def v : Fin 8 → Fin 3 := fun p => #[0,2,0,1,0,2,0,1][p.val]!

theorem label_sensitive_filter_control :
    Profile w ∧ Profile v ∧ Same w v ∧ w 1 = 1 ∧ v 1 = 2 := by decide

theorem fixed_fiber_two : (fiber w).length = 2 := by
  rw [fiber_length]
  rfl

theorem malformed_inventory_rejected :
    ¬ Profile (fun _ : Fin 6 => (0 : Fin 2)) ∧
    ¬ Profile (fun _ : Fin 5 => (0 : Fin 1)) := by decide

#print axioms small_profile_inventories
#print axioms small_accepted_inventories
#print axioms small_joint_counts
#print axioms label_sensitive_filter_control
#print axioms fixed_fiber_two
#print axioms malformed_inventory_rejected
end ECC.MatchingCountControls
