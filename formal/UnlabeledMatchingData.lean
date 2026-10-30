import JointMatchingCount

namespace ECC.UnlabeledMatchingData
open OccurrenceMatching MatchingRelabel MatchingFiber MatchingCount JointMatchingCount

-- Label-free data: the distinguished four-set and the equality relation on
-- its complementary two-element blocks. Diagonal entries add no extra data.
structure Data (L : Nat) where
  distinguished : Fin L → Bool
  paired : Fin L → Fin L → Bool

def data {r L} (w : Fin L → Fin (r+1)) : Data L where
  distinguished := fun p => decide (w p = 0)
  paired := fun p q => decide (w p ≠ 0 ∧ w p = w q)

theorem same_data_iff {r L} (w v : Fin L → Fin (r+1)) : data w = data v ↔ Same w v := by
  constructor
  · intro he
    have hf := congrArg Data.distinguished he
    have hp := congrArg Data.paired he
    have hz : ∀ p, w p = 0 ↔ v p = 0 := by
      intro p
      have hb := congrFun hf p
      exact decide_eq_decide.1 hb
    refine ⟨hz, ?_⟩
    intro p q
    have hb := decide_eq_decide.1 (congrFun (congrFun hp p) q)
    change (w p ≠ 0 ∧ w p = w q) ↔ (v p ≠ 0 ∧ v p = v q) at hb
    constructor
    · intro heq
      by_cases hp0 : w p = 0
      · exact ((hz p).1 hp0).trans ((hz q).1 (heq.symm.trans hp0)).symm
      · exact (hb.1 ⟨hp0,heq⟩).2
    · intro heq
      by_cases hp0 : v p = 0
      · exact ((hz p).2 hp0).trans ((hz q).2 (heq.symm.trans hp0)).symm
      · exact (hb.2 ⟨hp0,heq⟩).2
  · intro hs
    unfold data
    congr 1
    · funext p
      exact decide_eq_decide.2 (hs.1 p)
    · funext p q
      apply decide_eq_decide.2
      exact and_congr (not_congr (hs.1 p)) (hs.2 p q)

def canonicalData (r L : Nat) : List (Data L) := (representatives r L).map data

theorem canonicalData_nodup (r L : Nat) : (canonicalData r L).Nodup := by
  unfold canonicalData
  change List.Pairwise (· ≠ ·) ((representatives r L).map data)
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem
    (p := FiniteQuotient.select_nodup Same same_refl (fun w v => same_symm w v)
      (inventory r L).length (inventory r L))
  intro w v hw hv hne he
  exact hne (FiniteQuotient.select_unique Same (fun w v => same_symm w v)
    (inventory r L).length (inventory r L) w v hw hv ((same_data_iff w v).1 he))

theorem canonicalData_complete {r L} (w : Fin L → Fin (r+1)) (hw : Profile w) :
    data w ∈ canonicalData r L := by
  obtain ⟨v, hv, hs⟩ := FiniteQuotient.select_covers Same same_refl
    (fun u v w => same_trans u v w) (inventory r L).length (inventory r L)
    (Nat.le_refl _) w ((inventory_membership w).2 hw)
  exact List.mem_map.2 ⟨v,hv,(same_data_iff v w).2 hs⟩

theorem canonicalData_sound {r L} (d : Data L) (hd : d ∈ canonicalData r L) :
    ∃ w : Fin L → Fin (r+1), Profile w ∧ data w = d := by
  obtain ⟨w, hw, he⟩ := List.mem_map.1 hd
  exact ⟨w,representative_profile w hw,he⟩

-- A labeled endpoint matching produces one of the canonical label-free data;
-- reverse extraction already proves no valid endpoint matching is omitted.
theorem matching_data_complete {r L} (M : ResolutionMatching.Matching r L) :
    data (traceLabels M) ∈ canonicalData r L := canonicalData_complete _ (traceLabels_profile M)

theorem canonicalData_length (r L : Nat) :
    (canonicalData r L).length = (representatives r L).length := by
  rw [canonicalData, List.length_map]

def acceptedData (r : Nat) : List (Data (2*r+4)) :=
  ((representatives r (2*r+4)).filter accepted).map data

theorem acceptedData_nodup (r : Nat) : (acceptedData r).Nodup := by
  have hn := canonicalData_nodup r (2*r+4)
  change List.Pairwise (· ≠ ·) ((representatives r (2*r+4)).map data) at hn
  rw [List.pairwise_map] at hn
  change List.Pairwise (· ≠ ·) (((representatives r (2*r+4)).filter accepted).map data)
  rw [List.pairwise_map]
  exact hn.filter accepted

theorem acceptedData_membership {r} (w : Fin (2*r+4) → Fin (r+1)) (hw : Profile w) :
    data w ∈ acceptedData r ↔ accepted w = true := by
  constructor
  · intro hd
    obtain ⟨v, hv, he⟩ := List.mem_map.1 hd
    have hp := List.mem_filter.1 hv
    have hs := (same_data_iff v w).1 he
    exact (accepted_stable (by omega) v w (representative_profile v hp.1) hw hs).symm.trans hp.2
  · intro hwaccept
    obtain ⟨v, hv, hs⟩ := FiniteQuotient.select_covers Same same_refl
      (fun u v w => same_trans u v w) (inventory r (2*r+4)).length (inventory r (2*r+4))
      (Nat.le_refl _) w ((inventory_membership w).2 hw)
    apply List.mem_map.2
    exact ⟨v, List.mem_filter.2 ⟨hv,
      (accepted_stable (by omega) v w (representative_profile v hv) hw hs).trans hwaccept⟩,
      (same_data_iff v w).2 hs⟩

theorem jointMatchingCount_is_data_count (r : Nat) :
    jointMatchingCount r = (acceptedData r).length := by
  rw [acceptedData, List.length_map]
  rfl

theorem labeled_words_from_unlabeled_data (r : Nat) :
    ((inventory r (2*r+4)).filter accepted).length = MatchingLabels.factorial r * (acceptedData r).length := by
  rw [← jointMatchingCount_is_data_count]
  exact labeled_joint_count r

-- These are rooted INPUTS, before product-vertex trace reconstruction. Their
-- count is now proved; identifying them with the graph-sector inventory is
-- the remaining trace/quotient transport obligation.
def rootedInputs (r : Nat) : List ((Fin (2*r+4) → Fin (r+1)) × (Fin (r+1) → Fin 2)) :=
  ((inventory r (2*r+4)).filter accepted).flatMap fun w =>
    (MotifTransport.maps (r+1) 2).map fun b => (w,b)

theorem rootedInputs_length (r : Nat) :
    (rootedInputs r).length = 2^(r+1) * MatchingLabels.factorial r * jointMatchingCount r := by
  rw [rootedInputs, MatchingLabels.flatMap_constant_length _ _ (2^(r+1))]
  · rw [labeled_joint_count]
    ac_rfl
  · intro w _
    rw [List.length_map, MotifTransport.maps_length]

theorem rootedInputs_nodup (r : Nat) : (rootedInputs r).Nodup := by
  unfold rootedInputs
  change List.Pairwise (· ≠ ·) (((inventory r (2*r+4)).filter accepted).flatMap _)
  rw [List.pairwise_flatMap]
  constructor
  · intro w _
    rw [List.pairwise_map]
    exact (MotifTransport.maps_nodup (r+1) 2).imp
      (fun {a b} h he => h (congrArg Prod.snd he))
  · have hn : (((inventory r (2*r+4)).filter accepted)).Nodup :=
      ((MotifTransport.maps_nodup (2*r+4) (r+1)).filter _).filter _
    exact hn.imp (fun {u v} huv => by
      intro a ha b hb he
      obtain ⟨x, _, hx⟩ := List.mem_map.1 ha
      obtain ⟨y, _, hy⟩ := List.mem_map.1 hb
      exact huv (congrArg Prod.fst (hx.trans (he.trans hy.symm))))

theorem rootedInputs_membership {r} (w : Fin (2*r+4) → Fin (r+1)) (b : Fin (r+1) → Fin 2) :
    (w,b) ∈ rootedInputs r ↔ Profile w ∧ accepted w = true := by
  simp only [rootedInputs, List.mem_flatMap, List.mem_map, MotifTransport.mem_maps,
    true_and, Prod.mk.injEq, inventory_membership, List.mem_filter]
  constructor
  · rintro ⟨v, ⟨hp,ha⟩, c, ⟨he, _⟩⟩
    subst v
    exact ⟨hp,ha⟩
  · rintro ⟨hp,ha⟩
    exact ⟨w, ⟨hp,ha⟩, b, rfl, rfl⟩

theorem canonicalData_is_matching {r L} (d : Data L) (hd : d ∈ canonicalData r L) :
    ∃ M : ResolutionMatching.Matching r L, data (traceLabels M) = d := by
  obtain ⟨w,hw,he⟩ := canonicalData_sound d hd
  exact ⟨extract w hw, by rw [traceLabels_extract]; exact he⟩

theorem accepted_matching_data {r} (M : ResolutionMatching.Matching r (2*r+4)) :
    data (traceLabels M) ∈ acceptedData r ↔ jointCheck M = true := by
  rw [acceptedData_membership _ (traceLabels_profile M)]
  simp only [accepted, traceLabels_profile M, ↓reduceDIte, extract_traceLabels]

#print axioms canonicalData_is_matching
#print axioms accepted_matching_data
#print axioms rootedInputs_nodup
#print axioms rootedInputs_membership
#print axioms acceptedData_nodup
#print axioms acceptedData_membership
#print axioms jointMatchingCount_is_data_count
#print axioms labeled_words_from_unlabeled_data
#print axioms rootedInputs_length
#print axioms same_data_iff
#print axioms canonicalData_nodup
#print axioms canonicalData_complete
#print axioms canonicalData_sound
#print axioms matching_data_complete
#print axioms canonicalData_length
end ECC.UnlabeledMatchingData
