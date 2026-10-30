import MatchingCount

namespace ECC.JointMatchingCount
open OccurrenceMatching MatchingRelabel MatchingFiber MatchingCount ResolutionMatching
open ChordConnectivity MatchingLabels

theorem same_positions {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hs : Same w v)
    (a : Fin (r+1)) : positions v (rename w v h a) = positions w a := by
  apply sorted_unique _ _ (positions_sorted _ _) (positions_sorted _ _)
  intro p
  rw [mem_positions, mem_positions]
  constructor
  · intro he
    exact rename_injective w v h hs _ _ ((rename_word w v h hs p).trans he)
  · intro he
    exact (rename_word w v h hs p).symm.trans (congrArg (rename w v h) he)

theorem same_distinguished {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hv : Profile v)
    (hs : Same w v) (i : Fin 4) : (extract w h).pos (.inl i) = (extract v hv).pos (.inl i) := by
  have he := same_positions w v h hs 0
  rw [rename_zero w v h hs] at he
  change ((positions w 0)[i.val]'(slot_bound w h (.inl i))).val =
    ((positions v 0)[i.val]'(slot_bound v hv (.inl i))).val
  have hh := congrArg (fun ps : List (Fin L) => ps[i.val]?) he
  have hwidx : i.val < (positions w 0).length := slot_bound w h (.inl i)
  have hvidx : i.val < (positions v 0).length := slot_bound v hv (.inl i)
  rw [List.getElem?_eq_getElem hvidx, List.getElem?_eq_getElem hwidx] at hh
  exact congrArg Fin.val (Option.some.inj hh.symm)

theorem same_pair {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hv : Profile v)
    (hs : Same w v) (j : Fin r) (b : Bool) :
    (extract w h).pos (.inr (j,b)) = (extract v hv).pos (.inr (restRename w v h hs j,b)) := by
  have he := same_positions w v h hs j.succ
  rw [← restRename_succ w v h hs j] at he
  change ((positions w j.succ)[if b then 1 else 0]'(slot_bound w h (.inr (j,b)))).val =
    ((positions v (restRename w v h hs j).succ)[if b then 1 else 0]'
      (slot_bound v hv (.inr (restRename w v h hs j,b)))).val
  have hh := congrArg (fun ps : List (Fin L) => ps[if b then 1 else 0]?) he
  have hwidx : (if b then 1 else 0) < (positions w j.succ).length := slot_bound w h (.inr (j,b))
  have hvidx : (if b then 1 else 0) < (positions v (restRename w v h hs j).succ).length :=
    slot_bound v hv (.inr (restRename w v h hs j,b))
  rw [List.getElem?_eq_getElem hvidx, List.getElem?_eq_getElem hwidx] at hh
  exact congrArg Fin.val (Option.some.inj hh.symm)

theorem same_phase {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hv : Profile v)
    (hs : Same w v) (t : Nat) : phase (extract w h) t = phase (extract v hv) t := by
  apply Fin.ext
  simp only [phase, same_distinguished w v h hv hs]

theorem same_restState {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hv : Profile v)
    (hs : Same w v) (t : Nat) (j : Fin r) :
    restState (extract w h) t j = restState (extract v hv) t (restRename w v h hs j) := by
  simp only [restState, same_pair w v h hv hs]

theorem same_folded_forward {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hv : Profile v)
    (hs : Same w v) (hi : FoldedInjective (extract w h)) : FoldedInjective (extract v hv) := by
  intro s t he
  apply hi s t
  apply Prod.ext
  · have hp := congrArg Prod.fst he
    simpa only [same_phase w v h hv hs] using hp
  · funext j
    change restState (extract w h) s.val j = restState (extract w h) t.val j
    rw [same_restState w v h hv hs s.val j, same_restState w v h hv hs t.val j]
    exact congrFun (congrArg Prod.snd he) (restRename w v h hs j)

theorem same_folded_iff {r L} (w v : Fin L → Fin (r+1)) (h : Profile w) (hv : Profile v)
    (hs : Same w v) : FoldedInjective (extract w h) ↔ FoldedInjective (extract v hv) :=
  ⟨same_folded_forward w v h hv hs, same_folded_forward v w hv h (same_symm w v hs)⟩

def connectedCheck {n L} (D : Diagram n L) : Bool :=
  (colors n).all fun c => decide (Invariant D c → ∀ a b, c a = c b)

theorem connectedCheck_iff {n L} (D : Diagram n L) : connectedCheck D = true ↔ Connected D := by
  simp only [connectedCheck, List.all_eq_true, decide_eq_true_eq, Connected]
  exact ⟨fun h c => h c (mem_colors c), fun h c _ => h c⟩

def jointCheck {r L} (M : Matching r L) : Bool :=
  connectedCheck (diagram M false) && connectedCheck (diagram M true)

theorem jointCheck_iff {r L} (M : Matching r L) (hL : 0 < L) :
    jointCheck M = true ↔ FoldedInjective M := by
  rw [jointCheck, Bool.and_eq_true, connectedCheck_iff, connectedCheck_iff]
  exact (simultaneous_resolutions M hL).symm

def accepted {r L} (w : Fin L → Fin (r+1)) : Bool :=
  if h : Profile w then jointCheck (extract w h) else false

theorem accepted_iff {r L} (w : Fin L → Fin (r+1)) (h : Profile w) (hL : 0 < L) :
    accepted w = true ↔ FoldedInjective (extract w h) := by
  simp only [accepted, h, ↓reduceDIte]
  exact jointCheck_iff _ hL

theorem accepted_stable {r L} (hL : 0 < L) (w v : Fin L → Fin (r+1))
    (h : Profile w) (hv : Profile v) (hs : Same w v) : accepted w = accepted v := by
  have he : accepted w = true ↔ accepted v = true :=
    (accepted_iff w h hL).trans ((same_folded_iff w v h hv hs).trans (accepted_iff v hv hL).symm)
  cases hw : accepted w <;> cases hv' : accepted v
  · rfl
  · exact False.elim (Bool.noConfusion (hw.symm.trans (he.2 hv')))
  · exact False.elim (Bool.noConfusion (hv'.symm.trans (he.1 hw)))
  · rfl

-- J counts canonical representatives of the distinguished four-set plus
-- complementary unlabeled pairs, tested by both connected resolutions.
def jointMatchingCount (r : Nat) : Nat := J r (2*r+4) accepted

theorem labeled_joint_count (r : Nat) :
    ((inventory r (2*r+4)).filter accepted).length = factorial r * jointMatchingCount r :=
  matching_count (r := r) (L := 2*r+4) accepted (accepted_stable (by omega))

#print axioms same_positions
#print axioms same_distinguished
#print axioms same_pair
#print axioms same_phase
#print axioms same_restState
#print axioms same_folded_forward
#print axioms same_folded_iff
#print axioms connectedCheck_iff
#print axioms jointCheck_iff
#print axioms accepted_iff
#print axioms accepted_stable
#print axioms labeled_joint_count
end ECC.JointMatchingCount
