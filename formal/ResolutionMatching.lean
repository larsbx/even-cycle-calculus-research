import ChordConnectivity
import RepeatedEdge

namespace ECC.ResolutionMatching
open ChordConnectivity

abbrev End (r : Nat) := Sum (Fin 4) (Fin r × Bool)

-- false=0011 (front), true=0110 (outer).
def ends {r} (outer : Bool) (i : Fin (r+2)) (side : Bool) : End r :=
  Fin.cases (Sum.inl (if side then if outer then 3 else 1 else 0))
    (Fin.cases (Sum.inl (if side then if outer then 2 else 3 else if outer then 1 else 2))
      (fun j => Sum.inr (j, side))) i

def owner {r} (outer : Bool) : End r → Fin (r+2)
  | .inl p => if p = 0 ∨ p = (if outer then 3 else 1) then 0 else 1
  | .inr (j, _) => j.succ.succ

def sideOf {r} (outer : Bool) : End r → Bool
  | .inl p => if p = (if outer then 3 else 1) ∨ p = (if outer then 2 else 3) then true else false
  | .inr (_, b) => b

theorem owner_ends {r} (o : Bool) (i : Fin (r+2)) (b : Bool) :
    owner o (ends o i b) = i := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · cases o <;> cases b <;> rfl
  · cases o <;> cases b <;> rfl
  · cases o <;> cases b <;> rfl

theorem side_ends {r} (o : Bool) (i : Fin (r+2)) (b : Bool) :
    sideOf o (ends o i b) = b := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · cases o <;> cases b <;> rfl
  · cases o <;> cases b <;> rfl
  · cases o <;> cases b <;> rfl

theorem ends_owner {r} (o : Bool) (e : End r) :
    ends o (owner o e) (sideOf o e) = e := by
  cases e with
  | inl p =>
    have hp : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by
      have := p.isLt
      omega
    rcases hp with rfl | rfl | rfl | rfl <;> cases o <;> rfl
  | inr p => cases p with | mk j b => rfl

structure Matching (r L : Nat) where
  pos : End r → Nat
  injective : ∀ e f, pos e = pos f → e = f
  bound : ∀ e, pos e < L
  cover : ∀ p, p < L → ∃ e, pos e = p
  distinguished : pos (.inl 0) < pos (.inl 1) ∧
    pos (.inl 1) < pos (.inl 2) ∧ pos (.inl 2) < pos (.inl 3)
  rest : ∀ j, pos (.inr (j, false)) < pos (.inr (j, true))

def diagram {r L} (M : Matching r L) (o : Bool) : Diagram (r+2) L where
  lo := fun i => M.pos (ends o i false)
  hi := fun i => M.pos (ends o i true)
  ordered := by
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · cases o
      · exact M.distinguished.1
      · exact Nat.lt_trans M.distinguished.1 (Nat.lt_trans M.distinguished.2.1 M.distinguished.2.2)
    · cases o
      · exact M.distinguished.2.2
      · exact M.distinguished.2.1
    · exact M.rest k
  bounded := fun i => M.bound _
  cover := by
    intro p hp
    obtain ⟨e, he⟩ := M.cover p hp
    refine ⟨owner o e, ?_⟩
    have h := congrArg M.pos (ends_owner o e)
    cases hb : sideOf o e
    · exact Or.inl (by simpa only [hb, he] using h)
    · exact Or.inr (by simpa only [hb, he] using h)
  disjoint := by
    intro a b hab
    have hn : ∀ s t, M.pos (ends o a s) ≠ M.pos (ends o b t) := by
      intro s t h
      have he := congrArg (owner o) (M.injective _ _ h)
      exact hab (by simpa only [owner_ends] using he)
    exact ⟨hn false false, hn false true, hn true false, hn true true⟩

def phase {r L} (M : Matching r L) (t : Nat) : Fin 5 :=
  ⟨(if M.pos (.inl 0) < t then 1 else 0) +
   (if M.pos (.inl 1) < t then 1 else 0) +
   (if M.pos (.inl 2) < t then 1 else 0) +
   (if M.pos (.inl 3) < t then 1 else 0), by
    by_cases ha : M.pos (.inl 0) < t <;>
      by_cases hb : M.pos (.inl 1) < t <;>
      by_cases hc : M.pos (.inl 2) < t <;>
      by_cases hd : M.pos (.inl 3) < t <;> simp [ha, hb, hc, hd]⟩

def restState {r L} (M : Matching r L) (t : Nat) (j : Fin r) : Bool :=
  decide (M.pos (.inr (j, false)) < t ∧ t ≤ M.pos (.inr (j, true)))

def resolved {r L} (M : Matching r L) (o : Bool) (t : Nat) : Bool × Bool :=
  if o then RepeatedEdge.outer (phase M t) else RepeatedEdge.front (phase M t)

theorem resolved_state {r L} (M : Matching r L) (o : Bool) (t : Nat) :
    state (diagram M o) t 0 = (resolved M o t).1 ∧
    state (diagram M o) t 1 = (resolved M o t).2 ∧
    ∀ j : Fin r, state (diagram M o) t j.succ.succ = restState M t j := by
  have ho := M.distinguished
  change decide (M.pos (.inl 0) < t ∧ t ≤ M.pos (.inl (if o then 3 else 1))) =
      (resolved M o t).1 ∧
    decide (M.pos (.inl (if o then 1 else 2)) < t ∧
      t ≤ M.pos (.inl (if o then 2 else 3))) = (resolved M o t).2 ∧
    ∀ j : Fin r, restState M t j = restState M t j
  cases o <;>
    by_cases ha : M.pos (.inl 0) < t <;>
    by_cases hb : M.pos (.inl 1) < t <;>
    by_cases hc : M.pos (.inl 2) < t <;>
    by_cases hd : M.pos (.inl 3) < t <;>
    simp only [resolved, RepeatedEdge.front, RepeatedEdge.outer, phase, ha, hb, hc, hd,
      ↓reduceIte, Nat.add_zero, Nat.zero_add] <;>
    dsimp <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.false_eq_true,
      true_and, false_and, decide_false, Bool.and_true, Bool.and_false,
      (show decide (0 < 0) = false from rfl),
      (show decide (0 < 1) = true from rfl),
      (show decide (0 < 2) = true from rfl),
      (show decide (0 < 3) = true from rfl),
      (show decide (0 < 4) = true from rfl),
      (show decide (1 < 4) = true from rfl),
      (show decide (2 < 4) = true from rfl),
      (show decide (3 < 4) = true from rfl),
      (show decide (4 < 4) = false from rfl)] <;>
    (try simp only [decide_eq_true_eq, decide_eq_false_iff_not]) <;>
    (first | trivial | finite_omega)

-- Product-state equality is derived from occurrence positions, not assumed.
theorem resolved_equal {r L} (M : Matching r L) (o : Bool) (s t : Nat) :
    (∀ a, state (diagram M o) s a = state (diagram M o) t a) ↔
      resolved M o s = resolved M o t ∧ restState M s = restState M t := by
  have hs := resolved_state M o s
  have ht := resolved_state M o t
  constructor
  · intro h
    constructor
    · apply Prod.ext
      · exact hs.1.symm.trans ((h 0).trans ht.1)
      · exact hs.2.1.symm.trans ((h 1).trans ht.2.1)
    · funext j
      exact (hs.2.2 j).symm.trans ((h j.succ.succ).trans (ht.2.2 j))
  · rintro ⟨he, hr⟩ a
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) a
    · exact hs.1.trans ((congrArg Prod.fst he).trans ht.1.symm)
    · exact hs.2.1.trans ((congrArg Prod.snd he).trans ht.2.1.symm)
    · exact (hs.2.2 k).trans ((congrFun hr k).trans (ht.2.2 k).symm)

def FoldedInjective {r L} (M : Matching r L) : Prop :=
  ∀ s t : Fin L, (RepeatedEdge.folded (phase M s.val), restState M s.val) =
    (RepeatedEdge.folded (phase M t.val), restState M t.val) → s = t

theorem simultaneous_resolutions {r L} (M : Matching r L) (hL : 0 < L) :
    FoldedInjective M ↔ Connected (diagram M false) ∧ Connected (diagram M true) := by
  have hstate : ∀ o, CollisionFree (diagram M o) ↔
      (∀ s t : Fin L, (resolved M o s.val, restState M s.val) =
        (resolved M o t.val, restState M t.val) → s = t) := by
    intro o
    constructor
    · intro h s t he
      exact h s t ((resolved_equal M o _ _).2 ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩)
    · intro h s t he
      have hp := (resolved_equal M o _ _).1 he
      exact h s t (Prod.ext hp.1 hp.2)
  rw [← collision_free_iff_connected _ hL, ← collision_free_iff_connected _ hL,
    hstate false, hstate true]
  constructor
  · intro h
    constructor
    · intro s t he
      have hp := congrArg Prod.fst he
      have hr := congrArg Prod.snd he
      exact h s t (Prod.ext ((RepeatedEdge.phase_collision _ _).2 (Or.inl hp)) hr)
    · intro s t he
      have hp := congrArg Prod.fst he
      have hr := congrArg Prod.snd he
      exact h s t (Prod.ext ((RepeatedEdge.phase_collision _ _).2 (Or.inr hp)) hr)
  · rintro ⟨hf, ho⟩ s t he
    have hp := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    rcases (RepeatedEdge.phase_collision _ _).1 hp with h | h
    · exact hf s t (Prod.ext h hr)
    · exact ho s t (Prod.ext h hr)

#print axioms owner_ends
#print axioms side_ends
#print axioms ends_owner
#print axioms resolved_state
#print axioms resolved_equal
#print axioms simultaneous_resolutions
end ECC.ResolutionMatching
