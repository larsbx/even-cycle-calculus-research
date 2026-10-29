import Std

/- General finite graph-level decoding lemmas. They are independent of the
   numerical tables and introduce no axioms or runtime evaluation certificates.
   The remaining counting/extraction obligations are listed in README.md. -/
namespace ECC.CollisionBridge

abbrev Vertex {q : Nat} (n : Fin q → Nat) := (a : Fin q) → Fin (n a)

def Decode {q : Nat} {n N : Fin q → Nat}
    (f : (a : Fin q) → Fin (n a) → Fin (N a)) (x : Vertex n) : Vertex N :=
  fun a => f a (x a)

def CoordinateStep {q : Nat} {n : Fin q → Nat}
    (a : Fin q) (x y : Vertex n) : Prop :=
  x a ≠ y a ∧ ∀ b, b ≠ a → x b = y b

def CartesianAdj {q : Nat} {n : Fin q → Nat}
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (x y : Vertex n) : Prop :=
  ∃ a, edge a (x a) (y a) ∧ CoordinateStep a x y

def FactorInjective {q : Nat} {n N : Fin q → Nat}
    (f : (a : Fin q) → Fin (n a) → Fin (N a)) : Prop :=
  ∀ a u v, f a u = f a v → u = v

theorem decode_equal_iff {q : Nat} {n N : Fin q → Nat}
    (f : (a : Fin q) → Fin (n a) → Fin (N a))
    (hf : FactorInjective f) (x y : Vertex n) :
    Decode f x = Decode f y ↔ x = y := by
  constructor
  · intro h
    funext a
    exact hf a _ _ (congrFun h a)
  · intro h
    exact congrArg (Decode f) h

theorem coordinate_step_iff {q : Nat} {n N : Fin q → Nat}
    (f : (a : Fin q) → Fin (n a) → Fin (N a))
    (hf : FactorInjective f) (a : Fin q) (x y : Vertex n) :
    CoordinateStep a (Decode f x) (Decode f y) ↔ CoordinateStep a x y := by
  constructor
  · rintro ⟨hne, heq⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hne (congrArg (f a) h)
    · intro b hb
      exact hf b _ _ (heq b hb)
  · rintro ⟨hne, heq⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hne (hf a _ _ h)
    · intro b hb
      exact congrArg (f b) (heq b hb)

theorem coordinate_axis_unique {q : Nat} {n : Fin q → Nat}
    (a b : Fin q) (x y : Vertex n)
    (ha : CoordinateStep a x y) (hb : CoordinateStep b x y) : a = b := by
  by_cases h : a = b
  · exact h
  · exact False.elim (ha.1 (hb.2 a h))

theorem cartesian_adj_preserved {q : Nat} {n N : Fin q → Nat}
    (f : (a : Fin q) → Fin (n a) → Fin (N a)) (hf : FactorInjective f)
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (target : (a : Fin q) → Fin (N a) → Fin (N a) → Prop)
    (preserve : ∀ a u v, edge a u v → target a (f a u) (f a v))
    (x y : Vertex n) (h : CartesianAdj edge x y) :
    CartesianAdj target (Decode f x) (Decode f y) := by
  obtain ⟨a, he, hs⟩ := h
  exact ⟨a, preserve a _ _ he, (coordinate_step_iff f hf a x y).2 hs⟩

def TraceInjective {m q : Nat} {n : Fin q → Nat}
    (v : Fin m → Vertex n) : Prop :=
  ∀ s t, v s = v t → s = t

theorem trace_injective_iff {m q : Nat} {n N : Fin q → Nat}
    (f : (a : Fin q) → Fin (n a) → Fin (N a)) (hf : FactorInjective f)
    (shape : Fin m → Vertex n) :
    TraceInjective (fun t => Decode f (shape t)) ↔ TraceInjective shape := by
  constructor
  · intro h s t heq
    exact h s t ((decode_equal_iff f hf _ _).2 heq)
  · intro h s t heq
    exact h s t ((decode_equal_iff f hf _ _).1 heq)

def UsedCoordinate {m q : Nat} {n : Fin q → Nat}
    (v : Fin m → Vertex n) (a : Fin q) : Prop :=
  ∃ s t, v s a ≠ v t a

theorem used_coordinate_iff {m q : Nat} {n N : Fin q → Nat}
    (f : (a : Fin q) → Fin (n a) → Fin (N a)) (hf : FactorInjective f)
    (shape : Fin m → Vertex n) (a : Fin q) :
    UsedCoordinate (fun t => Decode f (shape t)) a ↔ UsedCoordinate shape a := by
  constructor
  · rintro ⟨s, t, h⟩
    exact ⟨s, t, fun heq => h (congrArg (f a) heq)⟩
  · rintro ⟨s, t, h⟩
    exact ⟨s, t, fun heq => h (hf a _ _ heq)⟩

def Next {m : Nat} (hm : 0 < m) (t : Fin m) : Fin m :=
  ⟨(t.val + 1) % m, Nat.mod_lt _ hm⟩

def CycleEmbedding {m q : Nat} {n : Fin q → Nat} (hm : 0 < m)
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (v : Fin m → Vertex n) : Prop :=
  3 ≤ m ∧ TraceInjective v ∧ ∀ t, CartesianAdj edge (v t) (v (Next hm t))

/- A prescribed closed shape must already have the required label edges.
   Only preservation of those edges is assumed; nonedges need not be preserved. -/
theorem decoded_cycle_iff {m q : Nat} {n N : Fin q → Nat} (hm : 0 < m)
    (f : (a : Fin q) → Fin (n a) → Fin (N a)) (hf : FactorInjective f)
    (edge : (a : Fin q) → Fin (n a) → Fin (n a) → Prop)
    (target : (a : Fin q) → Fin (N a) → Fin (N a) → Prop)
    (preserve : ∀ a u v, edge a u v → target a (f a u) (f a v))
    (shape : Fin m → Vertex n)
    (closedShape : ∀ t, CartesianAdj edge (shape t) (shape (Next hm t))) :
    CycleEmbedding hm target (fun t => Decode f (shape t)) ↔
      CycleEmbedding hm edge shape := by
  constructor
  · rintro ⟨hlen, hinj, _⟩
    exact ⟨hlen, (trace_injective_iff f hf shape).1 hinj, closedShape⟩
  · rintro ⟨hlen, hinj, hstep⟩
    refine ⟨hlen, (trace_injective_iff f hf shape).2 hinj, ?_⟩
    intro t
    exact cartesian_adj_preserved f hf edge target preserve _ _ (hstep t)

/- Factor injections are recoverable when the shape actually uses every label.
   This is the fixed-pattern no-overcount component, not canonical extraction. -/
theorem assignments_recovered {m q : Nat} {n N : Fin q → Nat}
    (shape : Fin m → Vertex n)
    (usedLabels : ∀ a (label : Fin (n a)), ∃ t, shape t a = label)
    (f g : (a : Fin q) → Fin (n a) → Fin (N a))
    (sameTrace : (fun t => Decode f (shape t)) = (fun t => Decode g (shape t))) :
    f = g := by
  funext a label
  obtain ⟨t, ht⟩ := usedLabels a label
  have heq := congrFun (congrFun sameTrace t) a
  change f a (shape t a) = g a (shape t a) at heq
  simpa only [ht] using heq

#print axioms decode_equal_iff
#print axioms coordinate_step_iff
#print axioms coordinate_axis_unique
#print axioms cartesian_adj_preserved
#print axioms trace_injective_iff
#print axioms used_coordinate_iff
#print axioms decoded_cycle_iff
#print axioms assignments_recovered

end ECC.CollisionBridge
