import CollisionBridge
import MatchingLabels

namespace ECC.MotifTransport
open CollisionBridge MatchingLabels

def maps : (q n : Nat) → List (Fin q → Fin n)
  | 0, _ => [fun i => Fin.elim0 i]
  | q+1, n => (List.ofFn (fun i : Fin n => i)).flatMap fun a =>
      (maps q n).map (Fin.cases a)

theorem mem_maps {q n} (f : Fin q → Fin n) : f ∈ maps q n := by
  induction q with
  | zero =>
    have he : f = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
    simp only [maps, List.mem_singleton, he]
  | succ q ih =>
    apply List.mem_flatMap.2
    refine ⟨f 0, List.mem_ofFn.2 ⟨f 0, rfl⟩, ?_⟩
    apply List.mem_map.2
    refine ⟨fun i => f i.succ, ih _, ?_⟩
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem maps_nodup (q n : Nat) : (maps q n).Nodup := by
  induction q with
  | zero => simp only [maps, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self]
  | succ q ih =>
    change List.Pairwise (· ≠ ·) ((List.ofFn (fun i : Fin n => i)).flatMap _)
    rw [List.pairwise_flatMap]
    constructor
    · intro a _
      rw [List.pairwise_map]
      exact ih.imp (fun {f g} h he => h (by funext i; exact congrFun he i.succ))
    · have hn : (List.ofFn (fun i : Fin n => i)).Nodup := by
        apply List.nodup_iff_eq_of_getElem_eq.2
        intro i j hi hj he
        have heq : (⟨i, by simpa only [List.length_ofFn] using hi⟩ : Fin n) =
            ⟨j, by simpa only [List.length_ofFn] using hj⟩ := by
          simpa only [List.getElem_ofFn] using he
        exact congrArg Fin.val heq
      exact hn.imp (fun {a b} hab => by
        intro f hf g hg he
        obtain ⟨u, _, hu⟩ := List.mem_map.1 hf
        obtain ⟨v, _, hv⟩ := List.mem_map.1 hg
        have h0 := congrFun (hu.trans (he.trans hv.symm)) 0
        exact hab h0)

theorem maps_length (q n : Nat) : (maps q n).length = n^q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [maps, flatMap_constant_length _ _ (n^q), List.length_ofFn]
    · rw [Nat.pow_succ, Nat.mul_comm]
    · intro a _
      rw [List.length_map, ih]

def Aut {n} (edge : Fin n → Fin n → Bool) (f : Fin n → Fin n) : Prop :=
  (∀ a b, f a = f b → a = b) ∧ ∀ a b, edge (f a) (f b) = edge a b
instance {n} (edge : Fin n → Fin n → Bool) (f : Fin n → Fin n) : Decidable (Aut edge f) :=
  inferInstanceAs (Decidable ((∀ a b, f a = f b → a = b) ∧ ∀ a b, edge (f a) (f b) = edge a b))

def autos {n} (edge : Fin n → Fin n → Bool) : List (Fin n → Fin n) :=
  (maps n n).filter fun f => decide (Aut edge f)

theorem mem_autos {n} (edge : Fin n → Fin n → Bool) (f) :
    f ∈ autos edge ↔ Aut edge f := by
  simp only [autos, List.mem_filter, decide_eq_true_eq, mem_maps, true_and]

def edge : Fin 2 → Fin 2 → Bool := fun a b => decide (a ≠ b)
def wedge : Fin 3 → Fin 3 → Bool := fun a b =>
  decide ((a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0))
def square : Fin 4 → Fin 4 → Bool := fun a b =>
  decide ((a.val+1)%4 = b.val ∨ (b.val+1)%4 = a.val)
def triangle : Fin 3 → Fin 3 → Bool := fun a b => decide (a ≠ b)

theorem motif_automorphisms :
    (autos edge).length = 2 ∧ (autos wedge).length = 2 ∧
    (autos square).length = 8 ∧ (autos triangle).length = 6 := by decide

-- The copy is selected: extra edges in the host do not enter this condition.
def assignments {n N} (edge : Fin n → Fin n → Bool) (copy : Fin n → Fin N) :
    List (Fin n → Fin N) := (autos edge).map fun a i => copy (a i)

theorem assignments_length {n N} (edge : Fin n → Fin n → Bool) (copy : Fin n → Fin N) :
    (assignments edge copy).length = (autos edge).length := by
  unfold assignments
  rw [List.length_map]

theorem assignments_nodup {n N} (edge : Fin n → Fin n → Bool) (copy : Fin n → Fin N)
    (hi : ∀ a b, copy a = copy b → a = b) : (assignments edge copy).Nodup := by
  unfold assignments
  change List.Pairwise (· ≠ ·) ((autos edge).map _)
  rw [List.pairwise_map]
  exact ((maps_nodup n n).filter _).imp (fun {a b} hab he =>
    hab (by funext i; exact hi _ _ (congrFun he i)))

-- Any second labeling of exactly the same selected copy is recovered uniquely
-- by a supplied inverse of its finite vertex labeling. No choice is used.
theorem selected_copy_factorization {n N} (edge : Fin n → Fin n → Bool)
    (copy : Fin n → Fin N) (decode : Fin N → Fin n)
    (hd : ∀ i, decode (copy i) = i) (f : Fin n → Fin N)
    (hrange : ∀ i, copy (decode (f i)) = f i)
    (hinj : ∀ i j, f i = f j → i = j)
    (hedge : ∀ i j, edge (decode (f i)) (decode (f j)) = edge i j) :
    f ∈ assignments edge copy ∧
      ∀ a, Aut edge a → (∀ i, copy (a i) = f i) → a = fun i => decode (f i) := by
  constructor
  · apply List.mem_map.2
    refine ⟨fun i => decode (f i), (mem_autos edge _).2 ⟨?_, hedge⟩, ?_⟩
    · intro i j he
      apply hinj
      change decode (f i) = decode (f j) at he
      rw [← hrange i, ← hrange j, he]
    · funext i
      exact hrange i
  · intro a _ he
    funext i
    have h := congrArg decode (he i)
    simpa only [hd] using h

-- Four closed steps admit exactly edge / the two wedge roots / square.
theorem four_step_partition {A : Type} [DecidableEq A] (a b c d : A)
    (_ab : a ≠ b) (_bc : b ≠ c) (_cd : c ≠ d) (_da : d ≠ a) :
    (a = c ∧ b = d) ∨ (a = c ∧ b ≠ d) ∨
    (a ≠ c ∧ b = d) ∨ (a ≠ c ∧ b ≠ d) := by
  by_cases hac : a = c <;> by_cases hbd : b = d
  · exact Or.inl ⟨hac, hbd⟩
  · exact Or.inr (Or.inl ⟨hac, hbd⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hac, hbd⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hac, hbd⟩))

theorem square_vertices_distinct {A : Type} (a b c d : A)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d) : [a,b,c,d].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true, not_or]
  exact ⟨⟨hab, hac, Ne.symm hda⟩, ⟨hbc, hbd⟩, hcd⟩

theorem triangle_vertices_distinct {A : Type} (a b c : A)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : [a,b,c].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true, not_or]
  exact ⟨⟨hab, Ne.symm hca⟩, hbc⟩

-- Product transport, including inactive coordinates modeled by one label.
theorem selected_product_transport {L q} {n N : Fin q → Nat}
    (copy : (a : Fin q) → Fin (n a) → Fin (N a)) (hi : FactorInjective copy)
    (shape : Fin L → Vertex n) :
    TraceInjective (fun t => Decode copy (shape t)) ↔ TraceInjective shape :=
  trace_injective_iff copy hi shape

#print axioms mem_maps
#print axioms maps_nodup
#print axioms maps_length
#print axioms mem_autos
#print axioms motif_automorphisms
#print axioms assignments_length
#print axioms assignments_nodup
#print axioms selected_copy_factorization
#print axioms four_step_partition
#print axioms square_vertices_distinct
#print axioms triangle_vertices_distinct
#print axioms selected_product_transport
end ECC.MotifTransport
