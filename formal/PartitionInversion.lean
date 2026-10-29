import Std

/- Finite quotient factorization and finite inversion transport. The numerical
   partition Mobius cancellation identity is NOT assumed proved by this file;
   it is the explicit hcancel hypothesis, checked exhaustively through Pi_10
   in the separate experiment. No coordinate shuffles enter this interface. -/
namespace ECC.PartitionInversion

def ConstantOn {I B V : Type} (rho : I → B) (t : I → V) : Prop :=
  ∀ i j, rho i = rho j → t i = t j

def Injective {I V : Type} (t : I → V) : Prop :=
  ∀ i j, t i = t j → i = j

theorem factor_constant {I B V : Type} (rho : I → B) (g : B → V) :
    ConstantOn rho (fun i => g (rho i)) := by
  intro i j h
  exact congrArg g h

theorem quotient_factorization {I B V : Type} (rho : I → B) (rep : B → I)
    (hrep : ∀ b, rho (rep b) = b) (t : I → V) :
    ConstantOn rho t ↔ ∃ g : B → V, ∀ i, g (rho i) = t i := by
  constructor
  · intro h
    exact ⟨fun b => t (rep b), fun i => h _ _ (hrep (rho i))⟩
  · rintro ⟨g, hg⟩ i j hij
    rw [← hg i, ← hg j, hij]

theorem quotient_unique {I B V : Type} (rho : I → B) (rep : B → I)
    (hrep : ∀ b, rho (rep b) = b) (g h : B → V)
    (heq : ∀ i, g (rho i) = h (rho i)) : g = h := by
  funext b
  have := heq (rep b)
  simpa only [hrep] using this

theorem kernel_discrete_iff {I V : Type} (t : I → V) :
    (∀ i j, t i = t j ↔ i = j) ↔ Injective t := by
  constructor
  · intro h i j hij
    exact (h i j).1 hij
  · intro h i j
    constructor
    · exact h i j
    · intro hij
      rw [hij]

theorem quotient_loop_obstruction {I B V : Type} (rho : I → B) (g : B → V)
    (adj : V → V → Prop) (loopless : ∀ v, ¬ adj v v)
    (i j : I) (collapse : rho i = rho j) :
    ¬ adj (g (rho i)) (g (rho j)) := by
  rw [collapse]
  exact loopless _

def isum {A : Type} (xs : List A) (f : A → Int) : Int :=
  match xs with
  | [] => 0
  | x :: rest => f x + isum rest f

theorem isum_add {A : Type} (xs : List A) (f g : A → Int) :
    isum xs (fun x => f x + g x) = isum xs f + isum xs g := by
  induction xs with
  | nil => simp [isum]
  | cons x xs ih => simp [isum, ih, Int.add_assoc, Int.add_left_comm]

theorem isum_mul {A : Type} (xs : List A) (w : Int) (f : A → Int) :
    isum xs (fun x => w * f x) = w * isum xs f := by
  induction xs with
  | nil => simp [isum]
  | cons x xs ih => simp [isum, ih, Int.mul_add]

theorem isum_swap {A B : Type} (xs : List A) (ys : List B) (f : A → B → Int) :
    isum xs (fun x => isum ys (fun y => f x y)) =
      isum ys (fun y => isum xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    induction ys with
    | nil => rfl
    | cons y ys ih => simpa [isum] using ih
  | cons x xs ih =>
    simp only [isum, ih, isum_add]

theorem isum_congr {A : Type} (xs : List A) (f g : A → Int)
    (h : ∀ x, f x = g x) : isum xs f = isum xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [isum, h x, ih]

/- compatibility is a finite 0/1 indicator in the application. hcancel must
   supply the actual partition weights and the complete partition list. -/
theorem finite_inversion {P W : Type} (ps : List P) (ws : List W)
    (mu : P → Int) (compatible : P → W → Int) (injective : W → Int)
    (hcancel : ∀ w, isum ps (fun p => mu p * compatible p w) = injective w) :
    isum ps (fun p => mu p * isum ws (fun w => compatible p w)) =
      isum ws injective := by
  calc
    _ = isum ps (fun p => isum ws (fun w => mu p * compatible p w)) := by
      apply isum_congr
      intro p
      exact (isum_mul ws (mu p) (compatible p)).symm
    _ = isum ws (fun w => isum ps (fun p => mu p * compatible p w)) :=
      isum_swap ps ws _
    _ = isum ws injective := isum_congr ws _ _ hcancel

/- Concrete repeated-product-vertex and rooted-quotient controls. -/
theorem repeated_edge_cancellation : (2 : Int) + (-1) * 2 = 0 := by decide

theorem rooted_c10_quotient :
    1805760 / 20 = 90288 ∧ 1805760 / 10 = 180576 ∧ 90288 % 20 = 8 := by decide

#print axioms factor_constant
#print axioms quotient_factorization
#print axioms quotient_unique
#print axioms kernel_discrete_iff
#print axioms quotient_loop_obstruction
#print axioms isum_add
#print axioms isum_mul
#print axioms isum_swap
#print axioms isum_congr
#print axioms finite_inversion
#print axioms repeated_edge_cancellation
#print axioms rooted_c10_quotient
end ECC.PartitionInversion
