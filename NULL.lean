import NULL.Basic
import Mathlib
open Equiv

-- Week 3

def IsComm (x : ℝ) (y : ℝ) : Prop :=
  x + y = y + x

example (x y : ℝ) : IsComm x y := by
  unfold IsComm
  exact AddCommMagma.add_comm x y

def IsEven (n : ℕ) : Prop :=
  ∃ (m: ℕ), n = 2 * m

lemma EvenPlusEven (x : ℕ) (y : ℕ) :
  IsEven x ∧ IsEven y → IsEven (x + y) := by
    simp[IsEven]
    intro x_1
    intro hx_1
    intro x_2
    intro hx_2
    use (x_1 + x_2)
    rw[hx_1, hx_2]
    ring

 -- Write IsOdd

 def IsOdd (n : ℕ) : Prop :=
  ∃ (m : ℕ), n = 2 * m + 1

 -- Write OddPlusOdd

lemma OddPlusOdd (x : ℕ) (y : ℕ) :
  IsOdd x ∧ IsOdd y → IsEven (x + y) := by
    simp[IsOdd]
    intro x_1
    intro hx_1
    intro x_2
    intro hx_2
    use (x_1 + x_2 + 1)
    rw[hx_1, hx_2]
    ring

example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl h =>
    exact Or.inr h
  | inr h =>
    exact Or.inl h

-- Week 4

-- Prove that for all n∈ℕ, n^2-n is even
-- Even n

example (n : ℕ) : Even (n^2 - n):= by
  cases Nat.even_or_odd n with
  | inl h_even =>
    unfold Even at *
    obtain ⟨r, hr⟩ := h_even
    use (2 * r^2 - r)
    rw [hr]
    ring_nf
    omega

  | inr h_odd =>
    unfold Even
    unfold Odd at h_odd
    obtain ⟨r, hr⟩ := h_odd
    use (2 * r^2 + r)
    rw [hr]
    ring_nf
    omega


-- Week 5

def add_nat : ℕ → ℕ
  | 0 => 0
  | n + 1 => add_nat n + n + 1


theorem sum_of_nat (n : ℕ) : add_nat n = n * (n + 1) / 2 := by
  -- type "induction n with" and wait for the lightbulb to pop up
  induction n with
  | zero => exact rfl
  | succ n hn =>
    rw[add_nat, hn]
    ring_nf
    omega

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_pos (n : ℕ) : 0 < factorial n := by
  induction n with
  | zero =>
    exact Nat.zero_lt_succ 0
  | succ n _ =>
    rw[factorial]
    (expose_names; exact Nat.succ_mul_pos n h)


theorem dvd_factorial {i n : ℕ} (i_pos : 0 < i) (i_le : i ≤ n) : i ∣ factorial n := by
  induction n with
  | zero =>
    omega
  | succ n _ =>
    rw[factorial]
    have h : (i = n + 1) ∨ (i ≤ n) := by
      exact Nat.le_succ_iff_eq_or_le.mp i_le
    cases h with
    | inl h => exact Dvd.intro (factorial n) (congrFun (congrArg HMul.hMul h) (factorial n))
    | inr h => (expose_names; exact Nat.dvd_mul_left_of_dvd (h_1 h) (n + 1))

-- Week 6

def fun_name (x_0 : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | f x_0 = 0}
  zero_mem' := by
    exact rfl
  add_mem' := by
    intro a b
    simp
    intro hx hy
    rw [hx, hy]
    rw [add_zero]
  smul_mem' := by
    intro c f hx
    have H: c • f x_0 = 0 := by
      exact smul_eq_zero_of_right c hx
    exact H



-- Week 7
abbrev addRight (a : ℝ) : Perm ℝ where
  toFun := fun x ↦ x + a
  invFun := fun x ↦ x - a
  left_inv := by
    dsimp [Function.LeftInverse]
    ring_nf
    simp
  right_inv := by
    dsimp [Function.RightInverse]
    dsimp [Function.LeftInverse]
    ring_nf
    simp

example (a : ℝ) :
    let α := addRight a
    ∀ x y, x - y = α x - α y := by
      dsimp [addRight]
      ring_nf
      simp

abbrev halfTurn (a : ℝ) : Perm ℝ where
  toFun := fun x ↦ -x + a
  invFun := fun x ↦ -x + a
  left_inv := by
    dsimp [Function.LeftInverse]
    ring_nf
    simp
  right_inv := by
    dsimp [Function.RightInverse]
    dsimp [Function.LeftInverse]
    ring_nf
    simp

example (a : ℝ) :
    let α := halfTurn a
    {x | α x = x} = {a / 2} := by
      dsimp [halfTurn]
      ext y
      constructor
      · intro h
        simp at *
        linarith
      · intro h
        simp at *
        linarith


-- Week 8

def PosReal := {x : ℝ // x > 0}

structure Rectangle where
  mk ::
  base : PosReal
  height : PosReal

def Rectangle.area (R : Rectangle) :=
  R.base.val * R.height.val


-- Alternative method

structure PosR extends ℝ where
  positivity : toReal > 0

structure FreeRect where
  base : PosR
  height : PosR

def area_rect (r : FreeRect) :=
  (r.base.toReal) * (r.height.toReal)

example : FreeRect where
  base := ⟨2, by simp⟩
  height := ⟨1, by simp⟩


structure Point where
  mk ::
  x : ℝ
  y : ℝ

def Point.Distance (P Q : Point) : ℝ :=
  ((P.x - Q.x) ^ 2 + (P.y - Q.y) ^ 2) ^ (1/2)

def Point.Dot_product (P Q : Point) :=
  P.x * Q.x + P.y * Q.y

noncomputable def Point.Slope_Segment (P Q : Point) : Option ℝ :=
  if P.x = Q.x then
    none
  else
    some ((Q.y - P.y) / (Q.x - P.x))

structure Quad where
  a : Point
  b : Point
  c : Point
  d : Point

structure Parallelogram extends Quad where
  equal_length : Point.Distance toQuad.a toQuad.b = Point.Distance toQuad.c toQuad.d
  segment_1_parallel : Point.Slope_Segment toQuad.a toQuad.b = Point.Slope_Segment toQuad.c toQuad.d
  segment_2_parallel : Point.Slope_Segment toQuad.a toQuad.d = Point.Slope_Segment toQuad.b toQuad.c

structure Trect extends Parallelogram where
  right_angle : Point.Dot_product toQuad.a toQuad.b = 0

-- Make a Parallelogram

-- Define rectangle as parallelogram with 90 degree angles
