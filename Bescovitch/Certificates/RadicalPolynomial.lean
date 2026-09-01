/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.RadicalInterval
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.GetD

/-!
# Dense polynomials with exact radical coefficients

The three nested coefficient lists record increasing powers in three scalar variables.
Their coefficients are exact radical expressions, so interval enclosures can later be checked
without replacing the algebraic endpoint data by decimal constants.
-/

@[expose] public section

namespace Bescovitch

/-- A dense univariate polynomial with radical-expression coefficients. -/
abbrev RadicalUnivariate (n : ℕ) := List (RadicalExpression n)

namespace RadicalUnivariate

/-- Add two dense coefficient lists, padding the shorter list by zero. -/
def add {n : ℕ} : RadicalUnivariate n → RadicalUnivariate n → RadicalUnivariate n
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => .add a b :: add p q

/-- Negate every coefficient. -/
def neg {n : ℕ} (p : RadicalUnivariate n) : RadicalUnivariate n :=
  p.map .neg

/-- Multiply every coefficient by an exact scalar expression. -/
def scale {n : ℕ} (a : RadicalExpression n) (p : RadicalUnivariate n) :
    RadicalUnivariate n :=
  p.map (.mul a)

/-- Multiply dense univariate polynomials by coefficient convolution. -/
def mul {n : ℕ} : RadicalUnivariate n → RadicalUnivariate n → RadicalUnivariate n
  | [], _ => []
  | a :: p, q => add (scale a q) (.constant 0 :: mul p q)

/-- A constant univariate polynomial. -/
def constant {n : ℕ} (a : RadicalExpression n) : RadicalUnivariate n := [a]

/-- The univariate indeterminate. -/
def indeterminate {n : ℕ} : RadicalUnivariate n := [.constant 0, .constant 1]

/-- Natural powers of a univariate polynomial. -/
def pow {n : ℕ} (p : RadicalUnivariate n) : ℕ → RadicalUnivariate n
  | 0 => constant (.constant 1)
  | k + 1 => mul (pow p k) p

/-- Evaluate by Horner's rule after evaluating the exact coefficients. -/
noncomputable def eval {n : ℕ} : RadicalUnivariate n → (Fin n → ℝ) → ℝ → ℝ
  | [], _, _ => 0
  | a :: p, input, x => a.eval input + x * eval p input x

theorem eval_add {n : ℕ} (p q : RadicalUnivariate n) (input : Fin n → ℝ) (x : ℝ) :
    eval (add p q) input x = eval p input x + eval q input x := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p hp =>
      cases q with
      | nil => simp [add, eval]
      | cons b q => simp [add, eval, hp, RadicalExpression.eval]; ring

theorem eval_neg {n : ℕ} (p : RadicalUnivariate n) (input : Fin n → ℝ) (x : ℝ) :
    eval (neg p) input x = -eval p input x := by
  induction p with
  | nil => simp [neg, eval]
  | cons a p hp =>
      simp only [neg] at hp
      simp [neg, eval, hp, RadicalExpression.eval]
      ring

theorem eval_scale {n : ℕ} (a : RadicalExpression n) (p : RadicalUnivariate n)
    (input : Fin n → ℝ) (x : ℝ) :
    eval (scale a p) input x = a.eval input * eval p input x := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p hp =>
      simp only [scale] at hp
      simp [scale, eval, hp, RadicalExpression.eval]
      ring

theorem eval_mul {n : ℕ} (p q : RadicalUnivariate n) (input : Fin n → ℝ) (x : ℝ) :
    eval (mul p q) input x = eval p input x * eval q input x := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p hp => simp [mul, eval, eval_add, eval_scale, hp, RadicalExpression.eval]; ring

@[simp] theorem eval_constant {n : ℕ} (a : RadicalExpression n) (input : Fin n → ℝ)
    (x : ℝ) : eval (constant a) input x = a.eval input := by
  simp [constant, eval]

@[simp] theorem eval_indeterminate {n : ℕ} (input : Fin n → ℝ) (x : ℝ) :
    eval indeterminate input x = x := by
  simp [indeterminate, eval, RadicalExpression.eval]

theorem eval_pow {n : ℕ} (p : RadicalUnivariate n) (k : ℕ) (input : Fin n → ℝ)
    (x : ℝ) : eval (pow p k) input x = eval p input x ^ k := by
  induction k with
  | zero => simp [pow, RadicalExpression.eval]
  | succ k hk => simp [pow, eval_mul, hk, pow_succ]

/-- Horner evaluation equals the padded power sum. -/
theorem eval_eq_sum_getD {n N : ℕ} (p : RadicalUnivariate n) (h : p.length ≤ N)
    (input : Fin n → ℝ) (x : ℝ) :
    eval p input x = ∑ i : Fin N, (p.getD i (.constant 0)).eval input * x ^ (i : ℕ) := by
  induction N generalizing p with
  | zero =>
      have hp : p = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
      subst p
      simp [eval]
  | succ N ih =>
      cases p with
      | nil => simp [eval, RadicalExpression.eval]
      | cons a p =>
          rw [Fin.sum_univ_succ]
          simp only [List.getD_cons_zero, Fin.val_zero, pow_zero, mul_one]
          rw [eval]
          have hp : p.length ≤ N := by simpa using h
          rw [ih p hp]
          simp only [Fin.val_succ, List.getD_cons_succ]
          rw [Finset.mul_sum]
          apply congrArg (a.eval input + ·)
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ]
          ring

end RadicalUnivariate

/-- A dense bivariate polynomial with radical-expression coefficients. -/
abbrev RadicalBivariate (n : ℕ) := List (RadicalUnivariate n)

namespace RadicalBivariate

/-- Add two dense bivariate polynomials. -/
def add {n : ℕ} : RadicalBivariate n → RadicalBivariate n → RadicalBivariate n
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => RadicalUnivariate.add a b :: add p q

/-- Negate every coefficient row. -/
def neg {n : ℕ} (p : RadicalBivariate n) : RadicalBivariate n :=
  p.map RadicalUnivariate.neg

/-- Multiply every outer coefficient by a univariate row. -/
def scaleRow {n : ℕ} (a : RadicalUnivariate n) (p : RadicalBivariate n) :
    RadicalBivariate n :=
  p.map (RadicalUnivariate.mul a)

/-- Multiply dense bivariate polynomials by coefficient convolution. -/
def mul {n : ℕ} : RadicalBivariate n → RadicalBivariate n → RadicalBivariate n
  | [], _ => []
  | a :: p, q => add (scaleRow a q) ([] :: mul p q)

/-- A constant bivariate polynomial. -/
def constant {n : ℕ} (a : RadicalExpression n) : RadicalBivariate n := [[a]]

/-- The first bivariate indeterminate. -/
def first {n : ℕ} : RadicalBivariate n := [[], [.constant 1]]

/-- The second bivariate indeterminate. -/
def second {n : ℕ} : RadicalBivariate n := [[.constant 0, .constant 1]]

/-- Natural powers of a bivariate polynomial. -/
def pow {n : ℕ} (p : RadicalBivariate n) : ℕ → RadicalBivariate n
  | 0 => constant (.constant 1)
  | k + 1 => mul (pow p k) p

/-- Evaluate by nested Horner rules. -/
noncomputable def eval {n : ℕ} :
    RadicalBivariate n → (Fin n → ℝ) → ℝ → ℝ → ℝ
  | [], _, _, _ => 0
  | a :: p, input, x, y => RadicalUnivariate.eval a input y + x * eval p input x y

theorem eval_add {n : ℕ} (p q : RadicalBivariate n) (input : Fin n → ℝ) (x y : ℝ) :
    eval (add p q) input x y = eval p input x y + eval q input x y := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p hp =>
      cases q with
      | nil => simp [add, eval]
      | cons b q => simp [add, eval, RadicalUnivariate.eval_add, hp]; ring

theorem eval_neg {n : ℕ} (p : RadicalBivariate n) (input : Fin n → ℝ) (x y : ℝ) :
    eval (neg p) input x y = -eval p input x y := by
  induction p with
  | nil => simp [neg, eval]
  | cons a p hp =>
      simp only [neg] at hp
      simp [neg, eval, RadicalUnivariate.eval_neg, hp]
      ring

theorem eval_scaleRow {n : ℕ} (a : RadicalUnivariate n) (p : RadicalBivariate n)
    (input : Fin n → ℝ) (x y : ℝ) :
    eval (scaleRow a p) input x y =
      RadicalUnivariate.eval a input y * eval p input x y := by
  induction p with
  | nil => simp [scaleRow, eval]
  | cons b p hp =>
      simp only [scaleRow] at hp
      simp [scaleRow, eval, RadicalUnivariate.eval_mul, hp]
      ring

theorem eval_mul {n : ℕ} (p q : RadicalBivariate n) (input : Fin n → ℝ) (x y : ℝ) :
    eval (mul p q) input x y = eval p input x y * eval q input x y := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p hp => simp [mul, eval, eval_add, eval_scaleRow, hp, RadicalUnivariate.eval]; ring

@[simp] theorem eval_constant {n : ℕ} (a : RadicalExpression n) (input : Fin n → ℝ)
    (x y : ℝ) : eval (constant a) input x y = a.eval input := by
  simp [constant, eval, RadicalUnivariate.eval]

@[simp] theorem eval_first {n : ℕ} (input : Fin n → ℝ) (x y : ℝ) :
    eval first input x y = x := by
  simp [first, eval, RadicalUnivariate.eval, RadicalExpression.eval]

@[simp] theorem eval_second {n : ℕ} (input : Fin n → ℝ) (x y : ℝ) :
    eval second input x y = y := by
  simp [second, eval, RadicalUnivariate.eval, RadicalExpression.eval]

theorem eval_pow {n : ℕ} (p : RadicalBivariate n) (k : ℕ) (input : Fin n → ℝ)
    (x y : ℝ) : eval (pow p k) input x y = eval p input x y ^ k := by
  induction k with
  | zero => simp [pow, RadicalExpression.eval]
  | succ k hk => simp [pow, eval_mul, hk, pow_succ]

/-- Horner evaluation in the first variable equals the padded power sum. -/
theorem eval_eq_sum_getD {n N : ℕ} (p : RadicalBivariate n) (h : p.length ≤ N)
    (input : Fin n → ℝ) (x y : ℝ) :
    eval p input x y =
      ∑ i : Fin N, RadicalUnivariate.eval (p.getD i []) input y * x ^ (i : ℕ) := by
  induction N generalizing p with
  | zero =>
      have hp : p = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
      subst p
      simp [eval]
  | succ N ih =>
      cases p with
      | nil => simp [eval, RadicalUnivariate.eval]
      | cons a p =>
          rw [Fin.sum_univ_succ]
          simp only [List.getD_cons_zero, Fin.val_zero, pow_zero, mul_one]
          rw [eval]
          have hp : p.length ≤ N := by simpa using h
          rw [ih p hp]
          simp only [Fin.val_succ, List.getD_cons_succ]
          rw [Finset.mul_sum]
          apply congrArg (RadicalUnivariate.eval a input y + ·)
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ]
          ring

end RadicalBivariate

/-- A dense trivariate polynomial with radical-expression coefficients. -/
abbrev RadicalTrivariate (n : ℕ) := List (RadicalBivariate n)

namespace RadicalTrivariate

/-- Add two dense trivariate polynomials. -/
def add {n : ℕ} : RadicalTrivariate n → RadicalTrivariate n → RadicalTrivariate n
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => RadicalBivariate.add a b :: add p q

/-- Negate every coefficient slice. -/
def neg {n : ℕ} (p : RadicalTrivariate n) : RadicalTrivariate n :=
  p.map RadicalBivariate.neg

/-- Multiply every outer coefficient by a bivariate slice. -/
def scaleSlice {n : ℕ} (a : RadicalBivariate n) (p : RadicalTrivariate n) :
    RadicalTrivariate n :=
  p.map (RadicalBivariate.mul a)

/-- Multiply dense trivariate polynomials by coefficient convolution. -/
def mul {n : ℕ} : RadicalTrivariate n → RadicalTrivariate n → RadicalTrivariate n
  | [], _ => []
  | a :: p, q => add (scaleSlice a q) ([] :: mul p q)

/-- A constant trivariate polynomial. -/
def constant {n : ℕ} (a : RadicalExpression n) : RadicalTrivariate n := [[[a]]]

/-- The first trivariate indeterminate. -/
def first {n : ℕ} : RadicalTrivariate n := [[], [[.constant 1]]]

/-- The second trivariate indeterminate. -/
def second {n : ℕ} : RadicalTrivariate n := [[[], [.constant 1]]]

/-- The third trivariate indeterminate. -/
def third {n : ℕ} : RadicalTrivariate n := [[[.constant 0, .constant 1]]]

/-- Natural powers of a trivariate polynomial. -/
def pow {n : ℕ} (p : RadicalTrivariate n) : ℕ → RadicalTrivariate n
  | 0 => constant (.constant 1)
  | k + 1 => mul (pow p k) p

/-- Evaluate by three nested Horner rules. -/
noncomputable def eval {n : ℕ} :
    RadicalTrivariate n → (Fin n → ℝ) → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _ => 0
  | a :: p, input, x, y, z =>
      RadicalBivariate.eval a input y z + x * eval p input x y z

theorem eval_add {n : ℕ} (p q : RadicalTrivariate n) (input : Fin n → ℝ)
    (x y z : ℝ) : eval (add p q) input x y z = eval p input x y z + eval q input x y z := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p hp =>
      cases q with
      | nil => simp [add, eval]
      | cons b q => simp [add, eval, RadicalBivariate.eval_add, hp]; ring

theorem eval_neg {n : ℕ} (p : RadicalTrivariate n) (input : Fin n → ℝ)
    (x y z : ℝ) : eval (neg p) input x y z = -eval p input x y z := by
  induction p with
  | nil => simp [neg, eval]
  | cons a p hp =>
      simp only [neg] at hp
      simp [neg, eval, RadicalBivariate.eval_neg, hp]
      ring

theorem eval_scaleSlice {n : ℕ} (a : RadicalBivariate n) (p : RadicalTrivariate n)
    (input : Fin n → ℝ) (x y z : ℝ) :
    eval (scaleSlice a p) input x y z =
      RadicalBivariate.eval a input y z * eval p input x y z := by
  induction p with
  | nil => simp [scaleSlice, eval]
  | cons b p hp =>
      simp only [scaleSlice] at hp
      simp [scaleSlice, eval, RadicalBivariate.eval_mul, hp]
      ring

theorem eval_mul {n : ℕ} (p q : RadicalTrivariate n) (input : Fin n → ℝ)
    (x y z : ℝ) : eval (mul p q) input x y z = eval p input x y z * eval q input x y z := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p hp =>
      simp [mul, eval, eval_add, eval_scaleSlice, hp, RadicalBivariate.eval]
      ring

@[simp] theorem eval_constant {n : ℕ} (a : RadicalExpression n) (input : Fin n → ℝ)
    (x y z : ℝ) : eval (constant a) input x y z = a.eval input := by
  simp [constant, eval, RadicalBivariate.eval, RadicalUnivariate.eval]

@[simp] theorem eval_first {n : ℕ} (input : Fin n → ℝ) (x y z : ℝ) :
    eval first input x y z = x := by
  simp [first, eval, RadicalBivariate.eval, RadicalUnivariate.eval, RadicalExpression.eval]

@[simp] theorem eval_second {n : ℕ} (input : Fin n → ℝ) (x y z : ℝ) :
    eval second input x y z = y := by
  simp [second, eval, RadicalBivariate.eval, RadicalUnivariate.eval, RadicalExpression.eval]

@[simp] theorem eval_third {n : ℕ} (input : Fin n → ℝ) (x y z : ℝ) :
    eval third input x y z = z := by
  simp [third, eval, RadicalBivariate.eval, RadicalUnivariate.eval, RadicalExpression.eval]

theorem eval_pow {n : ℕ} (p : RadicalTrivariate n) (k : ℕ) (input : Fin n → ℝ)
    (x y z : ℝ) : eval (pow p k) input x y z = eval p input x y z ^ k := by
  induction k with
  | zero => simp [pow, RadicalExpression.eval]
  | succ k hk => simp [pow, eval_mul, hk, pow_succ]

/-- Horner evaluation in the first variable equals the padded power sum. -/
theorem eval_eq_sum_getD {n N : ℕ} (p : RadicalTrivariate n) (h : p.length ≤ N)
    (input : Fin n → ℝ) (x y z : ℝ) :
    eval p input x y z =
      ∑ i : Fin N, RadicalBivariate.eval (p.getD i []) input y z * x ^ (i : ℕ) := by
  induction N generalizing p with
  | zero =>
      have hp : p = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
      subst p
      simp [eval]
  | succ N ih =>
      cases p with
      | nil => simp [eval, RadicalBivariate.eval]
      | cons a p =>
          rw [Fin.sum_univ_succ]
          simp only [List.getD_cons_zero, Fin.val_zero, pow_zero, mul_one]
          rw [eval]
          have hp : p.length ≤ N := by simpa using h
          rw [ih p hp]
          simp only [Fin.val_succ, List.getD_cons_succ]
          rw [Finset.mul_sum]
          apply congrArg (RadicalBivariate.eval a input y z + ·)
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ]
          ring

/-- A trivariate coefficient list fits in the stated padded degree box. -/
def Fits {n : ℕ} (firstDegree secondDegree thirdDegree : ℕ)
    (p : RadicalTrivariate n) : Prop :=
  p.length ≤ firstDegree + 1 ∧
    ∀ slice ∈ p, slice.length ≤ secondDegree + 1 ∧
      ∀ row ∈ slice, row.length ≤ thirdDegree + 1

/-- Read a coefficient, returning exact zero outside the stored lists. -/
def coefficient {n : ℕ} (p : RadicalTrivariate n) (i j k : ℕ) : RadicalExpression n :=
  ((p.getD i []).getD j []).getD k (.constant 0)

private theorem getD_slice_fits {n m l : ℕ} {p : RadicalTrivariate n}
    (h : ∀ slice ∈ p, slice.length ≤ m ∧ ∀ row ∈ slice, row.length ≤ l) (i : ℕ) :
    (p.getD i []).length ≤ m ∧ ∀ row ∈ p.getD i [], row.length ≤ l := by
  by_cases hi : i < p.length
  · rw [List.getD_eq_getElem p [] hi]
    exact h p[i] (List.getElem_mem ..)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    simp

private theorem getD_row_fits {n l : ℕ} {p : RadicalBivariate n}
    (h : ∀ row ∈ p, row.length ≤ l) (j : ℕ) : (p.getD j []).length ≤ l := by
  by_cases hj : j < p.length
  · rw [List.getD_eq_getElem p [] hj]
    exact h p[j] (List.getElem_mem ..)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
    simp

/-- A fitted trivariate polynomial evaluates as its rectangular padded power sum. -/
theorem eval_eq_power_sum {n m l d : ℕ} (p : RadicalTrivariate n) (h : Fits m l d p)
    (input : Fin n → ℝ) (x y z : ℝ) :
    eval p input x y z =
      ∑ i : Fin (m + 1), ∑ j : Fin (l + 1), ∑ k : Fin (d + 1),
        (coefficient p i j k).eval input * x ^ (i : ℕ) * y ^ (j : ℕ) * z ^ (k : ℕ) := by
  rw [eval_eq_sum_getD p h.1]
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hiLength, hiRows⟩ := getD_slice_fits h.2 i
  rw [RadicalBivariate.eval_eq_sum_getD _ hiLength]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjLength := getD_row_fits hiRows j
  rw [RadicalUnivariate.eval_eq_sum_getD _ hjLength]
  simp only [coefficient]
  rw [Finset.sum_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end RadicalTrivariate

end Bescovitch
