/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.DyadicTrivariatePolynomial.Basic
public import Bescovitch.Certificates.IntegerTensorBernstein
import Mathlib.Tactic.Ring

/-!
# Evaluation of exact dyadic trivariate polynomials

The list representation is related to fixed power tensors and their Bernstein certificates.
-/

@[expose] public section

open scoped BigOperators unitInterval

namespace Bescovitch.DyadicTrivariatePolynomial

noncomputable section

namespace IntPolynomial

/-- Evaluate an integer univariate power-coefficient list. -/
def eval : IntPolynomial → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => a + x * eval p x

/-- Evaluation commutes with addition of integer univariate polynomials. -/
theorem eval_add (p q : IntPolynomial) (x : ℝ) :
    eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
      cases q with
      | nil => simp [add, eval]
      | cons b q => simp [add, eval, ih]; ring

/-- Evaluation commutes with negation of integer univariate polynomials. -/
theorem eval_neg (p : IntPolynomial) (x : ℝ) : eval (neg p) x = -eval p x := by
  induction p with
  | nil => simp [neg, eval]
  | cons a p ih =>
      change ((-a : ℤ) : ℝ) + x * eval (neg p) x = -((a : ℝ) + x * eval p x)
      rw [ih]
      push_cast
      ring

/-- Evaluation commutes with integer scaling of a univariate polynomial. -/
theorem eval_scale (a : ℤ) (p : IntPolynomial) (x : ℝ) :
    eval (scale a p) x = a * eval p x := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p ih =>
      change ((a * b : ℤ) : ℝ) + x * eval (scale a p) x =
        (a : ℝ) * ((b : ℝ) + x * eval p x)
      rw [ih]
      push_cast
      ring

/-- Evaluation commutes with multiplication of integer univariate polynomials. -/
theorem eval_mul (p q : IntPolynomial) (x : ℝ) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih => simp [mul, eval, eval_add, eval_scale, ih]; ring

/-- Evaluation is unchanged when the coefficient list is padded with zeros. -/
theorem eval_eq_padded_sum (p : IntPolynomial) (n : ℕ) (hp : p.length ≤ n)
    (x : ℝ) :
    eval p x = ∑ i : Fin n, (p.getD i 0 : ℝ) * x ^ (i : ℕ) := by
  induction n generalizing p with
  | zero =>
      have : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
      subst p
      simp [eval]
  | succ n ih =>
      cases p with
      | nil => simp [eval]
      | cons a p =>
          have htail : p.length ≤ n := by simpa using hp
          rw [eval, Fin.sum_univ_succ, ih p htail, Finset.mul_sum]
          simp only [List.getD_cons_zero, Fin.val_zero, pow_zero, mul_one,
            List.getD_cons_succ, Fin.val_succ]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ]
          ring

end IntPolynomial

namespace IntBivariate

/-- Evaluate integer bivariate power coefficients. -/
def eval : IntBivariate → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | p :: ps, x, y => IntPolynomial.eval p y + x * eval ps x y

/-- Evaluation commutes with addition of integer bivariate polynomials. -/
theorem eval_add (p q : IntBivariate) (x y : ℝ) :
    eval (add p q) x y = eval p x y + eval q x y := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
      cases q with
      | nil => simp [add, eval]
      | cons b q => simp [add, eval, IntPolynomial.eval_add, ih]; ring

/-- Evaluation commutes with negation of integer bivariate polynomials. -/
theorem eval_neg (p : IntBivariate) (x y : ℝ) : eval (neg p) x y = -eval p x y := by
  induction p with
  | nil => simp [neg, eval]
  | cons a p ih =>
      change IntPolynomial.eval (IntPolynomial.neg a) y + x * eval (neg p) x y =
        -(IntPolynomial.eval a y + x * eval p x y)
      rw [IntPolynomial.eval_neg, ih]
      ring

/-- Evaluation commutes with univariate scaling of a bivariate polynomial. -/
theorem eval_scale (a : IntPolynomial) (p : IntBivariate) (x y : ℝ) :
    eval (scale a p) x y = IntPolynomial.eval a y * eval p x y := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p ih =>
      change IntPolynomial.eval (IntPolynomial.mul a b) y + x * eval (scale a p) x y =
        IntPolynomial.eval a y * (IntPolynomial.eval b y + x * eval p x y)
      rw [IntPolynomial.eval_mul, ih]
      ring

/-- Evaluation commutes with integer scaling of a bivariate polynomial. -/
theorem eval_scale_int (a : ℤ) (p : IntBivariate) (x y : ℝ) :
    eval (scaleInt a p) x y = a * eval p x y := by
  induction p with
  | nil => simp [scaleInt, eval]
  | cons b p ih =>
      change IntPolynomial.eval (IntPolynomial.scale a b) y + x * eval (scaleInt a p) x y =
        (a : ℝ) * (IntPolynomial.eval b y + x * eval p x y)
      rw [IntPolynomial.eval_scale, ih]
      ring

/-- Evaluation commutes with multiplication of integer bivariate polynomials. -/
theorem eval_mul (p q : IntBivariate) (x y : ℝ) :
    eval (mul p q) x y = eval p x y * eval q x y := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih => simp [mul, eval, eval_add, eval_scale, ih, IntPolynomial.eval]; ring

/-- Bivariate evaluation is unchanged when both coefficient axes are padded with zeros. -/
theorem eval_eq_padded_sum (p : IntBivariate) (n m : ℕ)
    (hp : p.length ≤ n) (hrows : ∀ row ∈ p, row.length ≤ m)
    (x y : ℝ) :
    eval p x y = ∑ i : Fin n, ∑ j : Fin m,
      (((p.getD i []).getD j 0 : ℤ) : ℝ) * x ^ (i : ℕ) * y ^ (j : ℕ) := by
  induction n generalizing p with
  | zero =>
      have : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
      subst p
      simp [eval]
  | succ n ih =>
      cases p with
      | nil => simp [eval]
      | cons row p =>
          have htail : p.length ≤ n := by simpa using hp
          have hrow : row.length ≤ m := hrows row (by simp)
          have htailRows : ∀ q ∈ p, q.length ≤ m := by
            intro q hq
            exact hrows q (by simp [hq])
          rw [eval, Fin.sum_univ_succ, ih p htail htailRows,
            IntPolynomial.eval_eq_padded_sum row m hrow, Finset.mul_sum]
          simp only [List.getD_cons_zero, Fin.val_zero, pow_zero, mul_one,
            List.getD_cons_succ, Fin.val_succ]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring

end IntBivariate

namespace IntTrivariate

/-- Evaluate integer trivariate power coefficients. -/
def eval : IntTrivariate → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _ => 0
  | p :: ps, x, y, z => IntBivariate.eval p y z + x * eval ps x y z

/-- Evaluation commutes with addition of integer trivariate polynomials. -/
theorem eval_add (p q : IntTrivariate) (x y z : ℝ) :
    eval (add p q) x y z = eval p x y z + eval q x y z := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
      cases q with
      | nil => simp [add, eval]
      | cons b q => simp [add, eval, IntBivariate.eval_add, ih]; ring

/-- Evaluation commutes with negation of integer trivariate polynomials. -/
theorem eval_neg (p : IntTrivariate) (x y z : ℝ) :
    eval (neg p) x y z = -eval p x y z := by
  induction p with
  | nil => simp [neg, eval]
  | cons a p ih =>
      change IntBivariate.eval (IntBivariate.neg a) y z + x * eval (neg p) x y z =
        -(IntBivariate.eval a y z + x * eval p x y z)
      rw [IntBivariate.eval_neg, ih]
      ring

/-- Evaluation commutes with bivariate scaling of a trivariate polynomial. -/
theorem eval_scale (a : IntBivariate) (p : IntTrivariate) (x y z : ℝ) :
    eval (scale a p) x y z = IntBivariate.eval a y z * eval p x y z := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p ih =>
      change IntBivariate.eval (IntBivariate.mul a b) y z + x * eval (scale a p) x y z =
        IntBivariate.eval a y z * (IntBivariate.eval b y z + x * eval p x y z)
      rw [IntBivariate.eval_mul, ih]
      ring

/-- Evaluation commutes with integer scaling of a trivariate polynomial. -/
theorem eval_scale_int (a : ℤ) (p : IntTrivariate) (x y z : ℝ) :
    eval (scaleInt a p) x y z = a * eval p x y z := by
  induction p with
  | nil => simp [scaleInt, eval]
  | cons b p ih =>
      change IntBivariate.eval (IntBivariate.scaleInt a b) y z +
          x * eval (scaleInt a p) x y z =
        (a : ℝ) * (IntBivariate.eval b y z + x * eval p x y z)
      rw [IntBivariate.eval_scale_int, ih]
      ring

/-- Evaluation commutes with multiplication of integer trivariate polynomials. -/
theorem eval_mul (p q : IntTrivariate) (x y z : ℝ) :
    eval (mul p q) x y z = eval p x y z * eval q x y z := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih => simp [mul, eval, eval_add, eval_scale, ih, IntBivariate.eval]; ring

/-- Trivariate evaluation is unchanged when all coefficient axes are padded with zeros. -/
theorem eval_eq_padded_sum (p : IntTrivariate) (n m l : ℕ)
    (hp : p.length ≤ n)
    (hslices : ∀ slice ∈ p, slice.length ≤ m)
    (hrows : ∀ slice ∈ p, ∀ row ∈ slice, row.length ≤ l)
    (x y z : ℝ) :
    eval p x y z = ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin l,
      (p.coefficient i j k : ℝ) * x ^ (i : ℕ) *
        y ^ (j : ℕ) * z ^ (k : ℕ) := by
  induction n generalizing p with
  | zero =>
      have : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
      subst p
      simp [eval, coefficient]
  | succ n ih =>
      cases p with
      | nil => simp [eval, coefficient]
      | cons slice p =>
          have htail : p.length ≤ n := by simpa using hp
          have hslice : slice.length ≤ m := hslices slice (by simp)
          have htailSlices : ∀ q ∈ p, q.length ≤ m := by
            intro q hq
            exact hslices q (by simp [hq])
          have hsliceRows : ∀ row ∈ slice, row.length ≤ l := by
            intro row hrow
            exact hrows slice (by simp) row hrow
          have htailRows : ∀ q ∈ p, ∀ row ∈ q, row.length ≤ l := by
            intro q hq row hrow
            exact hrows q (by simp [hq]) row hrow
          rw [eval, Fin.sum_univ_succ, ih p htail htailSlices htailRows,
            IntBivariate.eval_eq_padded_sum slice m l hslice hsliceRows,
            Finset.mul_sum]
          simp only [coefficient, List.getD_cons_zero, Fin.val_zero, pow_zero, mul_one,
            List.getD_cons_succ, Fin.val_succ]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring

end IntTrivariate

namespace ScaledPolynomial

/-- Evaluate a scaled polynomial as its numerator divided by its dyadic denominator. -/
def eval (p : ScaledPolynomial) (x y z : ℝ) : ℝ :=
  IntTrivariate.eval p.numerator x y z / (2 : ℝ) ^ p.exponent

/-- Dyadic coefficient shifts multiply the integer evaluation by the same power of two. -/
theorem eval_shift (n : ℕ) (p : IntTrivariate) (x y z : ℝ) :
    IntTrivariate.eval (shift n p) x y z =
      (2 : ℝ) ^ n * IntTrivariate.eval p x y z := by
  simp [shift, IntTrivariate.eval_scale_int]

/-- Evaluation commutes with addition of scaled polynomials. -/
theorem eval_add (p q : ScaledPolynomial) (x y z : ℝ) :
    eval (add p q) x y z = eval p x y z + eval q x y z := by
  rw [eval, add]
  split_ifs with h
  · rw [IntTrivariate.eval_add, eval_shift]
    have hpow : (2 : ℝ) ^ q.exponent =
        2 ^ (q.exponent - p.exponent) * 2 ^ p.exponent := by
      rw [← pow_add, Nat.sub_add_cancel h]
    dsimp only [eval]
    rw [hpow]
    field_simp
  · rw [IntTrivariate.eval_add, eval_shift]
    have hle : q.exponent ≤ p.exponent := Nat.le_of_not_ge h
    have hpow : (2 : ℝ) ^ p.exponent =
        2 ^ (p.exponent - q.exponent) * 2 ^ q.exponent := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    dsimp only [eval]
    rw [hpow]
    field_simp

/-- Evaluation commutes with negation of scaled polynomials. -/
theorem eval_neg (p : ScaledPolynomial) (x y z : ℝ) :
    eval (neg p) x y z = -eval p x y z := by
  rw [eval, neg, IntTrivariate.eval_neg]
  dsimp only [eval]
  ring

/-- Evaluation commutes with multiplication of scaled polynomials. -/
theorem eval_mul (p q : ScaledPolynomial) (x y z : ℝ) :
    eval (mul p q) x y z = eval p x y z * eval q x y z := by
  rw [eval, mul, IntTrivariate.eval_mul, pow_add]
  dsimp only [eval]
  field_simp

/-- Evaluation commutes with natural powers of scaled polynomials. -/
theorem eval_pow (p : ScaledPolynomial) (n : ℕ) (x y z : ℝ) :
    eval (pow p n) x y z = eval p x y z ^ n := by
  induction n with
  | zero => simp [pow, eval, IntTrivariate.constant, IntTrivariate.eval,
      IntBivariate.eval, IntPolynomial.eval]
  | succ n ih => simp [pow, eval_mul, ih, pow_succ]

/-- A constant scaled polynomial evaluates to its dyadic value. -/
theorem eval_dyadic (numerator : ℤ) (exponent : ℕ) (x y z : ℝ) :
    eval (dyadic numerator exponent) x y z = numerator / (2 : ℝ) ^ exponent := by
  simp [eval, dyadic, IntTrivariate.constant, IntTrivariate.eval,
    IntBivariate.eval, IntPolynomial.eval]

/-- The first coordinate polynomial evaluates to its first argument. -/
@[simp] theorem eval_first (x y z : ℝ) : eval first x y z = x := by
  simp [eval, first, IntTrivariate.first, IntTrivariate.eval,
    IntBivariate.eval, IntPolynomial.eval]

/-- The second coordinate polynomial evaluates to its second argument. -/
@[simp] theorem eval_second (x y z : ℝ) : eval second x y z = y := by
  simp [eval, second, IntTrivariate.second, IntTrivariate.eval,
    IntBivariate.eval, IntPolynomial.eval]

/-- The third coordinate polynomial evaluates to its third argument. -/
@[simp] theorem eval_third (x y z : ℝ) : eval third x y z = z := by
  simp [eval, third, IntTrivariate.third, IntTrivariate.eval,
    IntBivariate.eval, IntPolynomial.eval]

/-- Evaluation respects the additive instance. -/
@[simp] theorem eval_add_notation (p q : ScaledPolynomial) (x y z : ℝ) :
    eval (p + q) x y z = eval p x y z + eval q x y z := eval_add p q x y z

/-- Evaluation respects the negation instance. -/
@[simp] theorem eval_neg_notation (p : ScaledPolynomial) (x y z : ℝ) :
    eval (-p) x y z = -eval p x y z := eval_neg p x y z

/-- Evaluation respects the multiplication instance. -/
@[simp] theorem eval_mul_notation (p q : ScaledPolynomial) (x y z : ℝ) :
    eval (p * q) x y z = eval p x y z * eval q x y z := eval_mul p q x y z

/-- Evaluation respects the power instance. -/
@[simp] theorem eval_pow_notation (p : ScaledPolynomial) (n : ℕ) (x y z : ℝ) :
    eval (p ^ n) x y z = eval p x y z ^ n := eval_pow p n x y z

end ScaledPolynomial

/-- Equal bounded coefficient tensors with equal scales have equal real evaluations. -/
theorem ScaledPolynomial.eval_eq_of_tensor (p q : ScaledPolynomial)
    (hexponent : p.exponent = q.exponent)
    (hp : p.numerator.length ≤ 13)
    (hpslices : ∀ slice ∈ p.numerator, slice.length ≤ 13)
    (hprows : ∀ slice ∈ p.numerator, ∀ row ∈ slice, row.length ≤ 5)
    (hq : q.numerator.length ≤ 13)
    (hqslices : ∀ slice ∈ q.numerator, slice.length ≤ 13)
    (hqrows : ∀ slice ∈ q.numerator, ∀ row ∈ slice, row.length ≤ 5)
    (hcoeff : ∀ i j k, powerTensor p.numerator i j k =
      powerTensor q.numerator i j k) (x y z : ℝ) :
    p.eval x y z = q.eval x y z := by
  unfold ScaledPolynomial.eval
  rw [IntTrivariate.eval_eq_padded_sum p.numerator 13 13 5
    hp hpslices hprows]
  rw [IntTrivariate.eval_eq_padded_sum q.numerator 13 13 5
    hq hqslices hqrows]
  simp only [powerTensor] at hcoeff
  simp_rw [hcoeff]
  rw [hexponent]

/-- A scaled polynomial with a certified tensor is nonnegative on the unit cube. -/
theorem ScaledPolynomial.eval_nonnegative_of_tensor (p : ScaledPolynomial)
    (hp : p.numerator.length ≤ 13)
    (hslices : ∀ slice ∈ p.numerator, slice.length ≤ 13)
    (hrows : ∀ slice ∈ p.numerator, ∀ row ∈ slice, row.length ≤ 5)
    (tree : TensorSubdivision)
    (htree : IntegerTensorBernstein.SubdivisionNonnegative tree
      (IntegerTensorBernstein.convertPowerTensor (powerTensor p.numerator)))
    (x y z : I) : 0 ≤ p.eval x y z := by
  have h := IntegerTensorBernstein.paddedPowerTensor_nonnegative
    tree (powerTensor p.numerator) htree x y z
  simp only [powerTensor] at h
  rw [← IntTrivariate.eval_eq_padded_sum p.numerator 13 13 5
    hp hslices hrows] at h
  change 0 ≤ IntTrivariate.eval p.numerator x y z / (2 : ℝ) ^ p.exponent
  exact div_nonneg h (by positivity)

end

end Bescovitch.DyadicTrivariatePolynomial
