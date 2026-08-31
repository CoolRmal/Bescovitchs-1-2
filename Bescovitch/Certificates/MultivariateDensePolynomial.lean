/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Rat.Cast.Order

/-!
# Exact dense multivariable polynomials

A polynomial in `n + 1` variables is a coefficient sequence in the first variable whose entries
are polynomials in the remaining `n` variables.  The mutually inductive sequence avoids hidden
array or map invariants, so every arithmetic operation reduces transparently in the kernel.
-/

@[expose] public section

noncomputable section

open scoped BigOperators unitInterval

namespace Bescovitch

mutual

/-- Dense rational polynomials, recursively arranged by increasing powers. -/
inductive MultivariateDensePolynomial : ℕ → Type
  | base (value : ℚ) : MultivariateDensePolynomial 0
  | ofCoefficients {n : ℕ} (coefficients : MultivariateDenseCoefficients n) :
      MultivariateDensePolynomial (n + 1)

/-- A coefficient sequence for one polynomial variable. -/
inductive MultivariateDenseCoefficients : ℕ → Type
  | nil {n : ℕ} : MultivariateDenseCoefficients n
  | cons {n : ℕ} (head : MultivariateDensePolynomial n)
      (tail : MultivariateDenseCoefficients n) : MultivariateDenseCoefficients n

end

namespace MultivariateDensePolynomial

abbrev Coefficients := MultivariateDenseCoefficients

/-- The two coordinate degrees occurring in the mixed geometric certificate. -/
inductive BernsteinDegree where
  | quadratic
  | quartic
  deriving DecidableEq

namespace BernsteinDegree

/-- The natural-number value of a certificate degree. -/
def value : BernsteinDegree → ℕ
  | .quadratic => 2
  | .quartic => 4

end BernsteinDegree

namespace Coefficients

/-- Recursion over the coefficient tail, treating coefficient polynomials as atoms. -/
def recList {n : ℕ} {motive : Coefficients n → Sort*}
    (nil : motive .nil)
    (cons : ∀ head tail, motive tail → motive (.cons head tail)) :
    ∀ coefficients, motive coefficients
  | .nil => nil
  | .cons head tail => cons head tail (recList nil cons tail)

/-- Add two coefficient sequences, padding the shorter sequence by zero. -/
def add {n : ℕ} (addPolynomial : MultivariateDensePolynomial n →
    MultivariateDensePolynomial n → MultivariateDensePolynomial n) :
    Coefficients n → Coefficients n → Coefficients n
  | .nil, q => q
  | p, .nil => p
  | .cons p ps, .cons q qs => .cons (addPolynomial p q) (add addPolynomial ps qs)

/-- Map a coefficient operation over a sequence. -/
def map {n : ℕ} (f : MultivariateDensePolynomial n → MultivariateDensePolynomial n) :
    Coefficients n → Coefficients n
  | .nil => .nil
  | .cons p ps => .cons (f p) (map f ps)

/-- Exact coefficient convolution. -/
def mul {n : ℕ} (zero : MultivariateDensePolynomial n)
    (addPolynomial mulPolynomial : MultivariateDensePolynomial n →
      MultivariateDensePolynomial n → MultivariateDensePolynomial n) :
    Coefficients n → Coefficients n → Coefficients n
  | .nil, _ => .nil
  | .cons p ps, q =>
      add addPolynomial (map (mulPolynomial p) q)
        (.cons zero (mul zero addPolynomial mulPolynomial ps q))

/-- Horner evaluation of a coefficient sequence. -/
def eval {n : ℕ} (evalPolynomial : MultivariateDensePolynomial n → ℝ)
    (x : ℝ) : Coefficients n → ℝ
  | .nil => 0
  | .cons p ps => evalPolynomial p + x * eval evalPolynomial x ps

/-- The number of stored coefficients. -/
def length {n : ℕ} : Coefficients n → ℕ
  | .nil => 0
  | .cons _ ps => length ps + 1

/-- Read a coefficient, returning the zero polynomial past the stored support. -/
def get {n : ℕ} (zero : MultivariateDensePolynomial n) :
    Coefficients n → ℕ → MultivariateDensePolynomial n
  | .nil, _ => zero
  | .cons p _, 0 => p
  | .cons _ ps, k + 1 => get zero ps k

/-- Every stored coefficient satisfies `predicate`. -/
def All {n : ℕ} (predicate : MultivariateDensePolynomial n → Prop) :
    Coefficients n → Prop
  | .nil => True
  | .cons p ps => predicate p ∧ All predicate ps

/-- Boolean traversal of all stored coefficients. -/
def all {n : ℕ} (predicate : MultivariateDensePolynomial n → Bool) :
    Coefficients n → Bool
  | .nil => true
  | .cons p ps => predicate p && all predicate ps

end Coefficients

/-- The zero polynomial. -/
def zero : (n : ℕ) → MultivariateDensePolynomial n
  | 0 => .base 0
  | _ + 1 => .ofCoefficients .nil

/-- Polynomial addition. -/
def add : (n : ℕ) → MultivariateDensePolynomial n → MultivariateDensePolynomial n →
    MultivariateDensePolynomial n
  | 0, .base p, .base q => .base (p + q)
  | n + 1, .ofCoefficients p, .ofCoefficients q =>
      .ofCoefficients (Coefficients.add (add n) p q)

/-- Additive inverse. -/
def neg : (n : ℕ) → MultivariateDensePolynomial n → MultivariateDensePolynomial n
  | 0, .base p => .base (-p)
  | n + 1, .ofCoefficients p => .ofCoefficients (Coefficients.map (neg n) p)

/-- Multiply every coefficient by a rational scalar. -/
def scale (a : ℚ) : (n : ℕ) → MultivariateDensePolynomial n → MultivariateDensePolynomial n
  | 0, .base p => .base (a * p)
  | n + 1, .ofCoefficients p => .ofCoefficients (Coefficients.map (scale a n) p)

/-- Exact polynomial multiplication. -/
def mul : (n : ℕ) → MultivariateDensePolynomial n → MultivariateDensePolynomial n →
    MultivariateDensePolynomial n
  | 0, .base p, .base q => .base (p * q)
  | n + 1, .ofCoefficients p, .ofCoefficients q =>
      .ofCoefficients (Coefficients.mul (zero n) (add n) (mul n) p q)

/-- A constant polynomial. -/
def constant : (n : ℕ) → ℚ → MultivariateDensePolynomial n
  | 0, a => .base a
  | n + 1, a => .ofCoefficients (.cons (constant n a) .nil)

/-- A coordinate variable. -/
def coordinate : {n : ℕ} → Fin n → MultivariateDensePolynomial n
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases
      (.ofCoefficients (.cons (zero n) (.cons (constant n 1) .nil)))
      (fun j => .ofCoefficients (.cons (coordinate j) .nil)) i

/-- Natural powers of a dense polynomial. -/
def pow {n : ℕ} (p : MultivariateDensePolynomial n) : ℕ → MultivariateDensePolynomial n
  | 0 => constant n 1
  | k + 1 => mul n (pow p k) p

/-- Convert the outer variable from centered powers of degree two to Bernstein coefficients. -/
def centeredBernsteinQuadratic {n : ℕ} (p : Coefficients n) : Coefficients n :=
  let p₀ := p.get (zero n) 0
  let p₁ := p.get (zero n) 1
  let p₂ := p.get (zero n) 2
  .cons (add n (add n p₀ (neg n p₁)) p₂)
    (.cons (add n p₀ (neg n p₂))
      (.cons (add n (add n p₀ p₁) p₂) .nil))

/-- Convert the outer variable from centered powers of degree four to Bernstein coefficients. -/
def centeredBernsteinQuartic {n : ℕ} (p : Coefficients n) : Coefficients n :=
  let p₀ := p.get (zero n) 0
  let p₁ := p.get (zero n) 1
  let p₂ := p.get (zero n) 2
  let p₃ := p.get (zero n) 3
  let p₄ := p.get (zero n) 4
  .cons (add n (add n (add n (add n p₀ (neg n p₁)) p₂) (neg n p₃)) p₄)
    (.cons (add n (add n (add n p₀ (scale (-1 / 2) n p₁))
        (scale (1 / 2) n p₃)) (neg n p₄))
      (.cons (add n (add n p₀ (scale (-1 / 3) n p₂)) p₄)
        (.cons (add n (add n (add n p₀ (scale (1 / 2) n p₁))
            (scale (-1 / 2) n p₃)) (neg n p₄))
          (.cons (add n (add n (add n (add n p₀ p₁) p₂) p₃) p₄) .nil))))

/-- Convert one centered-power coordinate to its fixed Bernstein degree. -/
def centeredBernsteinCoefficients {n : ℕ} :
    BernsteinDegree → Coefficients n → Coefficients n
  | .quadratic => centeredBernsteinQuadratic
  | .quartic => centeredBernsteinQuartic

/-- Convert every coordinate of a dense polynomial to the centered Bernstein basis. -/
def centeredBernstein : {n : ℕ} → (Fin n → BernsteinDegree) →
    MultivariateDensePolynomial n → MultivariateDensePolynomial n
  | 0, _, .base p => .base p
  | _n + 1, degrees, .ofCoefficients p =>
      .ofCoefficients (centeredBernsteinCoefficients (degrees 0)
        (Coefficients.map (centeredBernstein (Fin.tail degrees)) p))

/-- A polynomial fits the coordinatewise degree profile used for conversion. -/
def Fits : {n : ℕ} → (Fin n → BernsteinDegree) →
    MultivariateDensePolynomial n → Prop
  | 0, _, .base _ => True
  | _n + 1, degrees, .ofCoefficients p =>
      Coefficients.length p ≤ (degrees 0).value + 1 ∧
        Coefficients.All (Fits (Fin.tail degrees)) p

/-- Decide whether a polynomial fits a coordinatewise Bernstein degree profile. -/
def fits : {n : ℕ} → (Fin n → BernsteinDegree) →
    MultivariateDensePolynomial n → Bool
  | 0, _, .base _ => true
  | _n + 1, degrees, .ofCoefficients p =>
      decide (Coefficients.length p ≤ (degrees 0).value + 1) &&
        Coefficients.all (fits (Fin.tail degrees)) p

/-- Evaluate a coefficient sequence in one Bernstein coordinate. -/
def Coefficients.bernsteinEval {n : ℕ} (zero : MultivariateDensePolynomial n)
    (evalPolynomial : MultivariateDensePolynomial n → ℝ) (degree : BernsteinDegree)
    (p : Coefficients n) (x : I) : ℝ := match degree with
  | .quadratic =>
      evalPolynomial (p.get zero 0) * bernstein 2 0 x +
        evalPolynomial (p.get zero 1) * bernstein 2 1 x +
        evalPolynomial (p.get zero 2) * bernstein 2 2 x
  | .quartic =>
      evalPolynomial (p.get zero 0) * bernstein 4 0 x +
        evalPolynomial (p.get zero 1) * bernstein 4 1 x +
        evalPolynomial (p.get zero 2) * bernstein 4 2 x +
        evalPolynomial (p.get zero 3) * bernstein 4 3 x +
        evalPolynomial (p.get zero 4) * bernstein 4 4 x

/-- Evaluate a dense tensor whose coordinates are in the Bernstein basis. -/
def centeredBernsteinEval : {n : ℕ} → (Fin n → BernsteinDegree) →
    MultivariateDensePolynomial n → (Fin n → I) → ℝ
  | 0, _, .base p, _ => p
  | n + 1, degrees, .ofCoefficients p, x =>
      Coefficients.bernsteinEval (zero n)
        (fun q => centeredBernsteinEval (Fin.tail degrees) q (Fin.tail x))
        (degrees 0) p (x 0)

/-- Exact Boolean sign check on all stored scalar coefficients. -/
def allNonpositive : {n : ℕ} → MultivariateDensePolynomial n → Bool
  | 0, .base p => decide (p ≤ 0)
  | _ + 1, .ofCoefficients p => Coefficients.all allNonpositive p

/-- Every stored scalar coefficient is nonpositive. -/
def AllNonpositive : {n : ℕ} → MultivariateDensePolynomial n → Prop
  | 0, .base p => p ≤ 0
  | _ + 1, .ofCoefficients p => Coefficients.All AllNonpositive p

/-- Evaluate a polynomial over the reals by nested Horner rules. -/
def eval : {n : ℕ} → MultivariateDensePolynomial n → (Fin n → ℝ) → ℝ
  | 0, .base p, _ => p
  | _n + 1, .ofCoefficients p, x =>
      Coefficients.eval (fun q => eval q (Fin.tail x)) (x 0) p

private theorem coefficients_eval_add {n : ℕ}
    (evalPolynomial : MultivariateDensePolynomial n → ℝ)
    (addPolynomial : MultivariateDensePolynomial n → MultivariateDensePolynomial n →
      MultivariateDensePolynomial n)
    (hadd : ∀ p q, evalPolynomial (addPolynomial p q) =
      evalPolynomial p + evalPolynomial q)
    (p q : Coefficients n) (x : ℝ) :
    Coefficients.eval evalPolynomial x (Coefficients.add addPolynomial p q) =
      Coefficients.eval evalPolynomial x p + Coefficients.eval evalPolynomial x q := by
  induction p using Coefficients.recList generalizing q with
  | nil => simp [Coefficients.add, Coefficients.eval]
  | cons p ps hps =>
      cases q with
      | nil => simp [Coefficients.add, Coefficients.eval]
      | cons q qs =>
          simp only [Coefficients.add, Coefficients.eval, hadd]
          rw [hps qs]
          ring

/-- Evaluation respects polynomial addition. -/
theorem eval_add {n : ℕ} (p q : MultivariateDensePolynomial n) (x : Fin n → ℝ) :
    eval (add n p q) x = eval p x + eval q x := by
  induction n with
  | zero => cases p; cases q; simp [add, eval]
  | succ n ih =>
      cases p with
      | ofCoefficients p =>
        cases q with
        | ofCoefficients q =>
          exact coefficients_eval_add _ _ (fun p q => ih p q (Fin.tail x)) p q (x 0)

private theorem coefficients_eval_map_neg {n : ℕ}
    (evalPolynomial : MultivariateDensePolynomial n → ℝ)
    (negPolynomial : MultivariateDensePolynomial n → MultivariateDensePolynomial n)
    (hneg : ∀ p, evalPolynomial (negPolynomial p) = -evalPolynomial p)
    (p : Coefficients n) (x : ℝ) :
    Coefficients.eval evalPolynomial x (Coefficients.map negPolynomial p) =
      -Coefficients.eval evalPolynomial x p := by
  induction p using Coefficients.recList with
  | nil => simp [Coefficients.map, Coefficients.eval]
  | cons p ps hps =>
      simp only [Coefficients.map, Coefficients.eval, hneg, hps]
      ring

/-- Evaluation respects additive inverse. -/
theorem eval_neg {n : ℕ} (p : MultivariateDensePolynomial n) (x : Fin n → ℝ) :
    eval (neg n p) x = -eval p x := by
  induction n with
  | zero => cases p; simp [neg, eval]
  | succ n ih =>
      cases p with
      | ofCoefficients p =>
          exact coefficients_eval_map_neg _ _ (fun p => ih p (Fin.tail x)) p (x 0)

private theorem coefficients_eval_map_scale {n : ℕ} (a : ℚ)
    (evalPolynomial : MultivariateDensePolynomial n → ℝ)
    (scalePolynomial : MultivariateDensePolynomial n → MultivariateDensePolynomial n)
    (hscale : ∀ p, evalPolynomial (scalePolynomial p) = a * evalPolynomial p)
    (p : Coefficients n) (x : ℝ) :
    Coefficients.eval evalPolynomial x (Coefficients.map scalePolynomial p) =
      a * Coefficients.eval evalPolynomial x p := by
  induction p using Coefficients.recList with
  | nil => simp [Coefficients.map, Coefficients.eval]
  | cons p ps hps =>
      simp only [Coefficients.map, Coefficients.eval, hscale, hps]
      ring

/-- Evaluation respects scalar multiplication. -/
theorem eval_scale (a : ℚ) {n : ℕ} (p : MultivariateDensePolynomial n)
    (x : Fin n → ℝ) : eval (scale a n p) x = a * eval p x := by
  induction n with
  | zero => cases p; simp [scale, eval]
  | succ n ih =>
      cases p with
      | ofCoefficients p =>
          exact coefficients_eval_map_scale a _ _ (fun p => ih p (Fin.tail x)) p (x 0)

private theorem coefficients_eval_mul {n : ℕ}
    (evalPolynomial : MultivariateDensePolynomial n → ℝ)
    (zeroPolynomial : MultivariateDensePolynomial n)
    (addPolynomial mulPolynomial : MultivariateDensePolynomial n →
      MultivariateDensePolynomial n → MultivariateDensePolynomial n)
    (hzero : evalPolynomial zeroPolynomial = 0)
    (hadd : ∀ p q, evalPolynomial (addPolynomial p q) =
      evalPolynomial p + evalPolynomial q)
    (hmul : ∀ p q, evalPolynomial (mulPolynomial p q) =
      evalPolynomial p * evalPolynomial q)
    (p q : Coefficients n) (x : ℝ) :
    Coefficients.eval evalPolynomial x
        (Coefficients.mul zeroPolynomial addPolynomial mulPolynomial p q) =
      Coefficients.eval evalPolynomial x p * Coefficients.eval evalPolynomial x q := by
  induction p using Coefficients.recList with
  | nil => simp [Coefficients.mul, Coefficients.eval]
  | cons p ps hps =>
      simp only [Coefficients.mul, coefficients_eval_add _ _ hadd, Coefficients.eval]
      have hmap := coefficients_eval_map_mul evalPolynomial mulPolynomial hmul p q x
      rw [hmap, hzero, hps]
      ring

where
  coefficients_eval_map_mul {n : ℕ}
      (evalPolynomial : MultivariateDensePolynomial n → ℝ)
      (mulPolynomial : MultivariateDensePolynomial n → MultivariateDensePolynomial n →
        MultivariateDensePolynomial n)
      (hmul : ∀ p q, evalPolynomial (mulPolynomial p q) =
        evalPolynomial p * evalPolynomial q)
      (p : MultivariateDensePolynomial n) (q : Coefficients n) (x : ℝ) :
      Coefficients.eval evalPolynomial x (Coefficients.map (mulPolynomial p) q) =
        evalPolynomial p * Coefficients.eval evalPolynomial x q := by
    induction q using Coefficients.recList with
    | nil => simp [Coefficients.map, Coefficients.eval]
    | cons q qs hqs =>
        simp only [Coefficients.map, Coefficients.eval, hmul, hqs]
        ring

/-- Evaluation respects polynomial multiplication. -/
theorem eval_mul {n : ℕ} (p q : MultivariateDensePolynomial n) (x : Fin n → ℝ) :
    eval (mul n p q) x = eval p x * eval q x := by
  induction n with
  | zero => cases p; cases q; simp [mul, eval]
  | succ n ih =>
      cases p with
      | ofCoefficients p =>
        cases q with
        | ofCoefficients q =>
          exact coefficients_eval_mul _ _ _ _
            (show eval (zero n) (Fin.tail x) = 0 by
              cases n <;> simp [zero, eval, Coefficients.eval])
            (fun p q => eval_add p q (Fin.tail x))
            (fun p q => ih p q (Fin.tail x)) p q (x 0)

@[simp]
theorem eval_zero (n : ℕ) (x : Fin n → ℝ) : eval (zero n) x = 0 := by
  cases n <;> simp [zero, eval, Coefficients.eval]

@[simp]
theorem eval_constant (n : ℕ) (a : ℚ) (x : Fin n → ℝ) : eval (constant n a) x = a := by
  induction n with
  | zero => simp [constant, eval]
  | succ n ih => simp [constant, eval, Coefficients.eval, ih]

@[simp]
theorem eval_coordinate {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    eval (coordinate i) x = x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [coordinate, eval, Coefficients.eval]
      · simp [coordinate, eval, Coefficients.eval, ih]
        rfl

theorem eval_pow {n : ℕ} (p : MultivariateDensePolynomial n) (k : ℕ)
    (x : Fin n → ℝ) : eval (pow p k) x = eval p x ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, eval_mul, ih, pow_succ]

private theorem coefficients_nil_add {n : ℕ}
    (addPolynomial : MultivariateDensePolynomial n → MultivariateDensePolynomial n →
      MultivariateDensePolynomial n) (p : Coefficients n) :
    Coefficients.add addPolynomial .nil p = p := by
  cases p <;> rfl

@[simp]
theorem zero_add (n : ℕ) (p : MultivariateDensePolynomial n) : add n (zero n) p = p := by
  cases n <;> cases p <;> simp [add, zero, coefficients_nil_add]

private theorem coefficients_add_nil {n : ℕ}
    (addPolynomial : MultivariateDensePolynomial n → MultivariateDensePolynomial n →
      MultivariateDensePolynomial n) (p : Coefficients n) :
    Coefficients.add addPolynomial p .nil = p := by
  induction p using Coefficients.recList with
  | nil => rfl
  | cons p ps hps => simp [Coefficients.add]

@[simp]
theorem add_zero (n : ℕ) (p : MultivariateDensePolynomial n) : add n p (zero n) = p := by
  cases n with
  | zero => cases p; simp [add, zero]
  | succ n =>
      cases p with
      | ofCoefficients p => simp [add, zero, coefficients_add_nil]

@[simp]
theorem neg_zero (n : ℕ) : neg n (zero n) = zero n := by
  cases n <;> simp [neg, zero, Coefficients.map]

@[simp]
theorem scale_zero (a : ℚ) (n : ℕ) : scale a n (zero n) = zero n := by
  cases n <;> simp [scale, zero, Coefficients.map]

private theorem coefficients_get_add {n : ℕ} (p q : Coefficients n) (k : ℕ) :
    Coefficients.get (zero n) (Coefficients.add (add n) p q) k =
      add n (Coefficients.get (zero n) p k) (Coefficients.get (zero n) q k) := by
  induction k generalizing p q with
  | zero => cases p <;> cases q <;> simp [Coefficients.get, Coefficients.add]
  | succ k ih => cases p <;> cases q <;> simp [Coefficients.get, Coefficients.add, ih]

private theorem coefficients_get_map_neg {n : ℕ} (p : Coefficients n) (k : ℕ) :
    Coefficients.get (zero n) (Coefficients.map (neg n) p) k =
      neg n (Coefficients.get (zero n) p k) := by
  induction k generalizing p with
  | zero => cases p <;> simp [Coefficients.get, Coefficients.map]
  | succ k ih => cases p <;> simp [Coefficients.get, Coefficients.map, ih]

private theorem coefficients_get_map_scale (a : ℚ) {n : ℕ} (p : Coefficients n) (k : ℕ) :
    Coefficients.get (zero n) (Coefficients.map (scale a n) p) k =
      scale a n (Coefficients.get (zero n) p k) := by
  induction k generalizing p with
  | zero => cases p <;> simp [Coefficients.get, Coefficients.map]
  | succ k ih => cases p <;> simp [Coefficients.get, Coefficients.map, ih]

@[simp]
theorem centeredBernsteinEval_zero {n : ℕ} (degrees : Fin n → BernsteinDegree)
    (x : Fin n → I) : centeredBernsteinEval degrees (zero n) x = 0 := by
  induction n with
  | zero => simp [centeredBernsteinEval, zero]
  | succ n ih =>
      change Coefficients.bernsteinEval (zero n)
        (fun q ↦ centeredBernsteinEval (Fin.tail degrees) q (Fin.tail x))
        (degrees 0) .nil (x 0) = 0
      cases hdegree : degrees 0 <;>
        simp [Coefficients.bernsteinEval, Coefficients.get,
          ih (Fin.tail degrees)]

theorem centeredBernsteinEval_add {n : ℕ} (degrees : Fin n → BernsteinDegree)
    (p q : MultivariateDensePolynomial n) (x : Fin n → I) :
    centeredBernsteinEval degrees (add n p q) x =
      centeredBernsteinEval degrees p x + centeredBernsteinEval degrees q x := by
  induction n with
  | zero => cases p; cases q; simp [centeredBernsteinEval, add]
  | succ n ih =>
      cases p with
      | ofCoefficients p =>
        cases q with
        | ofCoefficients q =>
          cases hdegree : degrees 0 <;>
            simp only [add, centeredBernsteinEval, Coefficients.bernsteinEval,
              hdegree, coefficients_get_add, ih (Fin.tail degrees)] <;>
            ring

theorem centeredBernsteinEval_neg {n : ℕ} (degrees : Fin n → BernsteinDegree)
    (p : MultivariateDensePolynomial n) (x : Fin n → I) :
    centeredBernsteinEval degrees (neg n p) x = -centeredBernsteinEval degrees p x := by
  induction n with
  | zero => cases p; simp [centeredBernsteinEval, neg]
  | succ n ih =>
      cases p with
      | ofCoefficients p =>
          cases hdegree : degrees 0 <;>
            simp only [neg, centeredBernsteinEval, Coefficients.bernsteinEval,
              hdegree, coefficients_get_map_neg, ih (Fin.tail degrees)] <;>
            ring

theorem centeredBernsteinEval_scale (a : ℚ) {n : ℕ}
    (degrees : Fin n → BernsteinDegree) (p : MultivariateDensePolynomial n)
    (x : Fin n → I) :
    centeredBernsteinEval degrees (scale a n p) x =
      a * centeredBernsteinEval degrees p x := by
  induction n with
  | zero => cases p; simp [centeredBernsteinEval, scale]
  | succ n ih =>
      cases p with
      | ofCoefficients p =>
          cases hdegree : degrees 0 <;>
            simp only [scale, centeredBernsteinEval, Coefficients.bernsteinEval,
              hdegree, coefficients_get_map_scale, ih (Fin.tail degrees)] <;>
            ring

private theorem coefficients_length_map {n : ℕ}
    (f : MultivariateDensePolynomial n → MultivariateDensePolynomial n)
    (p : Coefficients n) : Coefficients.length (Coefficients.map f p) =
      Coefficients.length p := by
  induction p using Coefficients.recList with
  | nil => rfl
  | cons p ps hps => simp [Coefficients.map, Coefficients.length, hps]

private theorem Coefficients.All.imp {n : ℕ}
    {first second : MultivariateDensePolynomial n → Prop} {p : Coefficients n}
    (h : p.All first) (himp : ∀ q, first q → second q) : p.All second := by
  induction p using Coefficients.recList with
  | nil => trivial
  | cons p ps hps =>
      exact ⟨himp p h.1, hps h.2⟩

private theorem coefficients_eval_map_of_all {n : ℕ}
    (f : MultivariateDensePolynomial n → MultivariateDensePolynomial n)
    (evalBefore evalAfter : MultivariateDensePolynomial n → ℝ)
    (p : Coefficients n) (x : ℝ)
    (h : p.All fun q ↦ evalAfter (f q) = evalBefore q) :
    Coefficients.eval evalAfter x (Coefficients.map f p) =
      Coefficients.eval evalBefore x p := by
  induction p using Coefficients.recList with
  | nil => simp [Coefficients.map, Coefficients.eval]
  | cons p ps hps => simp [Coefficients.map, Coefficients.eval, h.1, hps h.2]

private theorem coefficients_eval_centeredBernsteinQuadratic {n : ℕ}
    (evalPolynomial : MultivariateDensePolynomial n → ℝ)
    (hzero : evalPolynomial (zero n) = 0)
    (hadd : ∀ p q, evalPolynomial (add n p q) = evalPolynomial p + evalPolynomial q)
    (hneg : ∀ p, evalPolynomial (neg n p) = -evalPolynomial p)
    (p : Coefficients n) (hdegree : Coefficients.length p ≤ 3) (x : I) :
    Coefficients.eval evalPolynomial (2 * (x : ℝ) - 1) p =
      Coefficients.bernsteinEval (zero n) evalPolynomial .quadratic
        (centeredBernsteinQuadratic p) x := by
  cases p with
  | nil =>
      simp only [Coefficients.eval, Coefficients.bernsteinEval, centeredBernsteinQuadratic,
        Coefficients.get]
      norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, bernstein_apply,
        Nat.choose, hzero, hadd, hneg]
  | cons p₀ ps =>
      cases ps with
      | nil =>
          simp only [Coefficients.eval, Coefficients.bernsteinEval, centeredBernsteinQuadratic,
            Coefficients.get]
          norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, bernstein_apply,
            Nat.choose, hzero, hadd, hneg]
          ring
      | cons p₁ ps =>
          cases ps with
          | nil =>
              simp only [Coefficients.eval, Coefficients.bernsteinEval,
                centeredBernsteinQuadratic, Coefficients.get]
              norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, bernstein_apply,
                Nat.choose, hzero, hadd, hneg]
              ring
          | cons p₂ ps =>
              cases ps with
              | nil =>
                  simp only [Coefficients.eval, Coefficients.bernsteinEval,
                    centeredBernsteinQuadratic, Coefficients.get]
                  norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, bernstein_apply,
                    Nat.choose, hzero, hadd, hneg]
                  ring
              | cons p₃ ps =>
                  simp [Coefficients.length] at hdegree
                  omega

private theorem coefficients_eval_centeredBernsteinQuartic {n : ℕ}
    (evalPolynomial : MultivariateDensePolynomial n → ℝ)
    (hzero : evalPolynomial (zero n) = 0)
    (hadd : ∀ p q, evalPolynomial (add n p q) = evalPolynomial p + evalPolynomial q)
    (hneg : ∀ p, evalPolynomial (neg n p) = -evalPolynomial p)
    (hscale : ∀ a p, evalPolynomial (scale a n p) = a * evalPolynomial p)
    (p : Coefficients n) (hdegree : Coefficients.length p ≤ 5) (x : I) :
    Coefficients.eval evalPolynomial (2 * (x : ℝ) - 1) p =
      Coefficients.bernsteinEval (zero n) evalPolynomial .quartic
        (centeredBernsteinQuartic p) x := by
  cases p with
  | nil =>
      simp only [Coefficients.eval, Coefficients.bernsteinEval, centeredBernsteinQuartic,
        Coefficients.get]
      norm_num [bernstein_apply, Nat.choose, hzero, hadd, hneg, hscale]
  | cons p₀ ps =>
      cases ps with
      | nil =>
          simp only [Coefficients.eval, Coefficients.bernsteinEval, centeredBernsteinQuartic,
            Coefficients.get]
          norm_num [bernstein_apply, Nat.choose, hzero, hadd, hneg, hscale]; ring
      | cons p₁ ps =>
          cases ps with
          | nil =>
              simp only [Coefficients.eval, Coefficients.bernsteinEval,
                centeredBernsteinQuartic, Coefficients.get]
              norm_num [bernstein_apply, Nat.choose, hzero, hadd, hneg, hscale]; ring
          | cons p₂ ps =>
              cases ps with
              | nil =>
                  simp only [Coefficients.eval, Coefficients.bernsteinEval,
                    centeredBernsteinQuartic, Coefficients.get]
                  norm_num [bernstein_apply, Nat.choose, hzero, hadd, hneg, hscale]; ring
              | cons p₃ ps =>
                  cases ps with
                  | nil =>
                      simp only [Coefficients.eval, Coefficients.bernsteinEval,
                        centeredBernsteinQuartic, Coefficients.get]
                      norm_num [bernstein_apply, Nat.choose, hzero, hadd, hneg, hscale]; ring
                  | cons p₄ ps =>
                      cases ps with
                      | nil =>
                          simp only [Coefficients.eval, Coefficients.bernsteinEval,
                            centeredBernsteinQuartic, Coefficients.get]
                          norm_num [bernstein_apply, Nat.choose, hzero, hadd, hneg, hscale]; ring
                      | cons p₅ ps =>
                          simp [Coefficients.length] at hdegree
                          omega

/-- Exact power-to-Bernstein conversion on the centered cube. -/
theorem eval_centeredBernstein {n : ℕ} (degrees : Fin n → BernsteinDegree)
    (p : MultivariateDensePolynomial n) (hfits : Fits degrees p) (x : Fin n → I) :
    eval p (fun i ↦ 2 * (x i : ℝ) - 1) =
      centeredBernsteinEval degrees (centeredBernstein degrees p) x := by
  induction n with
  | zero => cases p; rfl
  | succ n ih =>
      cases p with
      | ofCoefficients p =>
          let tailDegrees := Fin.tail degrees
          let tailX := Fin.tail x
          let transformed := Coefficients.map (centeredBernstein tailDegrees) p
          have hcoeff : Coefficients.All (fun q ↦
              centeredBernsteinEval tailDegrees (centeredBernstein tailDegrees q) tailX =
                eval q (fun i ↦ 2 * (tailX i : ℝ) - 1)) p :=
            Coefficients.All.imp hfits.2 fun q hq ↦ (ih tailDegrees q hq tailX).symm
          have hmap :
              Coefficients.eval
                  (fun q ↦ centeredBernsteinEval tailDegrees q tailX)
                  (2 * (x 0 : ℝ) - 1) transformed =
                Coefficients.eval
                  (fun q ↦ eval q (fun i ↦ 2 * (tailX i : ℝ) - 1))
                  (2 * (x 0 : ℝ) - 1) p :=
            coefficients_eval_map_of_all _ _ _ p _ hcoeff
          change Coefficients.eval
              (fun q ↦ eval q (fun i ↦ 2 * (tailX i : ℝ) - 1))
              (2 * (x 0 : ℝ) - 1) p =
            Coefficients.bernsteinEval (zero n)
              (fun q ↦ centeredBernsteinEval tailDegrees q tailX) (degrees 0)
              (centeredBernsteinCoefficients (degrees 0) transformed) (x 0)
          rw [← hmap]
          cases hdegree : degrees 0 with
          | quadratic =>
              exact coefficients_eval_centeredBernsteinQuadratic
                (fun q ↦ centeredBernsteinEval tailDegrees q tailX)
                (centeredBernsteinEval_zero tailDegrees tailX)
                (fun q r ↦ centeredBernsteinEval_add tailDegrees q r tailX)
                (fun q ↦ centeredBernsteinEval_neg tailDegrees q tailX)
                transformed (by simpa [transformed, hdegree, BernsteinDegree.value,
                  coefficients_length_map] using hfits.1) (x 0)
          | quartic =>
              exact coefficients_eval_centeredBernsteinQuartic
                (fun q ↦ centeredBernsteinEval tailDegrees q tailX)
                (centeredBernsteinEval_zero tailDegrees tailX)
                (fun q r ↦ centeredBernsteinEval_add tailDegrees q r tailX)
                (fun q ↦ centeredBernsteinEval_neg tailDegrees q tailX)
                (fun a q ↦ centeredBernsteinEval_scale a tailDegrees q tailX)
                transformed (by simpa [transformed, hdegree, BernsteinDegree.value,
                  coefficients_length_map] using hfits.1) (x 0)

private theorem coefficients_all_eq_true {n : ℕ}
    (predicate : MultivariateDensePolynomial n → Bool) (p : Coefficients n) :
    Coefficients.all predicate p = true ↔
      Coefficients.All (fun q ↦ predicate q = true) p := by
  induction p using Coefficients.recList with
  | nil => simp [Coefficients.all, Coefficients.All]
  | cons p ps hps => simp [Coefficients.all, Coefficients.All, hps]

/-- A successful Boolean degree-profile check proves the corresponding exact property. -/
theorem fits_sound {n : ℕ} (degrees : Fin n → BernsteinDegree)
    (p : MultivariateDensePolynomial n) (h : fits degrees p = true) : Fits degrees p := by
  induction n with
  | zero => cases p; trivial
  | succ n ih =>
      cases p with
      | ofCoefficients p =>
          rw [fits, Bool.and_eq_true, decide_eq_true_eq, coefficients_all_eq_true] at h
          exact ⟨h.1, Coefficients.All.imp h.2 fun q hq ↦ ih _ q hq⟩

/-- The Boolean coefficient check reflects the corresponding exact sign property. -/
theorem allNonpositive_sound {n : ℕ} (p : MultivariateDensePolynomial n)
    (h : allNonpositive p = true) : AllNonpositive p := by
  induction n with
  | zero =>
      cases p with
      | base p => simpa [allNonpositive, AllNonpositive] using h
  | succ n ih =>
      cases p with
      | ofCoefficients p =>
          rw [allNonpositive, coefficients_all_eq_true] at h
          exact Coefficients.All.imp h fun q hq ↦ ih q hq

private theorem allNonpositive_zero (n : ℕ) : AllNonpositive (zero n) := by
  cases n <;> simp [AllNonpositive, zero, Coefficients.All]

private theorem coefficients_all_get {n : ℕ}
    (predicate : MultivariateDensePolynomial n → Prop) (zero : MultivariateDensePolynomial n)
    (hzero : predicate zero) (p : Coefficients n) (hp : Coefficients.All predicate p) (k : ℕ) :
    predicate (Coefficients.get zero p k) := by
  induction k generalizing p with
  | zero =>
      cases p with
      | nil => exact hzero
      | cons p ps => exact hp.1
  | succ k ih =>
      cases p with
      | nil => simpa [Coefficients.get] using hzero
      | cons p ps => exact ih ps hp.2

/-- A tensor with nonpositive Bernstein coefficients is nonpositive on the unit cube. -/
theorem centeredBernsteinEval_nonpos {n : ℕ} (degrees : Fin n → BernsteinDegree)
    (p : MultivariateDensePolynomial n) (x : Fin n → I) (hp : AllNonpositive p) :
    centeredBernsteinEval degrees p x ≤ 0 := by
  induction n with
  | zero =>
      cases p with
      | base p =>
          change (p : ℝ) ≤ 0
          change p ≤ 0 at hp
          exact_mod_cast hp
  | succ n ih =>
      cases p with
      | ofCoefficients p =>
          have hcoeff (k : ℕ) :
              centeredBernsteinEval (Fin.tail degrees)
                  (Coefficients.get (zero n) p k) (Fin.tail x) ≤ 0 :=
            ih (Fin.tail degrees) _ (Fin.tail x)
              (coefficients_all_get AllNonpositive (zero n) (allNonpositive_zero n) p hp k)
          cases hdegree : degrees 0 with
          | quadratic =>
              simp only [centeredBernsteinEval, Coefficients.bernsteinEval, hdegree]
              exact add_nonpos
                (add_nonpos
                  (mul_nonpos_of_nonpos_of_nonneg (hcoeff 0) bernstein_nonneg)
                  (mul_nonpos_of_nonpos_of_nonneg (hcoeff 1) bernstein_nonneg))
                (mul_nonpos_of_nonpos_of_nonneg (hcoeff 2) bernstein_nonneg)
          | quartic =>
              simp only [centeredBernsteinEval, Coefficients.bernsteinEval, hdegree]
              exact add_nonpos
                (add_nonpos
                  (add_nonpos
                    (add_nonpos
                      (mul_nonpos_of_nonpos_of_nonneg (hcoeff 0) bernstein_nonneg)
                      (mul_nonpos_of_nonpos_of_nonneg (hcoeff 1) bernstein_nonneg))
                    (mul_nonpos_of_nonpos_of_nonneg (hcoeff 2) bernstein_nonneg))
                  (mul_nonpos_of_nonpos_of_nonneg (hcoeff 3) bernstein_nonneg))
                (mul_nonpos_of_nonpos_of_nonneg (hcoeff 4) bernstein_nonneg)

/-- The exact Boolean Bernstein checker bounds a fitted polynomial on the centered cube. -/
theorem eval_nonpos_of_centeredBernstein_check {n : ℕ}
    (degrees : Fin n → BernsteinDegree) (p : MultivariateDensePolynomial n)
    (hfits : Fits degrees p)
    (hcheck : allNonpositive (centeredBernstein degrees p) = true)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) : eval p x ≤ 0 := by
  let u : Fin n → I := fun i ↦
    ⟨(x i + 1) / 2, by
      constructor
      · have := (abs_le.mp (hx i)).1
        linarith
      · have := (abs_le.mp (hx i)).2
        linarith⟩
  have hxcenter : (fun i ↦ 2 * (u i : ℝ) - 1) = x := by
    funext i
    dsimp [u]
    ring
  rw [← hxcenter, eval_centeredBernstein degrees p hfits u]
  exact centeredBernsteinEval_nonpos degrees _ u (allNonpositive_sound _ hcheck)

end MultivariateDensePolynomial

end Bescovitch
