/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.BivariateBernstein
public import Bescovitch.SixPoint.WeightedSelfFormula
public import Bescovitch.SixPoint.WeightedSelfCertificateCore

/-!
# Exact dyadic polynomials for the hard weighted-self bin
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

open Lean Macro

/-- Join fixed-width decimal chunks into one numeric literal during elaboration. -/
syntax "decimal60![" num,+ "]" : term

macro_rules
  | `(decimal60![$ns:num,*]) => do
      let parts := ns.getElems.toList.map fun n ↦ toString n.getNat
      let first :: rest := parts | Macro.throwError "expected at least one decimal chunk"
      let pad (s : String) := String.join (List.replicate (60 - s.length) "0") ++ s
      return Syntax.mkNumLit (first ++ String.join (rest.map pad))

/-- A univariate polynomial represented by its integer power coefficients. -/
abbrev IntPolynomial := List ℤ

/-- A bivariate polynomial represented by rows of integer power coefficients. -/
abbrev IntBivariate := List IntPolynomial

namespace IntPolynomial

/-- Add integer coefficient lists. -/
def add : IntPolynomial → IntPolynomial → IntPolynomial
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

/-- Negate every coefficient of an integer polynomial. -/
def neg (p : IntPolynomial) : IntPolynomial := p.map (- ·)

/-- Multiply every coefficient of an integer polynomial by an integer. -/
def scale (a : ℤ) (p : IntPolynomial) : IntPolynomial := p.map (a * ·)

/-- Multiply integer polynomials by convolution. -/
def mul : IntPolynomial → IntPolynomial → IntPolynomial
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

/-- The integer polynomial representing a constant. -/
def constant (a : ℤ) : IntPolynomial := [a]

end IntPolynomial

namespace IntBivariate

/-- Add rows of bivariate integer coefficients. -/
def add : IntBivariate → IntBivariate → IntBivariate
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => IntPolynomial.add a b :: add p q

/-- Negate every coefficient of a bivariate integer polynomial. -/
def neg (p : IntBivariate) : IntBivariate := p.map IntPolynomial.neg

/-- Multiply a bivariate polynomial by a polynomial in its second variable. -/
def scale (a : IntPolynomial) (p : IntBivariate) : IntBivariate :=
  p.map (IntPolynomial.mul a)

/-- Multiply every coefficient of a bivariate polynomial by an integer. -/
def scaleInt (a : ℤ) (p : IntBivariate) : IntBivariate :=
  p.map (fun q => q.map (a * ·))

/-- Multiply bivariate integer polynomials by row convolution. -/
def mul : IntBivariate → IntBivariate → IntBivariate
  | [], _ => []
  | a :: p, q => add (scale a q) ([] :: mul p q)

/-- The bivariate integer polynomial representing a constant. -/
def constant (a : ℤ) : IntBivariate := [[a]]

/-- The first coordinate polynomial. -/
def first : IntBivariate := [[], [1]]

/-- The second coordinate polynomial. -/
def second : IntBivariate := [[0, 1]]

/-- Read a coefficient, returning zero outside the stored rectangle. -/
def coefficient (p : IntBivariate) (i j : ℕ) : ℤ :=
  (p.getD i []).getD j 0

end IntBivariate

/-- A bivariate integer polynomial divided by a power of two. -/
structure ScaledPolynomial where
  exponent : ℕ
  numerator : IntBivariate

namespace ScaledPolynomial

/-- Compute a power of two in the integer coefficient ring. -/
def twoPow : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2 * twoPow n

/-- Raise the dyadic denominator exponent of an integer numerator. -/
def shift (n : ℕ) (p : IntBivariate) : IntBivariate :=
  IntBivariate.scaleInt (twoPow n) p

/-- Add scaled polynomials after aligning their dyadic denominators. -/
def add (p q : ScaledPolynomial) : ScaledPolynomial :=
  if _h : p.exponent ≤ q.exponent then
    ⟨q.exponent,
      IntBivariate.add (shift (q.exponent - p.exponent) p.numerator) q.numerator⟩
  else
    ⟨p.exponent,
      IntBivariate.add p.numerator (shift (p.exponent - q.exponent) q.numerator)⟩

/-- Negate a scaled polynomial. -/
def neg (p : ScaledPolynomial) : ScaledPolynomial :=
  ⟨p.exponent, IntBivariate.neg p.numerator⟩

/-- Multiply scaled polynomials. -/
def mul (p q : ScaledPolynomial) : ScaledPolynomial :=
  ⟨p.exponent + q.exponent, IntBivariate.mul p.numerator q.numerator⟩

/-- Raise a scaled polynomial to a natural power. -/
def pow (p : ScaledPolynomial) : ℕ → ScaledPolynomial
  | 0 => ⟨0, IntBivariate.constant 1⟩
  | n + 1 => mul (pow p n) p

/-- Embed an integer divided by a power of two as a constant polynomial. -/
def dyadic (numerator : ℤ) (exponent : ℕ) : ScaledPolynomial :=
  ⟨exponent, IntBivariate.constant numerator⟩

/-- The first coordinate as a scaled polynomial. -/
def first : ScaledPolynomial := ⟨0, IntBivariate.first⟩

/-- The second coordinate as a scaled polynomial. -/
def second : ScaledPolynomial := ⟨0, IntBivariate.second⟩

instance : Add ScaledPolynomial := ⟨add⟩
instance : Neg ScaledPolynomial := ⟨neg⟩
instance : Mul ScaledPolynomial := ⟨mul⟩
instance : Pow ScaledPolynomial ℕ := ⟨pow⟩

end ScaledPolynomial

/-- The reduced weighted-self formula evaluated in the dyadic polynomial algebra.
Only the integer constants and the half that actually occur in the formula are embedded. -/
def scaledWeightedSelfFormula (atom : Fin 18 → ScaledPolynomial)
    (r b t : ScaledPolynomial) : WeightedSelfFormula ScaledPolynomial :=
  let c := atom 0
  let B := atom 1
  let D := atom 2
  let A := atom 3
  let C := atom 4
  let lambda := atom 5
  let mu := atom 6
  let aB := atom 7
  let kappaB := atom 8
  let aD := atom 9
  let kappaD := atom 10
  let aA := atom 11
  let kappaA := atom 12
  let aC := atom 13
  let kappaC := atom 14
  let firstPenalty := atom 15
  let secondPenalty := atom 16
  let constantTerm := atom 17
  let one := ScaledPolynomial.dyadic 1 0
  let half := ScaledPolynomial.dyadic 1 1
  let two := ScaledPolynomial.dyadic 2 0
  let four := ScaledPolynomial.dyadic 4 0
  let sixteen := ScaledPolynomial.dyadic 16 0
  let k := half * (r ^ 2 + b ^ 2 + -(c ^ 2))
  let radicand := (one + -(t ^ 2)) * (r ^ 2 * b ^ 2 + -(k ^ 2))
  let qB := one + four * r ^ 2 + -(four * (r * t))
  let qA := one + r ^ 2 + -(two * (r * t))
  let uD := r * (one + four * b ^ 2 + -(D ^ 2)) + -(four * (k * t))
  let uC := r * (one + r ^ 2 + b ^ 2 +
      (two * k + -(two * (r * t))) + -(C ^ 2)) + -(two * (k * t))
  let FB := aB * qB + (one + lambda) * B * half +
    -(kappaB * (qB + -(B ^ 2)) ^ 2)
  let FA := aA * qA + mu * A * half + -(kappaA * (qA + -(A ^ 2)) ^ 2)
  let FD := aD * (D ^ 2 * r ^ 2 + r * uD) + D * half * r ^ 2 +
    -(kappaD * uD ^ 2)
  let FC := aC * (C ^ 2 * r ^ 2 + r * uC) + mu * C * half * r ^ 2 +
    -(kappaC * uC ^ 2)
  let p := one * (r ^ 2 *
      (((FB + FA + -(firstPenalty * r)) + -(secondPenalty * b)) + -constantTerm)) +
    ((FD + FC + -(sixteen * kappaD * radicand)) + -(four * kappaC * radicand))
  let q := four * (aD * r + -(two * kappaD * uD)) +
    two * (aC * r + -(two * kappaC * uC))
  ⟨p, q, radicand⟩

/-- The dyadic midpoint approximations of the eighteen weighted-self coefficients. -/
def bin4Atoms : Fin 18 → ScaledPolynomial := ![
  .dyadic 1524596944819 40,
  .dyadic 3159715121154 40,
  .dyadic 2247193809520 40,
  .dyadic 2094620947479 40,
  .dyadic 2278693482689 40,
  .dyadic 98380370149 40,
  .dyadic 1021268553918 40,
  .dyadic 208420083779 40,
  .dyadic 6041009426 40,
  .dyadic 268985659914 40,
  .dyadic 13621282339 40,
  .dyadic 268042924775 40,
  .dyadic 17577289049 40,
  .dyadic 246390455462 40,
  .dyadic 10817810015 40,
  .dyadic 413853097094 40,
  .dyadic 4365710208548 40,
  .dyadic 6131883299131 40]

/-- The bin-four dyadic formula, with the third cube coordinate supplied explicitly. -/
def bin4FormulaAt (z : ScaledPolynomial) : WeightedSelfFormula ScaledPolynomial :=
  let lower := ScaledPolynomial.dyadic 659706976666 40
  let upper := ScaledPolynomial.dyadic 769658139443 40
  let b := lower + (upper + -lower) * ScaledPolynomial.second
  let r := bin4Atoms 0 + -b +
    (ScaledPolynomial.dyadic 1 0 + -bin4Atoms 0 + b) * ScaledPolynomial.first
  let t := ScaledPolynomial.dyadic (-1) 0 + ScaledPolynomial.dyadic 2 0 * z
  scaledWeightedSelfFormula bin4Atoms r b t

/-- The constant coefficient of the nominal quadratic `P` in `z`. -/
def bin4A : ScaledPolynomial := (bin4FormulaAt (.dyadic 0 0)).p

/-- The constant coefficient of the nominal affine polynomial `Q` in `z`. -/
def bin4U : ScaledPolynomial := (bin4FormulaAt (.dyadic 0 0)).q

/-- The nominal formula at `z = 1/2`. -/
def bin4Mid : WeightedSelfFormula ScaledPolynomial := bin4FormulaAt (.dyadic 1 1)

/-- The nominal formula at `z = 1`. -/
def bin4AtOne : WeightedSelfFormula ScaledPolynomial := bin4FormulaAt (.dyadic 1 0)

/-- The quadratic coefficient of the nominal polynomial `P` in `z`. -/
def bin4C : ScaledPolynomial :=
  ScaledPolynomial.dyadic 2 0 *
    (bin4A + (bin4AtOne).p + -(ScaledPolynomial.dyadic 2 0 * bin4Mid.p))

/-- The linear coefficient of the nominal polynomial `P` in `z`. -/
def bin4B : ScaledPolynomial := (bin4AtOne).p + -bin4A + -bin4C

/-- The linear coefficient of the nominal polynomial `Q` in `z`. -/
def bin4V : ScaledPolynomial := (bin4AtOne).q + -bin4U

/-- The coefficient `H` in the nominal radicand `H z (1-z)`. -/
def bin4H : ScaledPolynomial := ScaledPolynomial.dyadic 4 0 * bin4Mid.radicand

/-- The linear coefficient of the nominal discriminant quartic in `z`. -/
def bin4D1 : ScaledPolynomial :=
  ScaledPolynomial.dyadic 2 0 * bin4A * bin4B + -(bin4H * bin4U ^ 2)

/-- The quadratic coefficient of the nominal discriminant quartic in `z`. -/
def bin4D2 : ScaledPolynomial :=
  bin4B ^ 2 + ScaledPolynomial.dyadic 2 0 * bin4A * bin4C +
    -(bin4H * (ScaledPolynomial.dyadic 2 0 * bin4U * bin4V + -(bin4U ^ 2)))

/-- The cubic coefficient of the nominal discriminant quartic in `z`. -/
def bin4D3 : ScaledPolynomial :=
  ScaledPolynomial.dyadic 2 0 * bin4B * bin4C +
    -(bin4H * (bin4V ^ 2 + -(ScaledPolynomial.dyadic 2 0 * bin4U * bin4V)))

/-- The quartic coefficient of the nominal discriminant in `z`. -/
def bin4D4 : ScaledPolynomial := bin4C ^ 2 + bin4H * bin4V ^ 2

/-- The rational Taylor center `3/32`. -/
def bin4Center : ScaledPolynomial := ScaledPolynomial.dyadic 3 5

/-- The nominal discriminant evaluated at the Taylor center. -/
def bin4CenterValue : ScaledPolynomial :=
  bin4A ^ 2 + bin4D1 * bin4Center + bin4D2 * bin4Center ^ 2 +
    bin4D3 * bin4Center ^ 3 + bin4D4 * bin4Center ^ 4

/-- The first Taylor coefficient of the nominal discriminant at the center. -/
def bin4CenterSlope : ScaledPolynomial :=
  bin4D1 + ScaledPolynomial.dyadic 2 0 * bin4D2 * bin4Center +
    ScaledPolynomial.dyadic 3 0 * bin4D3 * bin4Center ^ 2 +
    ScaledPolynomial.dyadic 4 0 * bin4D4 * bin4Center ^ 3

/-- A uniform lower model for the quadratic Taylor remainder. -/
def bin4LowerCurvature : ScaledPolynomial :=
  bin4D2 + ScaledPolynomial.dyadic 2 0 * bin4Center * bin4D3 +
    ScaledPolynomial.dyadic 3 0 * bin4Center ^ 2 * bin4D4 +
    -ScaledPolynomial.dyadic 3 4

/-- The affine coefficient in the nonconstant part of the Taylor remainder, including slack. -/
def bin4RemainderLinearSlack : ScaledPolynomial :=
  bin4D3 + ScaledPolynomial.dyadic 3 4 * bin4D4 + ScaledPolynomial.dyadic 3 4

/-- The slack in the elementary bound `bin4LowerCurvature ≤ 15`. -/
def bin4UpperCurvature : ScaledPolynomial :=
  ScaledPolynomial.dyadic 15 0 + -bin4LowerCurvature

/-- Forty times the completed-square budget, minus one. -/
def bin4Budget : ScaledPolynomial :=
  ScaledPolynomial.dyadic 40 0 *
    (ScaledPolynomial.dyadic 4 0 * bin4LowerCurvature * bin4CenterValue +
      -(bin4CenterSlope ^ 2)) + -ScaledPolynomial.dyadic 1 0

/-- Check one row of equality between two stored `13 × 13` coefficient arrays. -/
def rowEq13 (p q : IntBivariate) (i : Fin 13) : Bool :=
  decide (∀ j : Fin 13, p.coefficient i j = q.coefficient i j)

/-- Check one row of equality between two stored square coefficient arrays. -/
def rowEqN (n : ℕ) (p q : IntBivariate) (i : Fin n) : Bool :=
  decide (∀ j : Fin n, p.coefficient i j = q.coefficient i j)

/-- Check that a stored bivariate coefficient array has the requested square shape. -/
def matrixHasShape (n : ℕ) (p : IntBivariate) : Bool :=
  decide (p.length = n ∧ ∀ row ∈ p, row.length = n)

/-- Sum an integer-valued function on `Fin n` by primitive recursion. -/
def intSum : (n : ℕ) → (Fin n → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, f => f 0 + intSum n (fun i => f i.succ)

/-- Apply the first coordinate of integer power-to-Bernstein conversion. -/
def bernsteinFirstInteger (degree : ℕ) (binomialLcm : ℤ)
    (p : IntBivariate) (i j : Fin (degree + 1)) : ℤ :=
  intSum (degree + 1) fun h => if (h : ℕ) ≤ i then
    p.coefficient h j * Nat.choose i h * (binomialLcm / Nat.choose degree h)
  else 0

/-- Apply integer power-to-Bernstein conversion in both coordinates. -/
def bernsteinInteger (degree : ℕ) (binomialLcm : ℤ)
    (p : IntBivariate) (i j : Fin (degree + 1)) : ℤ :=
  intSum (degree + 1) fun h => if (h : ℕ) ≤ j then
    bernsteinFirstInteger degree binomialLcm p i h * Nat.choose j h *
      (binomialLcm / Nat.choose degree h)
  else 0

/-- Check nonnegativity of one row of converted integer Bernstein coefficients. -/
def bernsteinRowNonnegativeN (degree : ℕ) (binomialLcm : ℤ)
    (power : IntBivariate) (i : Fin (degree + 1)) : Bool :=
  decide (∀ j : Fin (degree + 1),
    0 ≤ bernsteinInteger degree binomialLcm power i j)

open scoped BigOperators unitInterval

namespace IntPolynomial

/-- Evaluate an integer coefficient list by Horner's rule. -/
def eval : IntPolynomial → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => a + x * eval p x

/-- Evaluation turns coefficient-list addition into real addition. -/
theorem eval_add (p q : IntPolynomial) (x : ℝ) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
      cases q with
      | nil => simp [add, eval]
      | cons b q => simp [add, eval, ih]; ring

/-- Evaluation commutes with negation of integer polynomials. -/
theorem eval_neg (p : IntPolynomial) (x : ℝ) : eval (neg p) x = -eval p x := by
  induction p with
  | nil => simp [neg, eval]
  | cons a p ih =>
      change ((-a : ℤ) : ℝ) + x * eval (neg p) x = -((a : ℝ) + x * eval p x)
      rw [ih]
      push_cast
      ring

/-- Evaluation commutes with integer scaling. -/
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

/-- Evaluation turns coefficient convolution into real multiplication. -/
theorem eval_mul (p q : IntPolynomial) (x : ℝ) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih => simp [mul, eval, eval_add, eval_scale, ih]; ring

end IntPolynomial

namespace IntBivariate

/-- Evaluate a bivariate integer coefficient list by nested Horner evaluation. -/
def eval : IntBivariate → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | p :: ps, x, y => IntPolynomial.eval p y + x * eval ps x y

/-- Evaluation turns bivariate coefficient addition into real addition. -/
theorem eval_add (p q : IntBivariate) (x y : ℝ) :
    eval (add p q) x y = eval p x y + eval q x y := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
      cases q with
      | nil => simp [add, eval]
      | cons b q => simp [add, eval, IntPolynomial.eval_add, ih]; ring

/-- Evaluation commutes with negation of bivariate polynomials. -/
theorem eval_neg (p : IntBivariate) (x y : ℝ) : eval (neg p) x y = -eval p x y := by
  induction p with
  | nil => simp [neg, eval]
  | cons a p ih =>
      change IntPolynomial.eval (IntPolynomial.neg a) y + x * eval (neg p) x y =
        -(IntPolynomial.eval a y + x * eval p x y)
      rw [IntPolynomial.eval_neg, ih]
      ring

/-- Evaluation respects scaling by a polynomial in the second variable. -/
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
theorem eval_scaleInt (a : ℤ) (p : IntBivariate) (x y : ℝ) :
    eval (scaleInt a p) x y = a * eval p x y := by
  induction p with
  | nil => simp [scaleInt, eval]
  | cons b p ih =>
      change IntPolynomial.eval (IntPolynomial.scale a b) y + x * eval (scaleInt a p) x y =
        (a : ℝ) * (IntPolynomial.eval b y + x * eval p x y)
      rw [IntPolynomial.eval_scale, ih]
      ring

/-- Evaluation turns bivariate coefficient convolution into multiplication. -/
theorem eval_mul (p q : IntBivariate) (x y : ℝ) :
    eval (mul p q) x y = eval p x y * eval q x y := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih =>
      simp [mul, eval, eval_add, eval_scale, ih, IntPolynomial.eval]
      ring

/-- Read an integer-scaled coefficient by scaling the original coefficient. -/
theorem coefficient_scaleInt (a : ℤ) (p : IntBivariate) (i j : ℕ) :
    (scaleInt a p).coefficient i j = a * p.coefficient i j := by
  simp only [coefficient, scaleInt, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hrow : p[i]? with
  | none => simp
  | some row =>
      simp only [Option.map_some, Option.getD_some, List.getElem?_map]
      cases hcoeff : row[j]? <;> simp

end IntBivariate

namespace ScaledPolynomial

/-- Evaluate a scaled integer polynomial at a real point. -/
def eval (p : ScaledPolynomial) (x y : ℝ) : ℝ :=
  IntBivariate.eval p.numerator x y / (2 : ℝ) ^ p.exponent

/-- The recursive integer `twoPow` agrees with ordinary exponentiation. -/
theorem twoPow_eq (n : ℕ) : twoPow n = (2 : ℤ) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [twoPow, pow_succ, ih, mul_comm]

/-- Denominator alignment scales evaluation by the corresponding power of two. -/
theorem eval_shift (n : ℕ) (p : IntBivariate) (x y : ℝ) :
    IntBivariate.eval (shift n p) x y = (2 : ℝ) ^ n * IntBivariate.eval p x y := by
  simp [shift, IntBivariate.eval_scaleInt, twoPow_eq]

/-- Evaluation preserves addition of scaled polynomials. -/
theorem eval_add (p q : ScaledPolynomial) (x y : ℝ) :
    eval (add p q) x y = eval p x y + eval q x y := by
  rw [eval, add]
  split_ifs with h
  · rw [IntBivariate.eval_add, eval_shift]
    have hpow : (2 : ℝ) ^ q.exponent =
        2 ^ (q.exponent - p.exponent) * 2 ^ p.exponent := by
      rw [← pow_add, Nat.sub_add_cancel h]
    dsimp only [eval]
    rw [hpow]
    field_simp
  · rw [IntBivariate.eval_add, eval_shift]
    have hle : q.exponent ≤ p.exponent := Nat.le_of_not_ge h
    have hpow : (2 : ℝ) ^ p.exponent =
        2 ^ (p.exponent - q.exponent) * 2 ^ q.exponent := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    dsimp only [eval]
    rw [hpow]
    field_simp

/-- Evaluation preserves negation of scaled polynomials. -/
theorem eval_neg (p : ScaledPolynomial) (x y : ℝ) : eval (neg p) x y = -eval p x y := by
  rw [eval, neg, IntBivariate.eval_neg]
  dsimp only [eval]
  ring

/-- Evaluation preserves multiplication of scaled polynomials. -/
theorem eval_mul (p q : ScaledPolynomial) (x y : ℝ) :
    eval (mul p q) x y = eval p x y * eval q x y := by
  rw [eval, mul, IntBivariate.eval_mul, pow_add]
  dsimp only [eval]
  field_simp

/-- Evaluation preserves natural powers of scaled polynomials. -/
theorem eval_pow (p : ScaledPolynomial) (n : ℕ) (x y : ℝ) :
    eval (pow p n) x y = eval p x y ^ n := by
  induction n with
  | zero => simp [pow, eval, IntBivariate.constant, IntBivariate.eval,
      IntPolynomial.eval]
  | succ n ih => simp [pow, eval_mul, ih, pow_succ]

/-- Evaluation of a constant dyadic polynomial gives its represented quotient. -/
theorem eval_dyadic (numerator : ℤ) (exponent : ℕ) (x y : ℝ) :
    eval (dyadic numerator exponent) x y = numerator / (2 : ℝ) ^ exponent := by
  simp [eval, dyadic, IntBivariate.constant, IntBivariate.eval, IntPolynomial.eval]

/-- Evaluation preserves additive notation. -/
@[simp] theorem eval_add_notation (p q : ScaledPolynomial) (x y : ℝ) :
    eval (p + q) x y = eval p x y + eval q x y := eval_add p q x y

/-- Evaluation preserves negation notation. -/
@[simp] theorem eval_neg_notation (p : ScaledPolynomial) (x y : ℝ) :
    eval (-p) x y = -eval p x y := eval_neg p x y

/-- Evaluation preserves multiplication notation. -/
@[simp] theorem eval_mul_notation (p q : ScaledPolynomial) (x y : ℝ) :
    eval (p * q) x y = eval p x y * eval q x y := eval_mul p q x y

/-- Evaluation preserves power notation. -/
@[simp] theorem eval_pow_notation (p : ScaledPolynomial) (n : ℕ) (x y : ℝ) :
    eval (p ^ n) x y = eval p x y ^ n := eval_pow p n x y

end ScaledPolynomial

/-- Evaluation of the specialized dyadic formula agrees with the exact real formula. -/
theorem eval_scaledWeightedSelfFormula (atom : Fin 18 → ScaledPolynomial)
    (r b t : ScaledPolynomial) (x y : ℝ) :
    let source := scaledWeightedSelfFormula atom r b t
    let target := weightedSelfFormula weightedSelfRealFormulaOperations
      (fun i ↦ ScaledPolynomial.eval (atom i) x y)
      (ScaledPolynomial.eval r x y) (ScaledPolynomial.eval b x y)
      (ScaledPolynomial.eval t x y)
    ScaledPolynomial.eval source.p x y = target.p ∧
      ScaledPolynomial.eval source.q x y = target.q ∧
      ScaledPolynomial.eval source.radicand x y = target.radicand := by
  simp only [scaledWeightedSelfFormula, weightedSelfFormula,
    weightedSelfRealFormulaOperations, ScaledPolynomial.eval_add_notation,
    ScaledPolynomial.eval_neg_notation, ScaledPolynomial.eval_mul_notation,
    ScaledPolynomial.eval_pow_notation, ScaledPolynomial.eval_dyadic]
  norm_num

/-- The `bin4FormulaAt` construction has the real semantics supplied by the formula map. -/
theorem eval_bin4FormulaAt (z : ScaledPolynomial) (x y : ℝ) :
    let lower := ScaledPolynomial.dyadic 659706976666 40
    let upper := ScaledPolynomial.dyadic 769658139443 40
    let b := lower + (upper + -lower) * ScaledPolynomial.second
    let r := bin4Atoms 0 + -b +
      (ScaledPolynomial.dyadic 1 0 + -bin4Atoms 0 + b) * ScaledPolynomial.first
    let t := ScaledPolynomial.dyadic (-1) 0 + ScaledPolynomial.dyadic 2 0 * z
    let target := weightedSelfFormula weightedSelfRealFormulaOperations
      (fun i ↦ ScaledPolynomial.eval (bin4Atoms i) x y)
      (ScaledPolynomial.eval r x y) (ScaledPolynomial.eval b x y)
      (ScaledPolynomial.eval t x y)
    ScaledPolynomial.eval (bin4FormulaAt z).p x y = target.p ∧
      ScaledPolynomial.eval (bin4FormulaAt z).q x y = target.q ∧
      ScaledPolynomial.eval (bin4FormulaAt z).radicand x y = target.radicand := by
  simpa only [bin4FormulaAt] using eval_scaledWeightedSelfFormula bin4Atoms
    (let lower := ScaledPolynomial.dyadic 659706976666 40
     let upper := ScaledPolynomial.dyadic 769658139443 40
     let b := lower + (upper + -lower) * ScaledPolynomial.second
     bin4Atoms 0 + -b +
       (ScaledPolynomial.dyadic 1 0 + -bin4Atoms 0 + b) * ScaledPolynomial.first)
    (let lower := ScaledPolynomial.dyadic 659706976666 40
     let upper := ScaledPolynomial.dyadic 769658139443 40
     lower + (upper + -lower) * ScaledPolynomial.second)
    (ScaledPolynomial.dyadic (-1) 0 + ScaledPolynomial.dyadic 2 0 * z) x y

namespace IntPolynomial

private theorem eval_eq_fin_sum (p : IntPolynomial) (x : ℝ) :
    eval p x = ∑ i : Fin p.length, (p.get i : ℝ) * x ^ (i : ℕ) := by
  induction p with
  | nil => simp [eval]
  | cons a p ih =>
      simp only [List.length_cons]
      rw [eval, Fin.sum_univ_succ]
      simp only [List.get_cons_zero, Fin.val_zero, pow_zero, mul_one]
      congr 1
      rw [ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (a :: p).get i.succ = p.get i by rfl]
      simp only [Fin.val_succ]
      ring

end IntPolynomial

namespace IntBivariate

private theorem eval_eq_fin_sum (p : IntBivariate) (x y : ℝ) :
    eval p x y = ∑ i : Fin p.length, IntPolynomial.eval (p.get i) y * x ^ (i : ℕ) := by
  induction p with
  | nil => simp [eval]
  | cons a p ih =>
      simp only [List.length_cons]
      rw [eval, Fin.sum_univ_succ]
      simp only [List.get_cons_zero, Fin.val_zero, pow_zero, mul_one]
      congr 1
      rw [ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (a :: p).get i.succ = p.get i by rfl]
      simp only [Fin.val_succ]
      ring

/-- A rectangular coefficient identity identifies raw and padded tensor evaluation. -/
theorem eval_eq_paddedPowerTensorEval_of_coefficients (degree : ℕ) (p : IntBivariate)
    (a : Fin (degree + 1) → Fin (degree + 1) → ℤ)
    (hp : p.length = degree + 1)
    (hrows : ∀ row ∈ p, row.length = degree + 1)
    (hcoeff : ∀ (i j : Fin (degree + 1)), p.coefficient i j = a i j) (x y : I) :
    eval p x y = Bescovitch.paddedPowerTensorEval (fun i j ↦ (a i j : ℝ)) x y := by
  rw [eval_eq_fin_sum, Bescovitch.paddedPowerTensorEval]
  rw [← (finCongr hp).sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  have hrow : (p.get i).length = degree + 1 := hrows _ (List.get_mem p i)
  rw [IntPolynomial.eval_eq_fin_sum]
  rw [← (finCongr hrow).sum_comp]
  calc
    (∑ j, ((p.get i).get j : ℝ) * (y : ℝ) ^ (j : ℕ)) * (x : ℝ) ^ (i : ℕ) =
        (∑ j, (a (finCongr hp i) (finCongr hrow j) : ℝ) *
          (y : ℝ) ^ (j : ℕ)) * (x : ℝ) ^ (i : ℕ) := by
      apply congrArg (· * (x : ℝ) ^ (i : ℕ))
      apply Finset.sum_congr rfl
      intro j hjmem
      have hi : finCongr hp i = ⟨i, hp ▸ i.isLt⟩ := rfl
      have hj : finCongr hrow j = ⟨j, hrow ▸ j.isLt⟩ := rfl
      rw [show ((p.get i).get j : ℤ) = a (finCongr hp i) (finCongr hrow j) by
        simpa [coefficient, hi, hj] using hcoeff (finCongr hp i) (finCongr hrow j)]
    _ = ∑ j, (a (finCongr hp i) (finCongr hrow j) : ℝ) *
        (x : ℝ) ^ (finCongr hp i : ℕ) * (y : ℝ) ^ (finCongr hrow j : ℕ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hjmem
      simp only [finCongr_apply_coe]
      ring

end IntBivariate

/-- The left Bernstein coefficient of the negative nominal quadratic in `z`. -/
def bin4NegativePLeft : ScaledPolynomial := -bin4A

/-- The middle Bernstein coefficient of the negative nominal quadratic in `z`. -/
def bin4NegativePMiddle : ScaledPolynomial :=
  -(bin4A + ScaledPolynomial.dyadic 1 1 * bin4B)

/-- The right Bernstein coefficient of the negative nominal quadratic in `z`. -/
def bin4NegativePRight : ScaledPolynomial := -(bin4A + bin4B + bin4C)

/-- One hundred times the left coefficient, minus the target margin `29`. -/
def bin4NegativePLeftMargin : ScaledPolynomial :=
  ScaledPolynomial.dyadic 100 0 * bin4NegativePLeft +
    -ScaledPolynomial.dyadic 29 0

/-- One hundred times the middle coefficient, minus the target margin `29`. -/
def bin4NegativePMiddleMargin : ScaledPolynomial :=
  ScaledPolynomial.dyadic 100 0 * bin4NegativePMiddle +
    -ScaledPolynomial.dyadic 29 0

/-- One hundred times the right coefficient, minus the target margin `29`. -/
def bin4NegativePRightMargin : ScaledPolynomial :=
  ScaledPolynomial.dyadic 100 0 * bin4NegativePRight +
    -ScaledPolynomial.dyadic 29 0

end

end WeightedSelfTaylorBin4
end Bescovitch
