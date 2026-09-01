/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.List.GetD
public import Mathlib.Data.Int.Notation

/-!
# Exact dyadic trivariate polynomials

Finite integer coefficient lists represent dyadic polynomials in three variables.
-/

@[expose] public section

namespace Bescovitch.DyadicTrivariatePolynomial

noncomputable section

open Lean Macro

/-- Concatenate decimal chunks, padding every chunk after the first to sixty digits. -/
syntax "decimal60![" num,+ "]" : term

macro_rules
  | `(decimal60![$ns:num,*]) => do
      let parts := ns.getElems.toList.map fun n ↦ toString n.getNat
      let first :: rest := parts | Macro.throwError "expected at least one decimal chunk"
      let pad (s : String) := String.join (List.replicate (60 - s.length) "0") ++ s
      return Syntax.mkNumLit (first ++ String.join (rest.map pad))

/-- Integer coefficients in increasing power order. -/
abbrev IntPolynomial := List ℤ

/-- Integer bivariate power coefficients, grouped by the first exponent. -/
abbrev IntBivariate := List IntPolynomial

/-- Integer trivariate power coefficients, grouped by the first two exponents. -/
abbrev IntTrivariate := List IntBivariate

namespace IntPolynomial

/-- Add integer power-coefficient lists. -/
def add : IntPolynomial → IntPolynomial → IntPolynomial
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

/-- Negate an integer power-coefficient list. -/
def neg (p : IntPolynomial) : IntPolynomial := p.map (- ·)

/-- Multiply every coefficient by an integer. -/
def scale (a : ℤ) (p : IntPolynomial) : IntPolynomial := p.map (a * ·)

/-- Multiply integer univariate power-coefficient lists. -/
def mul : IntPolynomial → IntPolynomial → IntPolynomial
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)
end IntPolynomial

namespace IntBivariate

/-- Add integer bivariate power-coefficient lists. -/
def add : IntBivariate → IntBivariate → IntBivariate
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => IntPolynomial.add a b :: add p q

/-- Negate integer bivariate power coefficients. -/
def neg (p : IntBivariate) : IntBivariate := p.map IntPolynomial.neg

/-- Multiply a bivariate polynomial by a univariate polynomial in its second variable. -/
def scale (a : IntPolynomial) (p : IntBivariate) : IntBivariate :=
  p.map (IntPolynomial.mul a)

/-- Multiply every bivariate coefficient by an integer. -/
def scaleInt (a : ℤ) (p : IntBivariate) : IntBivariate :=
  p.map (fun q ↦ q.map (a * ·))

/-- Multiply integer bivariate power-coefficient lists. -/
def mul : IntBivariate → IntBivariate → IntBivariate
  | [], _ => []
  | a :: p, q => add (scale a q) ([] :: mul p q)
end IntBivariate

namespace IntTrivariate

/-- Add integer trivariate power-coefficient lists. -/
def add : IntTrivariate → IntTrivariate → IntTrivariate
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => IntBivariate.add a b :: add p q

/-- Negate integer trivariate power coefficients. -/
def neg (p : IntTrivariate) : IntTrivariate := p.map IntBivariate.neg

/-- Multiply a trivariate polynomial by a bivariate polynomial in its last variables. -/
def scale (a : IntBivariate) (p : IntTrivariate) : IntTrivariate :=
  p.map (IntBivariate.mul a)

/-- Multiply every trivariate coefficient by an integer. -/
def scaleInt (a : ℤ) (p : IntTrivariate) : IntTrivariate :=
  p.map (IntBivariate.scaleInt a)

/-- Multiply integer trivariate power-coefficient lists. -/
def mul : IntTrivariate → IntTrivariate → IntTrivariate
  | [], _ => []
  | a :: p, q => add (scale a q) ([] :: mul p q)

/-- The constant integer trivariate polynomial. -/
def constant (a : ℤ) : IntTrivariate := [[[a]]]

/-- The first coordinate polynomial. -/
def first : IntTrivariate := [[], [[1]]]

/-- The second coordinate polynomial. -/
def second : IntTrivariate := [[[], [1]]]

/-- The third coordinate polynomial. -/
def third : IntTrivariate := [[[0, 1]]]

/-- Read a trivariate coefficient, returning zero outside the stored support. -/
def coefficient (p : IntTrivariate) (i j k : ℕ) : ℤ :=
  ((p.getD i []).getD j []).getD k 0

end IntTrivariate

/-- An integer trivariate numerator divided by a nonnegative power of two. -/
structure ScaledPolynomial where
  /-- The power of two in the denominator. -/
  exponent : ℕ
  /-- The integer power coefficients of the numerator. -/
  numerator : IntTrivariate

namespace ScaledPolynomial

/-- Multiply integer coefficients by a power of two. -/
def shift (n : ℕ) (p : IntTrivariate) : IntTrivariate :=
  IntTrivariate.scaleInt ((2 : ℤ) ^ n) p

/-- Add scaled polynomials after aligning their dyadic denominators. -/
def add (p q : ScaledPolynomial) : ScaledPolynomial :=
  if _h : p.exponent ≤ q.exponent then
    ⟨q.exponent,
      IntTrivariate.add (shift (q.exponent - p.exponent) p.numerator) q.numerator⟩
  else
    ⟨p.exponent,
      IntTrivariate.add p.numerator (shift (p.exponent - q.exponent) q.numerator)⟩

/-- Negate a scaled polynomial. -/
def neg (p : ScaledPolynomial) : ScaledPolynomial :=
  ⟨p.exponent, IntTrivariate.neg p.numerator⟩

/-- Multiply scaled polynomials. -/
def mul (p q : ScaledPolynomial) : ScaledPolynomial :=
  ⟨p.exponent + q.exponent, IntTrivariate.mul p.numerator q.numerator⟩

/-- Raise a scaled polynomial to a natural power. -/
def pow (p : ScaledPolynomial) : ℕ → ScaledPolynomial
  | 0 => ⟨0, IntTrivariate.constant 1⟩
  | n + 1 => mul (pow p n) p

/-- Embed an integer divided by a power of two as a constant polynomial. -/
def dyadic (numerator : ℤ) (exponent : ℕ) : ScaledPolynomial :=
  ⟨exponent, IntTrivariate.constant numerator⟩

/-- The first coordinate as a scaled polynomial. -/
def first : ScaledPolynomial := ⟨0, IntTrivariate.first⟩

/-- The second coordinate as a scaled polynomial. -/
def second : ScaledPolynomial := ⟨0, IntTrivariate.second⟩

/-- The third coordinate as a scaled polynomial. -/
def third : ScaledPolynomial := ⟨0, IntTrivariate.third⟩

instance : Add ScaledPolynomial := ⟨add⟩
instance : Neg ScaledPolynomial := ⟨neg⟩
instance : Mul ScaledPolynomial := ⟨mul⟩
instance : Pow ScaledPolynomial ℕ := ⟨pow⟩

end ScaledPolynomial

/-- Pad an integer coefficient list into the fixed 13 × 13 × 5 tensor. -/
def powerTensor (p : IntTrivariate) : Fin 13 → Fin 13 → Fin 5 → ℤ :=
  fun i j k ↦ p.coefficient i j k

/-- Check equality of one row of two padded coefficient tensors. -/
def tensorRowEq (p q : IntTrivariate) (i : Fin 13) : Bool :=
  decide (∀ j k, powerTensor p i j k = powerTensor q i j k)

/-- A successful tensor-row equality check is pointwise sound. -/
theorem tensor_row_eq_sound {p q : IntTrivariate} {i : Fin 13}
    (h : tensorRowEq p q i = true) :
    ∀ j k, powerTensor p i j k = powerTensor q i j k :=
  of_decide_eq_true h

/-- Check that a coefficient list fits the fixed 12 × 12 × 4 degree box. -/
def fitsDegreeBox (p : IntTrivariate) : Bool :=
  decide (p.length ≤ 13) && p.all fun slice ↦
    decide (slice.length ≤ 13) && slice.all fun row ↦ decide (row.length ≤ 5)

/-- A successful degree-box check gives all three support bounds. -/
theorem fits_degree_box_sound {p : IntTrivariate} (h : fitsDegreeBox p = true) :
    p.length ≤ 13 ∧
      (∀ slice ∈ p, slice.length ≤ 13) ∧
      (∀ slice ∈ p, ∀ row ∈ slice, row.length ≤ 5) := by
  rw [fitsDegreeBox, Bool.and_eq_true_iff] at h
  refine ⟨of_decide_eq_true h.1, ?_⟩
  rw [List.all_eq_true] at h
  constructor
  · intro slice hslice
    have hs := h.2 slice hslice
    rw [Bool.and_eq_true_iff] at hs
    exact of_decide_eq_true hs.1
  · intro slice hslice row hrow
    have hs := h.2 slice hslice
    rw [Bool.and_eq_true_iff] at hs
    rw [List.all_eq_true] at hs
    exact of_decide_eq_true (hs.2 row hrow)

end

end Bescovitch.DyadicTrivariatePolynomial
