/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.IntervalPolynomial
public import Bescovitch.Certificates.RadicalBernstein

/-!
# Interval-Horner certificates

This file evaluates interval-coefficient polynomials by Horner's rule. Adaptive rational box
subdivision turns a nonnegative lower endpoint at every leaf into an exact polynomial bound.
-/

@[expose] public section

namespace Bescovitch

namespace IntervalUnivariate

/-- Evaluate an interval polynomial over an interval argument by Horner's rule. -/
def evalOn : IntervalUnivariate → RationalInterval → RationalInterval
  | [], _ => .singleton 0
  | a :: p, X => a.add (X.mul (evalOn p X))

private theorem evalOn_contains {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalUnivariate} {p : RadicalUnivariate n}
    (h : P.Contains input p) {X : RationalInterval} {x : ℝ} (hx : X.Contains x) :
    (P.evalOn X).Contains (p.eval input x) := by
  induction h with
  | nil => simpa [evalOn, RadicalUnivariate.eval] using RationalInterval.singleton_contains 0
  | cons hhead htail ih =>
      exact RationalInterval.add_contains hhead (RationalInterval.mul_contains hx ih)

end IntervalUnivariate

namespace IntervalBivariate

/-- Evaluate an interval bivariate polynomial over an interval box. -/
def evalOn : IntervalBivariate → RationalInterval → RationalInterval → RationalInterval
  | [], _, _ => .singleton 0
  | a :: p, X, Y => (IntervalUnivariate.evalOn a Y).add (X.mul (evalOn p X Y))

private theorem evalOn_contains {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalBivariate} {p : RadicalBivariate n} (h : P.Contains input p)
    {X Y : RationalInterval} {x y : ℝ} (hx : X.Contains x) (hy : Y.Contains y) :
    (P.evalOn X Y).Contains (p.eval input x y) := by
  induction h with
  | nil => simpa [evalOn, RadicalBivariate.eval] using RationalInterval.singleton_contains 0
  | cons hhead htail ih =>
      exact RationalInterval.add_contains (IntervalUnivariate.evalOn_contains hhead hy)
        (RationalInterval.mul_contains hx ih)

end IntervalBivariate

namespace IntervalTrivariate

/-- Evaluate an interval trivariate polynomial over an interval box. -/
def evalOn (P : IntervalTrivariate) (X Y Z : RationalInterval) : RationalInterval :=
  match P with
  | [] => .singleton 0
  | a :: p => (IntervalBivariate.evalOn a Y Z).add (X.mul (evalOn p X Y Z))

private theorem evalOn_contains {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalTrivariate} {p : RadicalTrivariate n} (h : P.Contains input p)
    {X Y Z : RationalInterval} {x y z : ℝ}
    (hx : X.Contains x) (hy : Y.Contains y) (hz : Z.Contains z) :
    (P.evalOn X Y Z).Contains (p.eval input x y z) := by
  induction h with
  | nil => simpa [evalOn, RadicalTrivariate.eval] using RationalInterval.singleton_contains 0
  | cons hhead htail ih =>
      exact RationalInterval.add_contains (IntervalBivariate.evalOn_contains hhead hy hz)
        (RationalInterval.mul_contains hx ih)

end IntervalTrivariate

namespace RationalInterval

/-- The rational unit interval. -/
def unit : RationalInterval := ⟨0, 1, by norm_num⟩

/-- The left half of a rational interval. -/
def leftHalf (I : RationalInterval) : RationalInterval :=
  ⟨I.lower, (I.lower + I.upper) / 2, by linarith [I.lower_le_upper]⟩

/-- The right half of a rational interval. -/
def rightHalf (I : RationalInterval) : RationalInterval :=
  ⟨(I.lower + I.upper) / 2, I.upper, by linarith [I.lower_le_upper]⟩

private theorem contains_leftHalf_or_rightHalf {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) : I.leftHalf.Contains x ∨ I.rightHalf.Contains x := by
  by_cases hmid : x ≤ ((I.lower + I.upper) / 2 : ℚ)
  · left
    exact ⟨hx.1, by exact_mod_cast hmid⟩
  · right
    constructor
    · exact_mod_cast le_of_not_ge hmid
    · exact hx.2

end RationalInterval

/-- Check interval-Horner lower bounds after recursively bisecting a rational box. -/
def intervalPolynomialSubdivisionCertifiesNonnegative :
    TensorSubdivision → IntervalTrivariate → RationalInterval → RationalInterval →
      RationalInterval → Bool
  | .leaf, P, X, Y, Z => decide (0 ≤ (P.evalOn X Y Z).lower)
  | .splitFirst left right, P, X, Y, Z =>
      intervalPolynomialSubdivisionCertifiesNonnegative left P X.leftHalf Y Z &&
        intervalPolynomialSubdivisionCertifiesNonnegative right P X.rightHalf Y Z
  | .splitSecond left right, P, X, Y, Z =>
      intervalPolynomialSubdivisionCertifiesNonnegative left P X Y.leftHalf Z &&
        intervalPolynomialSubdivisionCertifiesNonnegative right P X Y.rightHalf Z
  | .splitThird left right, P, X, Y, Z =>
      intervalPolynomialSubdivisionCertifiesNonnegative left P X Y Z.leftHalf &&
        intervalPolynomialSubdivisionCertifiesNonnegative right P X Y Z.rightHalf

/-- A successful interval-Horner subdivision check proves exact polynomial nonnegativity. -/
theorem RadicalTrivariate.nonneg_of_interval_box_certificate {n : ℕ}
    (p : RadicalTrivariate n) (P : IntervalTrivariate) (input : Fin n → ℝ)
    (hcontains : P.Contains input p) (tree : TensorSubdivision)
    {X Y Z : RationalInterval} {x y z : ℝ}
    (hcertificate : intervalPolynomialSubdivisionCertifiesNonnegative tree P X Y Z = true)
    (hx : X.Contains x) (hy : Y.Contains y) (hz : Z.Contains z) :
    0 ≤ p.eval input x y z := by
  induction tree generalizing X Y Z x y z with
  | leaf =>
      have hlower : 0 ≤ (P.evalOn X Y Z).lower := of_decide_eq_true hcertificate
      have hvalue := IntervalTrivariate.evalOn_contains hcontains hx hy hz
      exact (by exact_mod_cast hlower : (0 : ℝ) ≤ (P.evalOn X Y Z).lower).trans hvalue.1
  | splitFirst left right ihLeft ihRight =>
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases RationalInterval.contains_leftHalf_or_rightHalf hx with hx | hx
      · exact ihLeft hparts.1 hx hy hz
      · exact ihRight hparts.2 hx hy hz
  | splitSecond left right ihLeft ihRight =>
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases RationalInterval.contains_leftHalf_or_rightHalf hy with hy | hy
      · exact ihLeft hparts.1 hx hy hz
      · exact ihRight hparts.2 hx hy hz
  | splitThird left right ihLeft ihRight =>
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases RationalInterval.contains_leftHalf_or_rightHalf hz with hz | hz
      · exact ihLeft hparts.1 hx hy hz
      · exact ihRight hparts.2 hx hy hz

end Bescovitch
