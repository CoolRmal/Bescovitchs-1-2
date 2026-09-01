/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateCore

/-!
# Direct interval evaluation of the weighted-self formula

The linear coefficient `Q` is nonnegative on every radius bin without subdividing the parameter
cube.  This file checks that fact directly in the original reduced formula, avoiding an
expanded polynomial or a separate replay certificate.
-/

@[expose] public section

namespace Bescovitch

/-- Rational interval operations used to evaluate the reduced weighted-self formula. -/
def weightedSelfRationalIntervalOperations :
    WeightedSelfFormulaOperations RationalInterval :=
  ⟨RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
    RationalInterval.mul, RationalInterval.pow⟩

/-- Direct interval evaluation of the affine unit-cube chart. -/
def weightedSelfDirectIntervalChart (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) (X Y Z : RationalInterval) :
    WeightedSelfChart RationalInterval :=
  let sub p q := RationalInterval.add p (RationalInterval.neg q)
  let b := RationalInterval.add (RationalInterval.singleton lower)
    (RationalInterval.mul (RationalInterval.singleton (upper - lower)) Y)
  let r := RationalInterval.add (sub (box 0) b)
    (RationalInterval.mul
      (RationalInterval.add (sub (RationalInterval.singleton 1) (box 0)) b) X)
  let t := RationalInterval.add (RationalInterval.singleton (-1))
    (RationalInterval.mul (RationalInterval.singleton 2) Z)
  ⟨r, b, t⟩

/-- Direct interval evaluation of the reduced formula on one parameter box. -/
def weightedSelfDirectIntervalFormula (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) (X Y Z : RationalInterval) :
    WeightedSelfFormula RationalInterval :=
  let chart := weightedSelfDirectIntervalChart lower upper box X Y Z
  weightedSelfFormula weightedSelfRationalIntervalOperations box chart.r chart.b chart.t

/-- The lower endpoint of the direct interval evaluation certifies `Q ≥ 0`. -/
def weightedSelfDirectQCertifiesNonnegative (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) (X Y Z : RationalInterval) : Bool :=
  decide (0 ≤ (weightedSelfDirectIntervalFormula lower upper box X Y Z).q.lower)

private theorem weightedSelfDirectIntervalChart_contains
    (lower upper : ℚ) (box : Fin 18 → RationalInterval) (input : Fin 18 → ℝ)
    (hinput : ∀ i, (box i).Contains (input i))
    {X Y Z : RationalInterval} {x y z : ℝ}
    (hx : X.Contains x) (hy : Y.Contains y) (hz : Z.Contains z) :
    let intervalChart := weightedSelfDirectIntervalChart lower upper box X Y Z
    let b : ℝ := lower + (upper - lower) * y
    let realChart : WeightedSelfChart ℝ :=
      ⟨input 0 - b + (1 - input 0 + b) * x, b, -1 + 2 * z⟩
    intervalChart.r.Contains realChart.r ∧ intervalChart.b.Contains realChart.b ∧
      intervalChart.t.Contains realChart.t := by
  dsimp only [weightedSelfDirectIntervalChart]
  let intervalB := RationalInterval.add (RationalInterval.singleton lower)
    (RationalInterval.mul (RationalInterval.singleton (upper + -lower)) Y)
  let realB : ℝ := lower + (upper + -lower) * y
  have hwidth : (RationalInterval.singleton (upper + -lower)).Contains
      ((upper : ℝ) + -lower) := by
    simpa only [Rat.cast_add, Rat.cast_neg] using
      RationalInterval.singleton_contains (upper + -lower)
  have hone : (RationalInterval.singleton 1).Contains (1 : ℝ) := by
    simpa only [Rat.cast_one] using RationalInterval.singleton_contains 1
  have hnegativeOne : (RationalInterval.singleton (-1)).Contains (-1 : ℝ) := by
    simpa only [Rat.cast_neg, Rat.cast_one] using RationalInterval.singleton_contains (-1)
  have htwo : (RationalInterval.singleton 2).Contains (2 : ℝ) := by
    norm_num [RationalInterval.Contains, RationalInterval.singleton]
  have hb : intervalB.Contains realB :=
    RationalInterval.add_contains (RationalInterval.singleton_contains lower)
      (RationalInterval.mul_contains hwidth hy)
  have hr :
      (RationalInterval.add
        (RationalInterval.add (box 0) (RationalInterval.neg intervalB))
        (RationalInterval.mul
          (RationalInterval.add
            (RationalInterval.add (RationalInterval.singleton 1)
              (RationalInterval.neg (box 0))) intervalB) X)).Contains
        (input 0 + -realB + (1 + -input 0 + realB) * x) := by
    exact RationalInterval.add_contains
      (RationalInterval.add_contains (hinput 0) (RationalInterval.neg_contains hb))
      (RationalInterval.mul_contains
        (RationalInterval.add_contains
          (RationalInterval.add_contains hone
            (RationalInterval.neg_contains (hinput 0))) hb) hx)
  have ht :
      (RationalInterval.add (RationalInterval.singleton (-1))
        (RationalInterval.mul (RationalInterval.singleton 2) Z)).Contains
        (-1 + 2 * z) :=
    RationalInterval.add_contains hnegativeOne
      (RationalInterval.mul_contains htwo hz)
  dsimp only [intervalB, realB] at hr hb
  simpa only [sub_eq_add_neg, Rat.cast_add, Rat.cast_neg, Rat.cast_one] using ⟨hr, hb, ht⟩

/-- Direct interval evaluation contains the exact reduced formula. -/
theorem weightedSelfDirectIntervalFormula_contains
    (lower upper : ℚ) (box : Fin 18 → RationalInterval) (input : Fin 18 → ℝ)
    (hinput : ∀ i, (box i).Contains (input i))
    {X Y Z : RationalInterval} {x y z : ℝ}
    (hx : X.Contains x) (hy : Y.Contains y) (hz : Z.Contains z) :
    let intervalFormula := weightedSelfDirectIntervalFormula lower upper box X Y Z
    let b : ℝ := lower + (upper - lower) * y
    let chart : WeightedSelfChart ℝ :=
      ⟨input 0 - b + (1 - input 0 + b) * x, b, -1 + 2 * z⟩
    let realFormula := weightedSelfFormula weightedSelfRealFormulaOperations
      input chart.r chart.b chart.t
    intervalFormula.p.Contains realFormula.p ∧ intervalFormula.q.Contains realFormula.q ∧
      intervalFormula.radicand.Contains realFormula.radicand := by
  obtain ⟨hr, hb, ht⟩ := weightedSelfDirectIntervalChart_contains
    lower upper box input hinput hx hy hz
  exact weightedSelfFormula_rel weightedSelfRationalIntervalOperations
    weightedSelfRealFormulaOperations RationalInterval.Contains
    RationalInterval.singleton_contains
    (fun ha hb ↦ RationalInterval.add_contains ha hb)
    (fun ha ↦ RationalInterval.neg_contains ha)
    (fun ha hb ↦ RationalInterval.mul_contains ha hb)
    (fun ha n ↦ RationalInterval.pow_contains ha n)
    hinput hr hb ht

/-- A successful direct interval check proves `Q ≥ 0` on the corresponding real chart. -/
theorem weightedSelfPolynomialQ_nonneg_of_direct_interval_certificate
    (lower upper : ℚ) (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput upper i))
    {X Y Z : RationalInterval}
    (hcertificate : weightedSelfDirectQCertifiesNonnegative lower upper box X Y Z = true)
    {x y z : ℝ} (hx : X.Contains x) (hy : Y.Contains y) (hz : Z.Contains z)
    (hr : (weightedSelfRealChart lower upper x y z).r ≠ 0) :
    0 ≤ weightedSelfPolynomialQ
      (weightedSelfRealChart lower upper x y z).r
      (weightedSelfRealChart lower upper x y z).b
      (weightedSelfRealChart lower upper x y z).t upper := by
  have hlower : 0 ≤
      (weightedSelfDirectIntervalFormula lower upper box X Y Z).q.lower :=
    of_decide_eq_true hcertificate
  have hcontains := (weightedSelfDirectIntervalFormula_contains lower upper box
    (weightedSelfCoefficientInput upper) hinput hx hy hz).2.1
  have hcontains' :
      (weightedSelfDirectIntervalFormula lower upper box X Y Z).q.Contains
        (weightedSelfRealFormula
          (weightedSelfRealChart lower upper x y z).r
          (weightedSelfRealChart lower upper x y z).b
          (weightedSelfRealChart lower upper x y z).t upper).q := by
    simpa only [weightedSelfRealFormula, weightedSelfRealChart,
      weightedSelfCoefficientInput, Matrix.cons_val_zero, Rat.cast_sub, Rat.cast_one]
      using hcontains
  have hrealLower : (0 : ℝ) ≤
      (weightedSelfDirectIntervalFormula lower upper box X Y Z).q.lower := by
    exact_mod_cast hlower
  have hformula : 0 ≤
      (weightedSelfRealFormula
        (weightedSelfRealChart lower upper x y z).r
        (weightedSelfRealChart lower upper x y z).b
        (weightedSelfRealChart lower upper x y z).t upper).q :=
    hrealLower.trans hcontains'.1
  rw [(weightedSelfRealFormula_eq_weightedSelf
    (weightedSelfRealChart lower upper x y z).r
    (weightedSelfRealChart lower upper x y z).b
    (weightedSelfRealChart lower upper x y z).t upper hr).2.1] at hformula
  exact hformula

end Bescovitch
