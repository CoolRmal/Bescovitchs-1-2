/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateCore
public import Bescovitch.SixPoint.WeightedSelfExceptional

/-!
# Polynomial certificates for the exceptional weighted-self box

The exceptional chart is controlled by three exact polynomial signs: the negative radial
derivative, a positive face-Hessian diagonal, and the nonnegative face-Hessian determinant.
This file derives those polynomials formally and proves that these three signs imply the desired
weighted-self discriminant bound. A finite certificate file can therefore remain purely algebraic.
-/

@[expose] public section

noncomputable section

open Filter Set

namespace Bescovitch

namespace RadicalUnivariate

/-- Formal differentiation of a radical-coefficient univariate polynomial. -/
def derivative {n : ℕ} : RadicalUnivariate n → RadicalUnivariate n
  | [] => []
  | _ :: p => RadicalUnivariate.add p (.constant 0 :: derivative p)

private theorem eval_derivative_cons {n : ℕ} (a : RadicalExpression n)
    (p : RadicalUnivariate n) (input : Fin n → ℝ) (x : ℝ) :
    RadicalUnivariate.eval (derivative (a :: p)) input x =
      RadicalUnivariate.eval p input x +
        x * RadicalUnivariate.eval (derivative p) input x := by
  simp [derivative, RadicalUnivariate.eval_add, RadicalUnivariate.eval,
    RadicalExpression.eval]

private theorem hasDerivAt_eval {n : ℕ} (p : RadicalUnivariate n)
    (input : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (RadicalUnivariate.eval p input)
      (RadicalUnivariate.eval (derivative p) input x) x := by
  induction p with
  | nil =>
      simpa [RadicalUnivariate.eval, derivative] using hasDerivAt_const x (0 : ℝ)
  | cons a p hp =>
      convert! (hasDerivAt_const x (a.eval input)).add
        ((hasDerivAt_id x).mul hp) using 1
      simp [eval_derivative_cons]

private theorem hasDerivAt_eval_affine {n : ℕ} (p : RadicalUnivariate n)
    (input : Fin n → ℝ) (t dt s : ℝ) :
    HasDerivAt (fun u ↦ RadicalUnivariate.eval p input (t + u * dt))
      (dt * RadicalUnivariate.eval (derivative p) input (t + s * dt)) s := by
  induction p with
  | nil =>
      simpa [RadicalUnivariate.eval, derivative] using hasDerivAt_const s (0 : ℝ)
  | cons a p hp =>
      have hinner : HasDerivAt (fun u : ℝ ↦ t + u * dt) dt s := by
        convert! (hasDerivAt_const s t).add ((hasDerivAt_id s).mul_const dt) using 1
        ring
      convert! (hasDerivAt_const s (a.eval input)).add (hinner.mul hp) using 1
      rw [eval_derivative_cons]
      ring

end RadicalUnivariate

namespace RadicalBivariate

/-- Formal differentiation in the first bivariate coordinate. -/
def derivativeFirst {n : ℕ} : RadicalBivariate n → RadicalBivariate n
  | [] => []
  | _ :: p => RadicalBivariate.add p ([] :: derivativeFirst p)

/-- Formal differentiation in the second bivariate coordinate. -/
def derivativeSecond {n : ℕ} (p : RadicalBivariate n) : RadicalBivariate n :=
  p.map RadicalUnivariate.derivative

private theorem eval_derivativeFirst_cons {n : ℕ} (a : RadicalUnivariate n)
    (p : RadicalBivariate n) (input : Fin n → ℝ) (x y : ℝ) :
    RadicalBivariate.eval (derivativeFirst (a :: p)) input x y =
      RadicalBivariate.eval p input x y +
        x * RadicalBivariate.eval (derivativeFirst p) input x y := by
  simp [derivativeFirst, RadicalBivariate.eval_add, RadicalBivariate.eval,
    RadicalUnivariate.eval]

private theorem hasDerivAt_eval_first {n : ℕ} (p : RadicalBivariate n)
    (input : Fin n → ℝ) (x y : ℝ) :
    HasDerivAt (fun u ↦ RadicalBivariate.eval p input u y)
      (RadicalBivariate.eval (derivativeFirst p) input x y) x := by
  induction p with
  | nil =>
      simpa [RadicalBivariate.eval, derivativeFirst] using hasDerivAt_const x (0 : ℝ)
  | cons a p hp =>
      convert! (hasDerivAt_const x (RadicalUnivariate.eval a input y)).add
        ((hasDerivAt_id x).mul hp) using 1
      simp [eval_derivativeFirst_cons]

private theorem hasDerivAt_eval_second {n : ℕ} (p : RadicalBivariate n)
    (input : Fin n → ℝ) (x y : ℝ) :
    HasDerivAt (fun u ↦ RadicalBivariate.eval p input x u)
      (RadicalBivariate.eval (derivativeSecond p) input x y) y := by
  induction p with
  | nil =>
      simpa [RadicalBivariate.eval, derivativeSecond] using hasDerivAt_const y (0 : ℝ)
  | cons a p hp =>
      convert! (RadicalUnivariate.hasDerivAt_eval a input y).add
        ((hasDerivAt_const y x).mul hp) using 1
      simp [derivativeSecond, RadicalBivariate.eval]

private theorem hasDerivAt_eval_affine {n : ℕ} (p : RadicalBivariate n)
    (input : Fin n → ℝ) (b t db dt s : ℝ) :
    HasDerivAt
      (fun u ↦ RadicalBivariate.eval p input (b + u * db) (t + u * dt))
      (db * RadicalBivariate.eval (derivativeFirst p) input
          (b + s * db) (t + s * dt) +
        dt * RadicalBivariate.eval (derivativeSecond p) input
          (b + s * db) (t + s * dt)) s := by
  induction p with
  | nil =>
      simpa [RadicalBivariate.eval, derivativeFirst, derivativeSecond] using
        hasDerivAt_const s (0 : ℝ)
  | cons a p hp =>
      have ha := RadicalUnivariate.hasDerivAt_eval_affine a input t dt s
      have hb : HasDerivAt (fun u : ℝ ↦ b + u * db) db s := by
        convert! (hasDerivAt_const s b).add ((hasDerivAt_id s).mul_const db) using 1
        ring
      have h := ha.add (hb.mul hp)
      convert! h using 1
      simp only [eval_derivativeFirst_cons, derivativeSecond,
        RadicalBivariate.eval, List.map_cons]
      ring

end RadicalBivariate

namespace RadicalTrivariate

/-- Formal differentiation in the first trivariate coordinate. -/
def derivativeFirst {n : ℕ} : RadicalTrivariate n → RadicalTrivariate n
  | [] => []
  | _ :: p => RadicalTrivariate.add p ([] :: derivativeFirst p)

/-- Formal differentiation in the second trivariate coordinate. -/
def derivativeSecond {n : ℕ} (p : RadicalTrivariate n) : RadicalTrivariate n :=
  p.map RadicalBivariate.derivativeFirst

/-- Formal differentiation in the third trivariate coordinate. -/
def derivativeThird {n : ℕ} (p : RadicalTrivariate n) : RadicalTrivariate n :=
  p.map RadicalBivariate.derivativeSecond

private theorem eval_derivativeFirst_cons {n : ℕ} (a : RadicalBivariate n)
    (p : RadicalTrivariate n) (input : Fin n → ℝ) (x y z : ℝ) :
    RadicalTrivariate.eval (derivativeFirst (a :: p)) input x y z =
      RadicalTrivariate.eval p input x y z +
        x * RadicalTrivariate.eval (derivativeFirst p) input x y z := by
  simp [derivativeFirst, RadicalTrivariate.eval_add, RadicalTrivariate.eval,
    RadicalBivariate.eval]

private theorem hasDerivAt_eval_first {n : ℕ} (p : RadicalTrivariate n)
    (input : Fin n → ℝ) (x y z : ℝ) :
    HasDerivAt (fun u ↦ RadicalTrivariate.eval p input u y z)
      (RadicalTrivariate.eval (derivativeFirst p) input x y z) x := by
  induction p with
  | nil =>
      simpa [RadicalTrivariate.eval, derivativeFirst] using hasDerivAt_const x (0 : ℝ)
  | cons a p hp =>
      convert! (hasDerivAt_const x (RadicalBivariate.eval a input y z)).add
        ((hasDerivAt_id x).mul hp) using 1
      simp [eval_derivativeFirst_cons]

private theorem hasDerivAt_eval_second {n : ℕ} (p : RadicalTrivariate n)
    (input : Fin n → ℝ) (x y z : ℝ) :
    HasDerivAt (fun u ↦ RadicalTrivariate.eval p input x u z)
      (RadicalTrivariate.eval (derivativeSecond p) input x y z) y := by
  induction p with
  | nil =>
      simpa [RadicalTrivariate.eval, derivativeSecond] using hasDerivAt_const y (0 : ℝ)
  | cons a p hp =>
      convert! (RadicalBivariate.hasDerivAt_eval_first a input y z).add
        ((hasDerivAt_const y x).mul hp) using 1
      simp [derivativeSecond, RadicalTrivariate.eval]

private theorem hasDerivAt_eval_third {n : ℕ} (p : RadicalTrivariate n)
    (input : Fin n → ℝ) (x y z : ℝ) :
    HasDerivAt (fun u ↦ RadicalTrivariate.eval p input x y u)
      (RadicalTrivariate.eval (derivativeThird p) input x y z) z := by
  induction p with
  | nil =>
      simpa [RadicalTrivariate.eval, derivativeThird] using hasDerivAt_const z (0 : ℝ)
  | cons a p hp =>
      convert! (RadicalBivariate.hasDerivAt_eval_second a input y z).add
        ((hasDerivAt_const z x).mul hp) using 1
      simp [derivativeThird, RadicalTrivariate.eval]

private theorem hasDerivAt_eval_faceAffine {n : ℕ} (p : RadicalTrivariate n)
    (input : Fin n → ℝ) (r b t db dt s : ℝ) :
    HasDerivAt
      (fun u ↦ RadicalTrivariate.eval p input r (b + u * db) (t + u * dt))
      (db * RadicalTrivariate.eval (derivativeSecond p) input r
          (b + s * db) (t + s * dt) +
        dt * RadicalTrivariate.eval (derivativeThird p) input r
          (b + s * db) (t + s * dt)) s := by
  induction p with
  | nil =>
      simpa [RadicalTrivariate.eval, derivativeSecond, derivativeThird] using
        hasDerivAt_const s (0 : ℝ)
  | cons a p hp =>
      have ha := RadicalBivariate.hasDerivAt_eval_affine a input b t db dt s
      have h := ha.add ((hasDerivAt_const s r).mul hp)
      convert! h using 1
      simp only [derivativeSecond, derivativeThird,
        RadicalTrivariate.eval, List.map_cons]
      ring

end RadicalTrivariate

namespace IntervalUnivariate

/-- Formal differentiation of an interval-coefficient univariate polynomial. -/
def derivative : IntervalUnivariate → IntervalUnivariate
  | [] => []
  | _ :: p => IntervalUnivariate.add p (.singleton 0 :: derivative p)

private theorem contains_derivative {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalUnivariate} {p : RadicalUnivariate n} (h : P.Contains input p) :
    P.derivative.Contains input p.derivative := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead htail ih =>
      exact IntervalUnivariate.contains_add htail
        (List.Forall₂.cons (RationalInterval.singleton_contains 0) ih)

end IntervalUnivariate

namespace IntervalBivariate

/-- Formal differentiation in the first interval-bivariate coordinate. -/
def derivativeFirst : IntervalBivariate → IntervalBivariate
  | [] => []
  | _ :: p => IntervalBivariate.add p ([] :: derivativeFirst p)

/-- Formal differentiation in the second interval-bivariate coordinate. -/
def derivativeSecond (p : IntervalBivariate) : IntervalBivariate :=
  p.map IntervalUnivariate.derivative

private theorem contains_derivativeFirst {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalBivariate} {p : RadicalBivariate n} (h : P.Contains input p) :
    P.derivativeFirst.Contains input p.derivativeFirst := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead htail ih =>
      exact IntervalBivariate.contains_add htail (List.Forall₂.cons List.Forall₂.nil ih)

private theorem contains_derivativeSecond {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalBivariate} {p : RadicalBivariate n} (h : P.Contains input p) :
    P.derivativeSecond.Contains input p.derivativeSecond := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead htail ih =>
      exact List.Forall₂.cons (IntervalUnivariate.contains_derivative hhead) ih

end IntervalBivariate

namespace IntervalTrivariate

/-- Formal differentiation in the first interval-trivariate coordinate. -/
def derivativeFirst : IntervalTrivariate → IntervalTrivariate
  | [] => []
  | _ :: p => IntervalTrivariate.add p ([] :: derivativeFirst p)

/-- Formal differentiation in the second interval-trivariate coordinate. -/
def derivativeSecond (p : IntervalTrivariate) : IntervalTrivariate :=
  p.map IntervalBivariate.derivativeFirst

/-- Formal differentiation in the third interval-trivariate coordinate. -/
def derivativeThird (p : IntervalTrivariate) : IntervalTrivariate :=
  p.map IntervalBivariate.derivativeSecond

private theorem contains_derivativeFirst {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalTrivariate} {p : RadicalTrivariate n} (h : P.Contains input p) :
    P.derivativeFirst.Contains input p.derivativeFirst := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead htail ih =>
      exact IntervalTrivariate.contains_add htail
        (List.Forall₂.cons List.Forall₂.nil ih)

private theorem contains_derivativeSecond {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalTrivariate} {p : RadicalTrivariate n} (h : P.Contains input p) :
    P.derivativeSecond.Contains input p.derivativeSecond := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead htail ih =>
      exact List.Forall₂.cons (IntervalBivariate.contains_derivativeFirst hhead) ih

private theorem contains_derivativeThird {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalTrivariate} {p : RadicalTrivariate n} (h : P.Contains input p) :
    P.derivativeThird.Contains input p.derivativeThird := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead htail ih =>
      exact List.Forall₂.cons (IntervalBivariate.contains_derivativeSecond hhead) ih

end IntervalTrivariate

/-- Radical-polynomial operations used to evaluate the reduced formula exactly. -/
def radicalPolynomialOperations :
    WeightedSelfFormulaOperations (RadicalTrivariate 18) :=
  ⟨fun q ↦ .constant (.constant q), RadicalTrivariate.add,
    RadicalTrivariate.neg, RadicalTrivariate.mul, RadicalTrivariate.pow⟩

/-- The exact radical-coefficient polynomial for the exceptional discriminant. -/
def weightedSelfExceptionalDiscriminantPolynomial : RadicalTrivariate 18 :=
  let formula := weightedSelfFormula radicalPolynomialOperations
    (fun i ↦ .constant (.var i)) .first .second .third
  RadicalTrivariate.add (RadicalTrivariate.mul formula.p formula.p)
    (RadicalTrivariate.neg
      (RadicalTrivariate.mul
        (RadicalTrivariate.mul formula.q formula.q) formula.radicand))

private abbrev exceptionalInput : Fin 18 → ℝ := weightedSelfCoefficientInput (4 / 5)

private theorem weightedSelfExceptionalDiscriminantPolynomial_eval
    (r b t : ℝ) (hr : r ≠ 0) :
    weightedSelfExceptionalDiscriminantPolynomial.eval exceptionalInput r b t =
      weightedSelfDiscriminant r b t (4 / 5) := by
  let formula := weightedSelfFormula radicalPolynomialOperations
    (fun i ↦ RadicalTrivariate.constant (.var i))
    RadicalTrivariate.first RadicalTrivariate.second RadicalTrivariate.third
  have hmap := weightedSelfFormula_map radicalPolynomialOperations
    weightedSelfRealFormulaOperations
    (fun p ↦ RadicalTrivariate.eval p exceptionalInput r b t)
    (fun q ↦ by
      simp [radicalPolynomialOperations, RadicalExpression.eval,
        weightedSelfRealFormulaOperations])
    (fun p q ↦ RadicalTrivariate.eval_add p q exceptionalInput r b t)
    (fun p ↦ RadicalTrivariate.eval_neg p exceptionalInput r b t)
    (fun p q ↦ RadicalTrivariate.eval_mul p q exceptionalInput r b t)
    (fun p n ↦ RadicalTrivariate.eval_pow p n exceptionalInput r b t)
    (fun i ↦ RadicalTrivariate.constant (.var i))
    RadicalTrivariate.first RadicalTrivariate.second RadicalTrivariate.third
  have hformula := weightedSelfRealFormula_eq_weightedSelf r b t (4 / 5) hr
  have hatom :
      (fun p ↦ RadicalTrivariate.eval p exceptionalInput r b t) ∘
          (fun i ↦ RadicalTrivariate.constant (.var i)) = exceptionalInput := by
    funext i
    simp [exceptionalInput, RadicalExpression.eval]
  simp only [RadicalTrivariate.eval_first, RadicalTrivariate.eval_second,
    RadicalTrivariate.eval_third] at hmap
  rw [hatom] at hmap
  change formula.p.eval exceptionalInput r b t =
      (weightedSelfRealFormula r b t (4 / 5)).p ∧
    formula.q.eval exceptionalInput r b t =
      (weightedSelfRealFormula r b t (4 / 5)).q ∧
    formula.radicand.eval exceptionalInput r b t =
      (weightedSelfRealFormula r b t (4 / 5)).radicand at hmap
  simp only [weightedSelfExceptionalDiscriminantPolynomial,
    RadicalTrivariate.eval_add, RadicalTrivariate.eval_neg,
    RadicalTrivariate.eval_mul]
  change formula.p.eval exceptionalInput r b t *
        formula.p.eval exceptionalInput r b t +
      -(formula.q.eval exceptionalInput r b t *
          formula.q.eval exceptionalInput r b t *
        formula.radicand.eval exceptionalInput r b t) = _
  rw [hmap.1, hmap.2.1, hmap.2.2, hformula.1, hformula.2.1, hformula.2.2]
  simp only [weightedSelfDiscriminant]
  ring

/-- The formal radial derivative of the exceptional discriminant. -/
def weightedSelfExceptionalRadialPolynomial : RadicalTrivariate 18 :=
  RadicalTrivariate.derivativeFirst weightedSelfExceptionalDiscriminantPolynomial

/-- The formal first face derivative in the radius coordinate. -/
def weightedSelfExceptionalFaceBPolynomial : RadicalTrivariate 18 :=
  RadicalTrivariate.derivativeSecond weightedSelfExceptionalDiscriminantPolynomial

/-- The formal first face derivative in the projection coordinate. -/
def weightedSelfExceptionalFaceTPolynomial : RadicalTrivariate 18 :=
  RadicalTrivariate.derivativeThird weightedSelfExceptionalDiscriminantPolynomial

/-- The negative radial derivative polynomial used by the exceptional certificate. -/
def weightedSelfExceptionalNegativeRadialPolynomial : RadicalTrivariate 18 :=
  RadicalTrivariate.neg weightedSelfExceptionalRadialPolynomial

/-- The second face derivative in the radius coordinate. -/
def weightedSelfExceptionalFaceBBPolynomial : RadicalTrivariate 18 :=
  RadicalTrivariate.derivativeSecond weightedSelfExceptionalFaceBPolynomial

/-- The mixed second face derivative. -/
def weightedSelfExceptionalFaceBTPolynomial : RadicalTrivariate 18 :=
  let bt := RadicalTrivariate.derivativeThird weightedSelfExceptionalFaceBPolynomial
  let tb := RadicalTrivariate.derivativeSecond weightedSelfExceptionalFaceTPolynomial
  RadicalTrivariate.mul
    (RadicalTrivariate.constant (.constant (1 / 2)))
    (RadicalTrivariate.add bt tb)

/-- The second face derivative in the projection coordinate. -/
def weightedSelfExceptionalFaceTTPolynomial : RadicalTrivariate 18 :=
  RadicalTrivariate.derivativeThird weightedSelfExceptionalFaceTPolynomial

/-- The determinant of the formal face Hessian. -/
def weightedSelfExceptionalFaceDeterminantPolynomial : RadicalTrivariate 18 :=
  RadicalTrivariate.add
    (RadicalTrivariate.mul weightedSelfExceptionalFaceBBPolynomial
      weightedSelfExceptionalFaceTTPolynomial)
    (RadicalTrivariate.neg
      (RadicalTrivariate.pow weightedSelfExceptionalFaceBTPolynomial 2))

/-- The interval-coefficient exceptional discriminant in physical coordinates. -/
def weightedSelfExceptionalIntervalDiscriminantPolynomial
    (box : Fin 18 → RationalInterval) : IntervalTrivariate :=
  let formula := weightedSelfFormula intervalPolynomialOperations
    (fun i ↦ .constant (box i)) .first .second .third
  IntervalTrivariate.add (IntervalTrivariate.mul formula.p formula.p)
    (IntervalTrivariate.neg
      (IntervalTrivariate.mul
        (IntervalTrivariate.mul formula.q formula.q) formula.radicand))

/-- The interval enclosure of the negative exceptional radial derivative. -/
def weightedSelfExceptionalNegativeRadialIntervalPolynomial
    (box : Fin 18 → RationalInterval) : IntervalTrivariate :=
  IntervalTrivariate.neg
    (weightedSelfExceptionalIntervalDiscriminantPolynomial box).derivativeFirst

/-- The interval enclosure of the exceptional face `bb` derivative. -/
def weightedSelfExceptionalFaceBBIntervalPolynomial
    (box : Fin 18 → RationalInterval) : IntervalTrivariate :=
  IntervalTrivariate.derivativeSecond
    (IntervalTrivariate.derivativeSecond
      (weightedSelfExceptionalIntervalDiscriminantPolynomial box))

/-- The interval enclosure of the symmetrized exceptional face mixed derivative. -/
def weightedSelfExceptionalFaceBTIntervalPolynomial
    (box : Fin 18 → RationalInterval) : IntervalTrivariate :=
  let firstB :=
    (weightedSelfExceptionalIntervalDiscriminantPolynomial box).derivativeSecond
  let firstT :=
    (weightedSelfExceptionalIntervalDiscriminantPolynomial box).derivativeThird
  let bt := firstB.derivativeThird
  let tb := firstT.derivativeSecond
  IntervalTrivariate.mul
    (IntervalTrivariate.constant (.singleton (1 / 2)))
    (IntervalTrivariate.add bt tb)

/-- The interval enclosure of the exceptional face `tt` derivative. -/
def weightedSelfExceptionalFaceTTIntervalPolynomial
    (box : Fin 18 → RationalInterval) : IntervalTrivariate :=
  IntervalTrivariate.derivativeThird
    (IntervalTrivariate.derivativeThird
      (weightedSelfExceptionalIntervalDiscriminantPolynomial box))

/-- The interval enclosure of the exceptional face-Hessian determinant. -/
def weightedSelfExceptionalFaceDeterminantIntervalPolynomial
    (box : Fin 18 → RationalInterval) : IntervalTrivariate :=
  IntervalTrivariate.add
    (IntervalTrivariate.mul
      (weightedSelfExceptionalFaceBBIntervalPolynomial box)
      (weightedSelfExceptionalFaceTTIntervalPolynomial box))
    (IntervalTrivariate.neg
      (IntervalTrivariate.pow
        (weightedSelfExceptionalFaceBTIntervalPolynomial box) 2))

/-- The face `bb` derivative minus a fixed positive rational margin. -/
def weightedSelfExceptionalFaceBBMarginPolynomial : RadicalTrivariate 18 :=
  RadicalTrivariate.add weightedSelfExceptionalFaceBBPolynomial
    (RadicalTrivariate.constant (.constant (-1 / 10000)))

/-- The interval enclosure of the face `bb` derivative with its positive margin removed. -/
def weightedSelfExceptionalFaceBBMarginIntervalPolynomial
    (box : Fin 18 → RationalInterval) : IntervalTrivariate :=
  IntervalTrivariate.add (weightedSelfExceptionalFaceBBIntervalPolynomial box)
    (IntervalTrivariate.constant (.singleton (-1 / 10000)))

private theorem weightedSelfExceptionalIntervalDiscriminant_contains
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (exceptionalInput i)) :
    (weightedSelfExceptionalIntervalDiscriminantPolynomial box).Contains
      exceptionalInput weightedSelfExceptionalDiscriminantPolynomial := by
  let intervalFormula := weightedSelfFormula intervalPolynomialOperations
    (fun i ↦ IntervalTrivariate.constant (box i))
    IntervalTrivariate.first IntervalTrivariate.second IntervalTrivariate.third
  let exactFormula := weightedSelfFormula radicalPolynomialOperations
    (fun i ↦ RadicalTrivariate.constant (.var i))
    RadicalTrivariate.first RadicalTrivariate.second RadicalTrivariate.third
  have hformula :
      intervalFormula.p.Contains exceptionalInput exactFormula.p ∧
        intervalFormula.q.Contains exceptionalInput exactFormula.q ∧
        intervalFormula.radicand.Contains exceptionalInput exactFormula.radicand := by
    apply weightedSelfFormula_rel intervalPolynomialOperations
      radicalPolynomialOperations (IntervalTrivariate.Contains exceptionalInput)
      (fun q ↦ IntervalTrivariate.contains_constant
        (RationalInterval.singleton_contains q))
      (fun ha hb ↦ IntervalTrivariate.contains_add ha hb)
      (fun ha ↦ IntervalTrivariate.contains_neg ha)
      (fun ha hb ↦ IntervalTrivariate.contains_mul ha hb)
      (fun ha n ↦ IntervalTrivariate.contains_pow ha n)
      (atom := fun i ↦ IntervalTrivariate.constant (box i))
      (atom' := fun i ↦ RadicalTrivariate.constant (.var i))
      (r := IntervalTrivariate.first) (r' := RadicalTrivariate.first)
      (b := IntervalTrivariate.second) (b' := RadicalTrivariate.second)
      (t := IntervalTrivariate.third) (t' := RadicalTrivariate.third)
    · intro i
      apply IntervalTrivariate.contains_constant
      simpa only [RadicalExpression.eval] using hinput i
    · exact IntervalTrivariate.contains_first exceptionalInput
    · exact IntervalTrivariate.contains_second exceptionalInput
    · exact IntervalTrivariate.contains_third exceptionalInput
  change (IntervalTrivariate.add (IntervalTrivariate.mul intervalFormula.p intervalFormula.p)
      (IntervalTrivariate.neg
        (IntervalTrivariate.mul (IntervalTrivariate.mul intervalFormula.q intervalFormula.q)
          intervalFormula.radicand))).Contains exceptionalInput
    (RadicalTrivariate.add (RadicalTrivariate.mul exactFormula.p exactFormula.p)
      (RadicalTrivariate.neg
        (RadicalTrivariate.mul (RadicalTrivariate.mul exactFormula.q exactFormula.q)
          exactFormula.radicand)))
  exact IntervalTrivariate.contains_add
    (IntervalTrivariate.contains_mul hformula.1 hformula.1)
    (IntervalTrivariate.contains_neg
      (IntervalTrivariate.contains_mul
        (IntervalTrivariate.contains_mul hformula.2.1 hformula.2.1) hformula.2.2))

/-- The exceptional radial interval polynomial encloses the exact negative derivative. -/
theorem weightedSelfExceptionalNegativeRadialInterval_contains
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput (4 / 5) i)) :
    (weightedSelfExceptionalNegativeRadialIntervalPolynomial box).Contains
      (weightedSelfCoefficientInput (4 / 5))
      weightedSelfExceptionalNegativeRadialPolynomial := by
  simpa only [weightedSelfExceptionalNegativeRadialIntervalPolynomial,
    weightedSelfExceptionalNegativeRadialPolynomial,
    weightedSelfExceptionalRadialPolynomial] using
    IntervalTrivariate.contains_neg
      (IntervalTrivariate.contains_derivativeFirst
        (weightedSelfExceptionalIntervalDiscriminant_contains box hinput))

private theorem weightedSelfExceptionalFaceBBInterval_contains
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (exceptionalInput i)) :
    (weightedSelfExceptionalFaceBBIntervalPolynomial box).Contains
      exceptionalInput weightedSelfExceptionalFaceBBPolynomial := by
  simpa only [weightedSelfExceptionalFaceBBIntervalPolynomial,
    weightedSelfExceptionalFaceBBPolynomial,
    weightedSelfExceptionalFaceBPolynomial] using
    IntervalTrivariate.contains_derivativeSecond
      (IntervalTrivariate.contains_derivativeSecond
        (weightedSelfExceptionalIntervalDiscriminant_contains box hinput))

private theorem weightedSelfExceptionalFaceBTInterval_contains
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (exceptionalInput i)) :
    (weightedSelfExceptionalFaceBTIntervalPolynomial box).Contains
      exceptionalInput weightedSelfExceptionalFaceBTPolynomial := by
  have hbase := weightedSelfExceptionalIntervalDiscriminant_contains box hinput
  simpa only [weightedSelfExceptionalFaceBTIntervalPolynomial,
    weightedSelfExceptionalFaceBTPolynomial,
    weightedSelfExceptionalFaceBPolynomial,
    weightedSelfExceptionalFaceTPolynomial] using
    IntervalTrivariate.contains_mul
      (IntervalTrivariate.contains_constant (RationalInterval.singleton_contains (1 / 2)))
      (IntervalTrivariate.contains_add
        (IntervalTrivariate.contains_derivativeThird
          (IntervalTrivariate.contains_derivativeSecond hbase))
        (IntervalTrivariate.contains_derivativeSecond
          (IntervalTrivariate.contains_derivativeThird hbase)))

private theorem weightedSelfExceptionalFaceTTInterval_contains
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (exceptionalInput i)) :
    (weightedSelfExceptionalFaceTTIntervalPolynomial box).Contains
      exceptionalInput weightedSelfExceptionalFaceTTPolynomial := by
  simpa only [weightedSelfExceptionalFaceTTIntervalPolynomial,
    weightedSelfExceptionalFaceTTPolynomial,
    weightedSelfExceptionalFaceTPolynomial] using
    IntervalTrivariate.contains_derivativeThird
      (IntervalTrivariate.contains_derivativeThird
        (weightedSelfExceptionalIntervalDiscriminant_contains box hinput))

private theorem weightedSelfExceptionalFaceDeterminantInterval_contains
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (exceptionalInput i)) :
    (weightedSelfExceptionalFaceDeterminantIntervalPolynomial box).Contains
      exceptionalInput weightedSelfExceptionalFaceDeterminantPolynomial := by
  simpa only [weightedSelfExceptionalFaceDeterminantIntervalPolynomial,
    weightedSelfExceptionalFaceDeterminantPolynomial] using
    IntervalTrivariate.contains_add
      (IntervalTrivariate.contains_mul
        (weightedSelfExceptionalFaceBBInterval_contains box hinput)
        (weightedSelfExceptionalFaceTTInterval_contains box hinput))
      (IntervalTrivariate.contains_neg
        (IntervalTrivariate.contains_pow
          (weightedSelfExceptionalFaceBTInterval_contains box hinput) 2))

private theorem weightedSelfExceptionalFaceBBMarginInterval_contains
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (exceptionalInput i)) :
    (weightedSelfExceptionalFaceBBMarginIntervalPolynomial box).Contains
      exceptionalInput weightedSelfExceptionalFaceBBMarginPolynomial := by
  simpa only [weightedSelfExceptionalFaceBBMarginIntervalPolynomial,
    weightedSelfExceptionalFaceBBMarginPolynomial] using
    IntervalTrivariate.contains_add
      (weightedSelfExceptionalFaceBBInterval_contains box hinput)
      (IntervalTrivariate.contains_constant
        (RationalInterval.singleton_contains (-1 / 10000)))

private def faceB (b t : ℝ) : ℝ :=
  weightedSelfExceptionalFaceBPolynomial.eval exceptionalInput 1 b t

private def faceT (b t : ℝ) : ℝ :=
  weightedSelfExceptionalFaceTPolynomial.eval exceptionalInput 1 b t

private def faceBB (b t : ℝ) : ℝ :=
  weightedSelfExceptionalFaceBBPolynomial.eval exceptionalInput 1 b t

private def faceBT (b t : ℝ) : ℝ :=
  weightedSelfExceptionalFaceBTPolynomial.eval exceptionalInput 1 b t

private def faceTT (b t : ℝ) : ℝ :=
  weightedSelfExceptionalFaceTTPolynomial.eval exceptionalInput 1 b t

private theorem weightedSelfExceptional_hasDerivAt_radial
    {r b t : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun u ↦ weightedSelfDiscriminant u b t (4 / 5))
      (weightedSelfExceptionalRadialPolynomial.eval exceptionalInput r b t) r := by
  have hpolynomial : HasDerivAt
      (fun u ↦ weightedSelfExceptionalDiscriminantPolynomial.eval
        exceptionalInput u b t)
      (weightedSelfExceptionalRadialPolynomial.eval exceptionalInput r b t) r := by
    simpa only [weightedSelfExceptionalRadialPolynomial] using
      RadicalTrivariate.hasDerivAt_eval_first
        weightedSelfExceptionalDiscriminantPolynomial exceptionalInput r b t
  apply hpolynomial.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hr] with u hu
  exact (weightedSelfExceptionalDiscriminantPolynomial_eval u b t hu).symm

private theorem weightedSelfExceptionalFace_hasDerivAt_b (b t : ℝ) :
    HasDerivAt (fun u ↦ weightedSelfExceptionalFace u t) (faceB b t) b := by
  have hpolynomial : HasDerivAt
      (fun u ↦ weightedSelfExceptionalDiscriminantPolynomial.eval
        exceptionalInput 1 u t)
      (weightedSelfExceptionalFaceBPolynomial.eval exceptionalInput 1 b t) b := by
    simpa only [weightedSelfExceptionalFaceBPolynomial] using
      RadicalTrivariate.hasDerivAt_eval_second
        weightedSelfExceptionalDiscriminantPolynomial exceptionalInput 1 b t
  apply hpolynomial.congr_of_eventuallyEq
  filter_upwards with u
  simpa only [weightedSelfExceptionalFace] using
    (weightedSelfExceptionalDiscriminantPolynomial_eval 1 u t one_ne_zero).symm

private theorem weightedSelfExceptionalFace_hasDerivAt_t (b t : ℝ) :
    HasDerivAt (fun u ↦ weightedSelfExceptionalFace b u) (faceT b t) t := by
  have hpolynomial : HasDerivAt
      (fun u ↦ weightedSelfExceptionalDiscriminantPolynomial.eval
        exceptionalInput 1 b u)
      (weightedSelfExceptionalFaceTPolynomial.eval exceptionalInput 1 b t) t := by
    simpa only [weightedSelfExceptionalFaceTPolynomial] using
      RadicalTrivariate.hasDerivAt_eval_third
        weightedSelfExceptionalDiscriminantPolynomial exceptionalInput 1 b t
  apply hpolynomial.congr_of_eventuallyEq
  filter_upwards with u
  simpa only [weightedSelfExceptionalFace] using
    (weightedSelfExceptionalDiscriminantPolynomial_eval 1 b u one_ne_zero).symm

private theorem weightedSelfExceptionalFace_hasDerivAt_affine
    (b t db dt s : ℝ) :
    HasDerivAt
      (fun u ↦ weightedSelfExceptionalFace (b + u * db) (t + u * dt))
      (db * faceB (b + s * db) (t + s * dt) +
        dt * faceT (b + s * db) (t + s * dt)) s := by
  have hpolynomial := RadicalTrivariate.hasDerivAt_eval_faceAffine
    weightedSelfExceptionalDiscriminantPolynomial exceptionalInput 1 b t db dt s
  apply hpolynomial.congr_of_eventuallyEq
  filter_upwards with u
  simpa only [weightedSelfExceptionalFace] using
    (weightedSelfExceptionalDiscriminantPolynomial_eval
      1 (b + u * db) (t + u * dt) one_ne_zero).symm

private theorem weightedSelfExceptionalSlope_hasDerivAt_affine
    (b t db dt s : ℝ) :
    HasDerivAt
      (fun u ↦ db * faceB (b + u * db) (t + u * dt) +
        dt * faceT (b + u * db) (t + u * dt))
      (db ^ 2 * faceBB (b + s * db) (t + s * dt) +
        2 * db * dt * faceBT (b + s * db) (t + s * dt) +
        dt ^ 2 * faceTT (b + s * db) (t + s * dt)) s := by
  have hb := RadicalTrivariate.hasDerivAt_eval_faceAffine
    weightedSelfExceptionalFaceBPolynomial exceptionalInput 1 b t db dt s
  have ht := RadicalTrivariate.hasDerivAt_eval_faceAffine
    weightedSelfExceptionalFaceTPolynomial exceptionalInput 1 b t db dt s
  have h := ((hasDerivAt_const s db).mul hb).add ((hasDerivAt_const s dt).mul ht)
  convert! h using 1
  simp only [faceBB, faceBT, faceTT,
    weightedSelfExceptionalFaceBBPolynomial,
    weightedSelfExceptionalFaceBTPolynomial,
    weightedSelfExceptionalFaceTTPolynomial,
    RadicalTrivariate.eval_add, RadicalTrivariate.eval_mul,
    RadicalTrivariate.eval_constant, RadicalExpression.eval]
  ring

/-- The three formal polynomial signs imply the weighted-self bound on the exceptional box. -/
theorem weightedSelfDiscriminant_nonneg_on_exceptionalBox_of_polynomial_signs
    (hradial : ∀ r b t,
      weightedSelfExceptionalRadialLower b ≤ r → r ≤ 1 →
      (29 : ℝ) / 40 ≤ b → b ≤ 3 / 4 →
      (-209 : ℝ) / 256 ≤ t → t ≤ -13 / 16 →
      0 ≤ weightedSelfExceptionalNegativeRadialPolynomial.eval
        (weightedSelfCoefficientInput (4 / 5)) r b t)
    (hfaceBB : ∀ b t,
      (29 : ℝ) / 40 ≤ b → b ≤ 3 / 4 →
      (-209 : ℝ) / 256 ≤ t → t ≤ -13 / 16 →
      0 < weightedSelfExceptionalFaceBBPolynomial.eval
        (weightedSelfCoefficientInput (4 / 5)) 1 b t)
    (hfaceDeterminant : ∀ b t,
      (29 : ℝ) / 40 ≤ b → b ≤ 3 / 4 →
      (-209 : ℝ) / 256 ≤ t → t ≤ -13 / 16 →
      0 ≤ weightedSelfExceptionalFaceDeterminantPolynomial.eval
        (weightedSelfCoefficientInput (4 / 5)) 1 b t)
    {r b t : ℝ}
    (hrLower : weightedSelfExceptionalRadialLower b ≤ r) (hrUpper : r ≤ 1)
    (hbLower : (29 : ℝ) / 40 ≤ b) (hbUpper : b ≤ 3 / 4)
    (htLower : (-209 : ℝ) / 256 ≤ t) (htUpper : t ≤ -13 / 16) :
    0 ≤ weightedSelfDiscriminant r b t (4 / 5) := by
  apply weightedSelfDiscriminant_nonneg_on_exceptionalBox_of_certificates
    faceB faceT faceBB faceBT faceTT
  · intro r' b' t' hr'Lower hr'Upper hb'Lower hb'Upper ht'Lower ht'Upper
    have hr'Positive : 0 < r' := by
      have hlowerPositive : 0 < weightedSelfExceptionalRadialLower b' := by
        rw [weightedSelfExceptionalRadialLower]
        norm_num at hb'Upper ⊢
        nlinarith [one_lt_cStar_and_cStar_lt_two.1]
      exact hlowerPositive.trans_le hr'Lower
    have hderiv :
        deriv (fun u ↦ weightedSelfDiscriminant u b' t' (4 / 5)) r' =
          weightedSelfExceptionalRadialPolynomial.eval exceptionalInput r' b' t' :=
      (weightedSelfExceptional_hasDerivAt_radial
        (b := b') (t := t') hr'Positive.ne').deriv
    rw [hderiv]
    have hnonneg := hradial r' b' t' hr'Lower hr'Upper
      hb'Lower hb'Upper ht'Lower ht'Upper
    apply neg_nonneg.mp
    simpa only [weightedSelfExceptionalNegativeRadialPolynomial,
      RadicalTrivariate.eval_neg, exceptionalInput] using hnonneg
  · intro b' t' hb'Lower hb'Upper ht'Lower ht'Upper
    exact hfaceBB b' t' hb'Lower hb'Upper ht'Lower ht'Upper
  · intro b' t' hb'Lower hb'Upper ht'Lower ht'Upper
    have hdet := hfaceDeterminant b' t' hb'Lower hb'Upper ht'Lower ht'Upper
    simpa only [weightedSelfExceptionalFaceDeterminantPolynomial,
      RadicalTrivariate.eval_add, RadicalTrivariate.eval_mul,
      RadicalTrivariate.eval_neg, RadicalTrivariate.eval_pow,
      faceBB, faceBT, faceTT, exceptionalInput, sub_eq_add_neg] using hdet
  · exact hrLower
  · exact hrUpper
  · exact hbLower
  · exact hbUpper
  · exact htLower
  · exact htUpper
  · exact weightedSelfExceptionalFace_hasDerivAt_b _ _
  · exact weightedSelfExceptionalFace_hasDerivAt_t _ _
  · intro s _
    exact weightedSelfExceptionalFace_hasDerivAt_affine _ _ _ _ s
  · intro s _
    exact weightedSelfExceptionalSlope_hasDerivAt_affine _ _ _ _ s

/-- The rational radius interval containing the unresolved radial sliver. -/
def weightedSelfExceptionalRadiusInterval : RationalInterval :=
  ⟨8191 / 8192, 1, by norm_num⟩

/-- The rational second-radius interval of the exceptional box. -/
def weightedSelfExceptionalSecondRadiusInterval : RationalInterval :=
  ⟨29 / 40, 3 / 4, by norm_num⟩

/-- The rational projection interval of the exceptional box. -/
def weightedSelfExceptionalProjectionInterval : RationalInterval :=
  ⟨-209 / 256, -13 / 16, by norm_num⟩

set_option maxHeartbeats 5000000 in
/-- Three executable interval-Horner checks prove the exceptional weighted-self bound. -/
theorem weightedSelfDiscriminant_nonneg_on_exceptionalBox_of_interval_certificates
    (kappaDBox kappaCBox : RationalInterval)
    (hD : (weightedSelfCoefficientExpression (4 / 5) 10).certifiesWithin
      weightedSelfEndpointBox kappaDBox = true)
    (hC : (weightedSelfCoefficientExpression (4 / 5) 14).certifiesWithin
      weightedSelfEndpointBox kappaCBox = true)
    (radialTree faceBBTree determinantTree : TensorSubdivision)
    (hradialCertificate : intervalPolynomialSubdivisionCertifiesNonnegative radialTree
      (weightedSelfExceptionalNegativeRadialIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      weightedSelfExceptionalRadiusInterval
      weightedSelfExceptionalSecondRadiusInterval
      weightedSelfExceptionalProjectionInterval = true)
    (hfaceBBCertificate : intervalPolynomialSubdivisionCertifiesNonnegative faceBBTree
      (weightedSelfExceptionalFaceBBMarginIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (.singleton 1) weightedSelfExceptionalSecondRadiusInterval
      weightedSelfExceptionalProjectionInterval = true)
    (hdeterminantCertificate : intervalPolynomialSubdivisionCertifiesNonnegative
      determinantTree
      (weightedSelfExceptionalFaceDeterminantIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (.singleton 1) weightedSelfExceptionalSecondRadiusInterval
      weightedSelfExceptionalProjectionInterval = true)
    {r b t : ℝ}
    (hrLower : weightedSelfExceptionalRadialLower b ≤ r) (hrUpper : r ≤ 1)
    (hbLower : (29 : ℝ) / 40 ≤ b) (hbUpper : b ≤ 3 / 4)
    (htLower : (-209 : ℝ) / 256 ≤ t) (htUpper : t ≤ -13 / 16) :
    0 ≤ weightedSelfDiscriminant r b t (4 / 5) := by
  have hinput : ∀ i,
      (weightedSelfCoefficientBox kappaDBox kappaCBox i).Contains
        (exceptionalInput i) := by
    intro i
    convert weightedSelfCoefficientInput_mem
      ((4 : ℚ) / 5) kappaDBox kappaCBox hD hC i using 1
    norm_num [exceptionalInput]
  apply weightedSelfDiscriminant_nonneg_on_exceptionalBox_of_polynomial_signs
  · intro r' b' t' hr'Lower hr'Upper hb'Lower hb'Upper ht'Lower ht'Upper
    apply RadicalTrivariate.nonneg_of_interval_box_certificate
      weightedSelfExceptionalNegativeRadialPolynomial
      (weightedSelfExceptionalNegativeRadialIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      exceptionalInput
      (weightedSelfExceptionalNegativeRadialInterval_contains
        (weightedSelfCoefficientBox kappaDBox kappaCBox) hinput)
      radialTree hradialCertificate
    · have hrMem : (8191 : ℝ) / 8192 ≤ r' ∧ r' ≤ 1 := by
        constructor
        · rw [weightedSelfExceptionalRadialLower] at hr'Lower
          norm_num at hb'Upper hr'Lower ⊢
          nlinarith [one_lt_cStar_and_cStar_lt_two.1]
        · exact hr'Upper
      simpa [weightedSelfExceptionalRadiusInterval, RationalInterval.Contains] using hrMem
    · have hbMem : (29 : ℝ) / 40 ≤ b' ∧ b' ≤ 3 / 4 :=
        ⟨hb'Lower, hb'Upper⟩
      simpa [weightedSelfExceptionalSecondRadiusInterval,
        RationalInterval.Contains] using hbMem
    · have htMem : (-209 : ℝ) / 256 ≤ t' ∧ t' ≤ -13 / 16 :=
        ⟨ht'Lower, ht'Upper⟩
      simpa [weightedSelfExceptionalProjectionInterval,
        RationalInterval.Contains] using htMem
  · intro b' t' hb'Lower hb'Upper ht'Lower ht'Upper
    have hOne : (RationalInterval.singleton 1).Contains (1 : ℝ) := by
      norm_num [RationalInterval.singleton, RationalInterval.Contains]
    have hbMem : weightedSelfExceptionalSecondRadiusInterval.Contains b' := by
      simpa [weightedSelfExceptionalSecondRadiusInterval,
        RationalInterval.Contains] using (And.intro hb'Lower hb'Upper)
    have htMem : weightedSelfExceptionalProjectionInterval.Contains t' := by
      simpa [weightedSelfExceptionalProjectionInterval,
        RationalInterval.Contains] using (And.intro ht'Lower ht'Upper)
    have hmargin := RadicalTrivariate.nonneg_of_interval_box_certificate
      weightedSelfExceptionalFaceBBMarginPolynomial
      (weightedSelfExceptionalFaceBBMarginIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      exceptionalInput
      (weightedSelfExceptionalFaceBBMarginInterval_contains
        (weightedSelfCoefficientBox kappaDBox kappaCBox) hinput)
      faceBBTree hfaceBBCertificate
      hOne hbMem htMem
    simp only [weightedSelfExceptionalFaceBBMarginPolynomial,
      RadicalTrivariate.eval_add, RadicalTrivariate.eval_constant,
      RadicalExpression.eval] at hmargin
    norm_num at hmargin ⊢
    linarith
  · intro b' t' hb'Lower hb'Upper ht'Lower ht'Upper
    have hOne : (RationalInterval.singleton 1).Contains (1 : ℝ) := by
      norm_num [RationalInterval.singleton, RationalInterval.Contains]
    have hbMem : weightedSelfExceptionalSecondRadiusInterval.Contains b' := by
      simpa [weightedSelfExceptionalSecondRadiusInterval,
        RationalInterval.Contains] using (And.intro hb'Lower hb'Upper)
    have htMem : weightedSelfExceptionalProjectionInterval.Contains t' := by
      simpa [weightedSelfExceptionalProjectionInterval,
        RationalInterval.Contains] using (And.intro ht'Lower ht'Upper)
    exact RadicalTrivariate.nonneg_of_interval_box_certificate
      weightedSelfExceptionalFaceDeterminantPolynomial
      (weightedSelfExceptionalFaceDeterminantIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      exceptionalInput
      (weightedSelfExceptionalFaceDeterminantInterval_contains
        (weightedSelfCoefficientBox kappaDBox kappaCBox) hinput)
      determinantTree hdeterminantCertificate
      hOne hbMem htMem
  · exact hrLower
  · exact hrUpper
  · exact hbLower
  · exact hbUpper
  · exact htLower
  · exact htUpper

end Bescovitch
