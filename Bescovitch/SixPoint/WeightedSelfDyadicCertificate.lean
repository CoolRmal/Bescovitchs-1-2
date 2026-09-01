/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.DyadicIntervalBernstein
public import Bescovitch.SixPoint.WeightedSelfCertificateCore

/-!
# Direct dyadic certificates for the weighted self estimate

The fixed weighted-self formula is evaluated with outward-rounded dyadic intervals.  A successful
direct Bernstein check is then transferred to the exact rational interval certificate used by the
analytic proof.
-/

@[expose] public section

namespace Bescovitch

variable {precision : ℕ}

/-- Fixed-precision dyadic operations on trivariate interval polynomials. -/
def dyadicSelfPolynomialOperations (precision : ℕ) :
    WeightedSelfFormulaOperations (DyadicIntervalTrivariate precision) :=
  ⟨fun q ↦ .constant (.ofRat precision q),
    DyadicIntervalTrivariate.add, DyadicIntervalTrivariate.neg,
    DyadicIntervalTrivariate.mul, DyadicIntervalTrivariate.pow⟩

/-- The affine unit-cube chart evaluated by fixed-precision dyadic arithmetic. -/
def dyadicWeightedSelfChart (precision : ℕ) (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) :
    WeightedSelfChart (DyadicIntervalTrivariate precision) :=
  let coefficient i := DyadicIntervalTrivariate.constant
    (DyadicInterval.ofInterval precision (box i))
  let rational q := DyadicIntervalTrivariate.constant (DyadicInterval.ofRat precision q)
  let sub p q := DyadicIntervalTrivariate.add p (DyadicIntervalTrivariate.neg q)
  let b := DyadicIntervalTrivariate.add (rational lower)
    (DyadicIntervalTrivariate.mul (rational (upper - lower))
      (DyadicIntervalTrivariate.second precision))
  let r := DyadicIntervalTrivariate.add (sub (coefficient 0) b)
    (DyadicIntervalTrivariate.mul
      (DyadicIntervalTrivariate.add (sub (rational 1) (coefficient 0)) b)
      (DyadicIntervalTrivariate.first precision))
  let t := DyadicIntervalTrivariate.add (rational (-1))
    (DyadicIntervalTrivariate.mul (rational 2)
      (DyadicIntervalTrivariate.third precision))
  ⟨r, b, t⟩

/-- The reduced weighted-self formula evaluated by fixed-precision dyadic arithmetic. -/
def dyadicWeightedSelfFormula (precision : ℕ) (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) :
    WeightedSelfFormula (DyadicIntervalTrivariate precision) :=
  let chart := dyadicWeightedSelfChart precision lower upper box
  weightedSelfFormula (dyadicSelfPolynomialOperations precision)
    (fun i ↦ .constant (.ofInterval precision (box i))) chart.r chart.b chart.t

/-- The dyadic interval polynomial enclosing `-P`. -/
def dyadicWeightedSelfNegativeP (precision : ℕ) (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) : DyadicIntervalTrivariate precision :=
  DyadicIntervalTrivariate.neg (dyadicWeightedSelfFormula precision lower upper box).p

/-- The dyadic interval polynomial enclosing `Q`. -/
def dyadicWeightedSelfQ (precision : ℕ) (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) : DyadicIntervalTrivariate precision :=
  (dyadicWeightedSelfFormula precision lower upper box).q

/-- The dyadic interval polynomial enclosing `P² - Q²R`. -/
def dyadicWeightedSelfDiscriminant (precision : ℕ) (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) : DyadicIntervalTrivariate precision :=
  let formula := dyadicWeightedSelfFormula precision lower upper box
  DyadicIntervalTrivariate.add
    (DyadicIntervalTrivariate.mul formula.p formula.p)
    (DyadicIntervalTrivariate.neg
      (DyadicIntervalTrivariate.mul
        (DyadicIntervalTrivariate.mul formula.q formula.q) formula.radicand))

private theorem dyadicWeightedSelfChart_widens (precision : ℕ) (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) :
    let D := dyadicWeightedSelfChart precision lower upper box
    let I := weightedSelfIntervalChart lower upper box
    D.r.Widens I.r ∧ D.b.Widens I.b ∧ D.t.Widens I.t := by
  let coefficient (i : Fin 18) := DyadicIntervalTrivariate.constant
    (DyadicInterval.ofInterval precision (box i))
  let rational (q : ℚ) :=
    DyadicIntervalTrivariate.constant (DyadicInterval.ofRat precision q)
  have hcoefficient (i : Fin 18) :
      (coefficient i).Widens (IntervalTrivariate.constant (box i)) :=
    DyadicIntervalTrivariate.constant_widens
      (DyadicInterval.ofInterval_widens precision (box i))
  have hrational (q : ℚ) :
      (rational q).Widens (IntervalTrivariate.constant (.singleton q)) :=
    DyadicIntervalTrivariate.constant_widens
      (DyadicInterval.ofInterval_widens precision (.singleton q))
  let Db := DyadicIntervalTrivariate.add (rational lower)
    (DyadicIntervalTrivariate.mul (rational (upper - lower))
      (DyadicIntervalTrivariate.second precision))
  let Ib := IntervalTrivariate.add (.constant (.singleton lower))
    (IntervalTrivariate.mul (.constant (.singleton (upper - lower))) .second)
  have hb : Db.Widens Ib := DyadicIntervalTrivariate.add_widens (hrational lower)
    (DyadicIntervalTrivariate.mul_widens (hrational (upper - lower))
      (DyadicIntervalTrivariate.second_widens precision))
  let Dr := DyadicIntervalTrivariate.add
    (DyadicIntervalTrivariate.add (coefficient 0) (DyadicIntervalTrivariate.neg Db))
    (DyadicIntervalTrivariate.mul
      (DyadicIntervalTrivariate.add
        (DyadicIntervalTrivariate.add (rational 1)
          (DyadicIntervalTrivariate.neg (coefficient 0))) Db)
      (DyadicIntervalTrivariate.first precision))
  let Ir := IntervalTrivariate.add
    (IntervalTrivariate.add (.constant (box 0)) (IntervalTrivariate.neg Ib))
    (IntervalTrivariate.mul
      (IntervalTrivariate.add
        (IntervalTrivariate.add (.constant (.singleton 1))
          (IntervalTrivariate.neg (.constant (box 0)))) Ib) .first)
  have hr : Dr.Widens Ir := DyadicIntervalTrivariate.add_widens
    (DyadicIntervalTrivariate.add_widens (hcoefficient 0)
      (DyadicIntervalTrivariate.neg_widens hb))
    (DyadicIntervalTrivariate.mul_widens
      (DyadicIntervalTrivariate.add_widens
        (DyadicIntervalTrivariate.add_widens (hrational 1)
          (DyadicIntervalTrivariate.neg_widens (hcoefficient 0))) hb)
      (DyadicIntervalTrivariate.first_widens precision))
  let Dt := DyadicIntervalTrivariate.add (rational (-1))
    (DyadicIntervalTrivariate.mul (rational 2)
      (DyadicIntervalTrivariate.third precision))
  let It := IntervalTrivariate.add (.constant (.singleton (-1)))
    (IntervalTrivariate.mul (.constant (.singleton 2)) .third)
  have ht : Dt.Widens It := DyadicIntervalTrivariate.add_widens (hrational (-1))
    (DyadicIntervalTrivariate.mul_widens (hrational 2)
      (DyadicIntervalTrivariate.third_widens precision))
  exact ⟨hr, hb, ht⟩

private def FormulaWidens {precision : ℕ}
    (D : WeightedSelfFormula (DyadicIntervalTrivariate precision))
    (I : WeightedSelfFormula IntervalTrivariate) : Prop :=
  D.p.Widens I.p ∧ D.q.Widens I.q ∧ D.radicand.Widens I.radicand

private theorem formulaWidens_p {precision : ℕ}
    {D : WeightedSelfFormula (DyadicIntervalTrivariate precision)}
    {I : WeightedSelfFormula IntervalTrivariate} (h : FormulaWidens D I) :
    D.p.Widens I.p := h.1

private theorem formulaWidens_q {precision : ℕ}
    {D : WeightedSelfFormula (DyadicIntervalTrivariate precision)}
    {I : WeightedSelfFormula IntervalTrivariate} (h : FormulaWidens D I) :
    D.q.Widens I.q := h.2.1

private theorem formulaWidens_radicand {precision : ℕ}
    {D : WeightedSelfFormula (DyadicIntervalTrivariate precision)}
    {I : WeightedSelfFormula IntervalTrivariate} (h : FormulaWidens D I) :
    D.radicand.Widens I.radicand := h.2.2

private structure PolynomialWidens {precision : ℕ}
    (D : DyadicIntervalTrivariate precision) (I : IntervalTrivariate) : Prop where
  sound : D.Widens I

private theorem polynomialWidens_of_widens {precision : ℕ}
    {D : DyadicIntervalTrivariate precision} {I : IntervalTrivariate}
    (h : D.Widens I) : PolynomialWidens D I := ⟨h⟩

private theorem intervalCertificate_of_polynomialWidens {precision : ℕ}
    {D : DyadicIntervalTrivariate precision} {I : IntervalTrivariate}
    (hwide : PolynomialWidens D I) (tree : TensorSubdivision)
    (hcheck : dyadicIntervalTensorSubdivisionCertifiesNonnegative tree
      (dyadicIntervalTensorBernsteinThird
        (dyadicIntervalTensorBernsteinSecond
          (dyadicIntervalTensorBernsteinFirst D.powerTensor))) = true) :
    intervalTensorSubdivisionCertifiesNonnegative tree I.bernsteinCoefficients = true :=
  dyadicIntervalPolynomialCertificate_sound hwide.sound tree hcheck

private theorem dyadicWeightedSelfFormula_widens (precision : ℕ) (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) :
    FormulaWidens (dyadicWeightedSelfFormula precision lower upper box)
      (weightedSelfIntervalFormula lower upper box) := by
  let Dchart := dyadicWeightedSelfChart precision lower upper box
  let Ichart := weightedSelfIntervalChart lower upper box
  let Dcoefficient (i : Fin 18) := DyadicIntervalTrivariate.constant
    (DyadicInterval.ofInterval precision (box i))
  let Icoefficient (i : Fin 18) := IntervalTrivariate.constant (box i)
  have hchart : Dchart.r.Widens Ichart.r ∧ Dchart.b.Widens Ichart.b ∧
      Dchart.t.Widens Ichart.t := by
    simpa only [Dchart, Ichart] using
      dyadicWeightedSelfChart_widens precision lower upper box
  have hformula :
      let D := weightedSelfFormula (dyadicSelfPolynomialOperations precision)
        Dcoefficient Dchart.r Dchart.b Dchart.t
      let I := weightedSelfFormula intervalPolynomialOperations
        Icoefficient Ichart.r Ichart.b Ichart.t
      D.p.Widens I.p ∧ D.q.Widens I.q ∧ D.radicand.Widens I.radicand := by
    apply weightedSelfFormula_rel (dyadicSelfPolynomialOperations precision)
      intervalPolynomialOperations DyadicIntervalTrivariate.Widens
    · intro q
      exact DyadicIntervalTrivariate.constant_widens
        (DyadicInterval.ofInterval_widens precision (.singleton q))
    · exact fun hA hB ↦ DyadicIntervalTrivariate.add_widens hA hB
    · exact fun hA ↦ DyadicIntervalTrivariate.neg_widens hA
    · exact fun hA hB ↦ DyadicIntervalTrivariate.mul_widens hA hB
    · exact fun hA n ↦ DyadicIntervalTrivariate.pow_widens hA n
    · intro i
      exact DyadicIntervalTrivariate.constant_widens
        (DyadicInterval.ofInterval_widens precision (box i))
    · exact hchart.1
    · exact hchart.2.1
    · exact hchart.2.2
  unfold FormulaWidens
  simpa only [dyadicWeightedSelfFormula, weightedSelfIntervalFormula,
    Dchart, Ichart, Dcoefficient, Icoefficient] using hformula

private def CertificatePolynomialsWiden {precision : ℕ}
    (D : WeightedSelfFormula (DyadicIntervalTrivariate precision))
    (I : WeightedSelfFormula IntervalTrivariate) : Prop :=
  PolynomialWidens (DyadicIntervalTrivariate.neg D.p) (IntervalTrivariate.neg I.p) ∧
    PolynomialWidens D.q I.q ∧
      PolynomialWidens
        (DyadicIntervalTrivariate.add
          (DyadicIntervalTrivariate.mul D.p D.p)
          (DyadicIntervalTrivariate.neg
            (DyadicIntervalTrivariate.mul
              (DyadicIntervalTrivariate.mul D.q D.q) D.radicand)))
        (IntervalTrivariate.add
          (IntervalTrivariate.mul I.p I.p)
          (IntervalTrivariate.neg
            (IntervalTrivariate.mul
              (IntervalTrivariate.mul I.q I.q) I.radicand)))

private theorem certificatePolynomialsWiden_of_formulaWidens {precision : ℕ}
    {D : WeightedSelfFormula (DyadicIntervalTrivariate precision)}
    {I : WeightedSelfFormula IntervalTrivariate} (h : FormulaWidens D I) :
    CertificatePolynomialsWiden D I := by
  have hp := formulaWidens_p h
  have hq := formulaWidens_q h
  have hR := formulaWidens_radicand h
  refine ⟨polynomialWidens_of_widens (DyadicIntervalTrivariate.neg_widens hp),
    polynomialWidens_of_widens hq, ?_⟩
  exact polynomialWidens_of_widens (DyadicIntervalTrivariate.add_widens
    (DyadicIntervalTrivariate.mul_widens hp hp)
    (DyadicIntervalTrivariate.neg_widens
      (DyadicIntervalTrivariate.mul_widens
        (DyadicIntervalTrivariate.mul_widens hq hq) hR)))

private theorem certificatePolynomialsWiden_negativeP {precision : ℕ}
    {D : WeightedSelfFormula (DyadicIntervalTrivariate precision)}
    {I : WeightedSelfFormula IntervalTrivariate} (h : CertificatePolynomialsWiden D I) :
    PolynomialWidens (DyadicIntervalTrivariate.neg D.p) (IntervalTrivariate.neg I.p) :=
  h.1

private theorem certificatePolynomialsWiden_q {precision : ℕ}
    {D : WeightedSelfFormula (DyadicIntervalTrivariate precision)}
    {I : WeightedSelfFormula IntervalTrivariate} (h : CertificatePolynomialsWiden D I) :
    PolynomialWidens D.q I.q := h.2.1

private theorem certificatePolynomialsWiden_discriminant {precision : ℕ}
    {D : WeightedSelfFormula (DyadicIntervalTrivariate precision)}
    {I : WeightedSelfFormula IntervalTrivariate} (h : CertificatePolynomialsWiden D I) :
    PolynomialWidens
      (DyadicIntervalTrivariate.add
        (DyadicIntervalTrivariate.mul D.p D.p)
        (DyadicIntervalTrivariate.neg
          (DyadicIntervalTrivariate.mul
            (DyadicIntervalTrivariate.mul D.q D.q) D.radicand)))
      (IntervalTrivariate.add
        (IntervalTrivariate.mul I.p I.p)
        (IntervalTrivariate.neg
          (IntervalTrivariate.mul
            (IntervalTrivariate.mul I.q I.q) I.radicand))) :=
  h.2.2

private theorem dyadicWeightedSelfCertificatePolynomials_widen (precision : ℕ)
    (lower upper : ℚ) (box : Fin 18 → RationalInterval) :
    CertificatePolynomialsWiden
      (dyadicWeightedSelfFormula precision lower upper box)
      (weightedSelfIntervalFormula lower upper box) :=
  certificatePolynomialsWiden_of_formulaWidens
    (dyadicWeightedSelfFormula_widens precision lower upper box)

private theorem dyadicWeightedSelfNegativeP_widens (precision : ℕ)
    (lower upper : ℚ) (box : Fin 18 → RationalInterval) :
    PolynomialWidens (dyadicWeightedSelfNegativeP precision lower upper box)
      (weightedSelfNegativePIntervalPolynomial lower upper box) := by
  have h := certificatePolynomialsWiden_negativeP
    (dyadicWeightedSelfCertificatePolynomials_widen precision lower upper box)
  simpa only [dyadicWeightedSelfNegativeP,
    weightedSelfNegativePIntervalPolynomial] using h

private theorem dyadicWeightedSelfQ_widens (precision : ℕ)
    (lower upper : ℚ) (box : Fin 18 → RationalInterval) :
    PolynomialWidens (dyadicWeightedSelfQ precision lower upper box)
      (weightedSelfQIntervalPolynomial lower upper box) := by
  have h := certificatePolynomialsWiden_q
    (dyadicWeightedSelfCertificatePolynomials_widen precision lower upper box)
  simpa only [dyadicWeightedSelfQ, weightedSelfQIntervalPolynomial] using h

private theorem dyadicWeightedSelfDiscriminant_widens (precision : ℕ)
    (lower upper : ℚ) (box : Fin 18 → RationalInterval) :
    PolynomialWidens (dyadicWeightedSelfDiscriminant precision lower upper box)
      (weightedSelfDiscriminantIntervalPolynomial lower upper box) := by
  have h := certificatePolynomialsWiden_discriminant
    (dyadicWeightedSelfCertificatePolynomials_widen precision lower upper box)
  simpa only [dyadicWeightedSelfDiscriminant,
    weightedSelfDiscriminantIntervalPolynomial] using h

/-- Directly check one dyadic polynomial on a prescribed Bernstein subdivision. -/
def checkDyadicWeightedSelfPolynomial (tree : TensorSubdivision)
    (p : DyadicIntervalTrivariate precision) : Bool :=
  dyadicIntervalTensorSubdivisionCertifiesNonnegative tree
    (dyadicIntervalTensorBernsteinThird
      (dyadicIntervalTensorBernsteinSecond
        (dyadicIntervalTensorBernsteinFirst p.powerTensor)))

/-- Three direct dyadic checks imply the weighted-self estimate on one radius bin. -/
theorem weightedSelfRadiusBinBound_of_dyadic_certificates
    (precision : ℕ) (lower upper : ℚ)
    (hwidth : (lower : ℝ) < upper) (hupper : (upper : ℝ) ≤ 1)
    (kappaDBox kappaCBox : RationalInterval)
    (hD : (weightedSelfCoefficientExpression upper 10).certifiesWithin
      weightedSelfEndpointBox kappaDBox = true)
    (hC : (weightedSelfCoefficientExpression upper 14).certifiesWithin
      weightedSelfEndpointBox kappaCBox = true)
    (negativePTree qTree discriminantTree : TensorSubdivision)
    (hnegativeP : checkDyadicWeightedSelfPolynomial negativePTree
      (dyadicWeightedSelfNegativeP precision lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox)) = true)
    (hq : checkDyadicWeightedSelfPolynomial qTree
      (dyadicWeightedSelfQ precision lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox)) = true)
    (hdiscriminant : checkDyadicWeightedSelfPolynomial discriminantTree
      (dyadicWeightedSelfDiscriminant precision lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox)) = true) :
    WeightedSelfRadiusBinBound lower upper := by
  apply weightedSelfRadiusBinBound_of_interval_certificates lower upper hwidth hupper
    kappaDBox kappaCBox hD hC negativePTree qTree discriminantTree
  · apply intervalCertificate_of_polynomialWidens
      (D := dyadicWeightedSelfNegativeP precision lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (I := weightedSelfNegativePIntervalPolynomial lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (dyadicWeightedSelfNegativeP_widens precision lower upper _) negativePTree
    simpa only [checkDyadicWeightedSelfPolynomial] using hnegativeP
  · apply intervalCertificate_of_polynomialWidens
      (D := dyadicWeightedSelfQ precision lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (I := weightedSelfQIntervalPolynomial lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (dyadicWeightedSelfQ_widens precision lower upper _) qTree
    simpa only [checkDyadicWeightedSelfPolynomial] using hq
  · apply intervalCertificate_of_polynomialWidens
      (D := dyadicWeightedSelfDiscriminant precision lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (I := weightedSelfDiscriminantIntervalPolynomial lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (dyadicWeightedSelfDiscriminant_widens precision lower upper _)
      discriminantTree
    simpa only [checkDyadicWeightedSelfPolynomial] using hdiscriminant

end Bescovitch
