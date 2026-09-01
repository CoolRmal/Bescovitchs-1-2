/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.NormalizedBivariateBernstein
public import Bescovitch.SixPoint.WeightedSelfExceptionalCertificate

/-!
# Normalized Bernstein certificates for the exceptional weighted-self face

The unresolved face is parametrized by
`b = 29 / 40 + u / 40` and `t = -209 / 256 + v / 256` on the unit square.
Normalizing this substitution before interval arithmetic exposes the true bidegrees `8 × 4`
and `16 × 8` of the Hessian diagonal and determinant. Both are padded to one `16 × 8`
certificate format. The radial derivative remains on the existing interval-Horner checker.
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace Bescovitch

namespace RadicalExpression

/-- Convert the polynomial fragment of a radical expression to a normalized polynomial. -/
def polynomialPart? {n : ℕ} :
    RadicalExpression n → Option (MvPolynomial (Fin n) ℚ)
  | .var i => some (MvPolynomial.X i)
  | .constant q => some (MvPolynomial.C q)
  | .add a b => return (← a.polynomialPart?) + (← b.polynomialPart?)
  | .neg a => return -(← a.polynomialPart?)
  | .mul a b => return (← a.polynomialPart?) * (← b.polynomialPart?)
  | .inv _ | .sqrt _ _ _ => none

private theorem eval_polynomialPart? {n : ℕ} {e : RadicalExpression n}
    {p : MvPolynomial (Fin n) ℚ} (h : e.polynomialPart? = some p)
    (input : Fin n → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) input p = e.eval input := by
  induction e generalizing p with
  | var i =>
      simp only [polynomialPart?, Option.some.injEq] at h
      subst p
      simp [RadicalExpression.eval]
  | constant q =>
      simp only [polynomialPart?, Option.some.injEq] at h
      subst p
      simp [RadicalExpression.eval]
  | add a b ha hb =>
      cases hpa : a.polynomialPart? with
      | none => simp [polynomialPart?, hpa] at h
      | some pa =>
          cases hpb : b.polynomialPart? with
          | none => simp [polynomialPart?, hpa, hpb] at h
          | some pb =>
              simp only [polynomialPart?, hpa, hpb] at h
              have hp : some (pa + pb) = some p := h
              injection hp with hp
              subst p
              simp [MvPolynomial.eval₂_add, ha hpa, hb hpb, RadicalExpression.eval]
  | neg a ha =>
      cases hpa : a.polynomialPart? with
      | none => simp [polynomialPart?, hpa] at h
      | some pa =>
          simp only [polynomialPart?, hpa] at h
          have hp : some (-pa) = some p := h
          injection hp with hp
          subst p
          simp [ha hpa, RadicalExpression.eval]
  | mul a b ha hb =>
      cases hpa : a.polynomialPart? with
      | none => simp [polynomialPart?, hpa] at h
      | some pa =>
          cases hpb : b.polynomialPart? with
          | none => simp [polynomialPart?, hpa, hpb] at h
          | some pb =>
              simp only [polynomialPart?, hpa, hpb] at h
              have hp : some (pa * pb) = some p := h
              injection hp with hp
              subst p
              simp [MvPolynomial.eval₂_mul, ha hpa, hb hpb, RadicalExpression.eval]
  | inv a => simp [polynomialPart?] at h
  | sqrt a lower upper => simp [polynomialPart?] at h

end RadicalExpression

namespace RadicalUnivariate

/-- Substitute one normalized bivariate polynomial into a dense radical polynomial. -/
def normalizedSubstitution? {n : ℕ} (p : RadicalUnivariate n)
    (x : NormalizedBivariatePolynomial n) : Option (NormalizedBivariatePolynomial n) :=
  match p with
  | [] => some 0
  | a :: q => return MvPolynomial.C (← a.polynomialPart?) +
      x * (← normalizedSubstitution? q x)

private theorem eval_normalizedSubstitution? {n : ℕ} {p : RadicalUnivariate n}
    {x q : NormalizedBivariatePolynomial n} (h : p.normalizedSubstitution? x = some q)
    (input : Fin n → ℝ) (u v : ℝ) :
    q.eval input u v = p.eval input (x.eval input u v) := by
  induction p generalizing q with
  | nil =>
      simp only [normalizedSubstitution?, Option.some.injEq] at h
      subst q
      simp [NormalizedBivariatePolynomial.eval, RadicalUnivariate.eval]
  | cons a p ih =>
      cases ha : a.polynomialPart? with
      | none => simp [normalizedSubstitution?, ha] at h
      | some ap =>
          cases hp : RadicalUnivariate.normalizedSubstitution? p x with
          | none => simp [normalizedSubstitution?, ha, hp] at h
          | some qp =>
              simp only [normalizedSubstitution?, ha, hp] at h
              have hq : some (MvPolynomial.C ap + x * qp) = some q := h
              injection hq with hq
              subst q
              simp only [NormalizedBivariatePolynomial.eval,
                MvPolynomial.eval₂_add, MvPolynomial.eval₂_C,
                MvPolynomial.eval₂_mul, MvPolynomial.coe_eval₂Hom,
                RadicalUnivariate.eval]
              have htail : MvPolynomial.eval₂
                  (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) input)
                  (![u, v] : Fin 2 → ℝ) qp =
                    RadicalUnivariate.eval p input
                      (NormalizedBivariatePolynomial.eval x input u v) := ih hp
              rw [RadicalExpression.eval_polynomialPart? ha, htail]
              simp only [NormalizedBivariatePolynomial.eval]

end RadicalUnivariate

namespace RadicalBivariate

/-- Substitute two normalized polynomials into a dense radical bivariate polynomial. -/
def normalizedSubstitution? {n : ℕ} (p : RadicalBivariate n)
    (x y : NormalizedBivariatePolynomial n) : Option (NormalizedBivariatePolynomial n) :=
  match p with
  | [] => some 0
  | a :: q => return (← a.normalizedSubstitution? y) +
      x * (← normalizedSubstitution? q x y)

private theorem eval_normalizedSubstitution? {n : ℕ} {p : RadicalBivariate n}
    {x y q : NormalizedBivariatePolynomial n}
    (h : p.normalizedSubstitution? x y = some q)
    (input : Fin n → ℝ) (u v : ℝ) :
    q.eval input u v = p.eval input (x.eval input u v) (y.eval input u v) := by
  induction p generalizing q with
  | nil =>
      simp only [normalizedSubstitution?, Option.some.injEq] at h
      subst q
      simp [NormalizedBivariatePolynomial.eval, RadicalBivariate.eval]
  | cons a p ih =>
      cases ha : a.normalizedSubstitution? y with
      | none => simp [normalizedSubstitution?, ha] at h
      | some ap =>
          cases hp : RadicalBivariate.normalizedSubstitution? p x y with
          | none => simp [normalizedSubstitution?, ha, hp] at h
          | some qp =>
              simp only [normalizedSubstitution?, ha, hp] at h
              have hq : some (ap + x * qp) = some q := h
              injection hq with hq
              subst q
              simp only [NormalizedBivariatePolynomial.eval,
                MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
                RadicalBivariate.eval]
              have hhead : MvPolynomial.eval₂
                  (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) input)
                  (![u, v] : Fin 2 → ℝ) ap =
                    RadicalUnivariate.eval a input
                      (NormalizedBivariatePolynomial.eval y input u v) :=
                RadicalUnivariate.eval_normalizedSubstitution? ha input u v
              have htail : MvPolynomial.eval₂
                  (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) input)
                  (![u, v] : Fin 2 → ℝ) qp =
                    RadicalBivariate.eval p input
                      (NormalizedBivariatePolynomial.eval x input u v)
                      (NormalizedBivariatePolynomial.eval y input u v) := ih hp
              rw [hhead, htail]
              simp only [NormalizedBivariatePolynomial.eval]

end RadicalBivariate

namespace RadicalTrivariate

/-- Substitute three normalized polynomials into a dense radical trivariate polynomial. -/
def normalizedSubstitution? {n : ℕ} (p : RadicalTrivariate n)
    (x y z : NormalizedBivariatePolynomial n) : Option (NormalizedBivariatePolynomial n) :=
  match p with
  | [] => some 0
  | a :: q => return (← a.normalizedSubstitution? y z) +
      x * (← normalizedSubstitution? q x y z)

private theorem eval_normalizedSubstitution? {n : ℕ} {p : RadicalTrivariate n}
    {x y z q : NormalizedBivariatePolynomial n}
    (h : p.normalizedSubstitution? x y z = some q)
    (input : Fin n → ℝ) (u v : ℝ) :
    q.eval input u v =
      p.eval input (x.eval input u v) (y.eval input u v) (z.eval input u v) := by
  induction p generalizing q with
  | nil =>
      simp only [normalizedSubstitution?, Option.some.injEq] at h
      subst q
      simp [NormalizedBivariatePolynomial.eval, RadicalTrivariate.eval]
  | cons a p ih =>
      cases ha : a.normalizedSubstitution? y z with
      | none => simp [normalizedSubstitution?, ha] at h
      | some ap =>
          cases hp : RadicalTrivariate.normalizedSubstitution? p x y z with
          | none => simp [normalizedSubstitution?, ha, hp] at h
          | some qp =>
              simp only [normalizedSubstitution?, ha, hp] at h
              have hq : some (ap + x * qp) = some q := h
              injection hq with hq
              subst q
              simp only [NormalizedBivariatePolynomial.eval,
                MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
                RadicalTrivariate.eval]
              have hhead : MvPolynomial.eval₂
                  (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) input)
                  (![u, v] : Fin 2 → ℝ) ap =
                    RadicalBivariate.eval a input
                      (NormalizedBivariatePolynomial.eval y input u v)
                      (NormalizedBivariatePolynomial.eval z input u v) :=
                RadicalBivariate.eval_normalizedSubstitution? ha input u v
              have htail : MvPolynomial.eval₂
                  (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) input)
                  (![u, v] : Fin 2 → ℝ) qp =
                    RadicalTrivariate.eval p input
                      (NormalizedBivariatePolynomial.eval x input u v)
                      (NormalizedBivariatePolynomial.eval y input u v)
                      (NormalizedBivariatePolynomial.eval z input u v) := ih hp
              rw [hhead, htail]
              simp only [NormalizedBivariatePolynomial.eval]

private theorem eval_normalizedSubstitution_get {n : ℕ} (p : RadicalTrivariate n)
    (x y z : NormalizedBivariatePolynomial n)
    (h : (p.normalizedSubstitution? x y z).isSome)
    (input : Fin n → ℝ) (u v : ℝ) :
    MvPolynomial.eval₂ (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) input)
        (![u, v] : Fin 2 → ℝ) ((p.normalizedSubstitution? x y z).get h) =
      p.eval input (x.eval input u v) (y.eval input u v) (z.eval input u v) := by
  exact eval_normalizedSubstitution? (Option.some_get h).symm input u v

end RadicalTrivariate

/-- The affine second-radius chart `b = 29 / 40 + u / 40`. -/
def weightedSelfExceptionalSecondRadiusChart : NormalizedBivariatePolynomial 18 :=
  MvPolynomial.C (MvPolynomial.C (29 / 40)) +
    MvPolynomial.C (MvPolynomial.C (1 / 40)) * MvPolynomial.X 0

/-- The affine projection chart `t = -209 / 256 + v / 256`. -/
def weightedSelfExceptionalProjectionChart : NormalizedBivariatePolynomial 18 :=
  MvPolynomial.C (MvPolynomial.C (-209 / 256)) +
    MvPolynomial.C (MvPolynomial.C (1 / 256)) * MvPolynomial.X 1

/-- The chart `bb` Hessian entry after removing the fixed positive physical margin. -/
def weightedSelfExceptionalFaceBBMarginChartPolynomial :
    NormalizedBivariatePolynomial 18 :=
  MvPolynomial.C (MvPolynomial.C (1 / 1600)) *
      (weightedSelfExceptionalFaceBBPolynomial.normalizedSubstitution?
        (MvPolynomial.C (MvPolynomial.C 1))
        weightedSelfExceptionalSecondRadiusChart
        weightedSelfExceptionalProjectionChart).get
        (by rfl) -
    MvPolynomial.C (MvPolynomial.C (1 / 16000000))

/-- The determinant of the face Hessian in the unit-square affine chart. -/
def weightedSelfExceptionalFaceDeterminantChartPolynomial :
    NormalizedBivariatePolynomial 18 :=
  MvPolynomial.C (MvPolynomial.C (1 / 104857600)) *
    ((weightedSelfExceptionalFaceBBPolynomial.normalizedSubstitution?
        (MvPolynomial.C (MvPolynomial.C 1))
        weightedSelfExceptionalSecondRadiusChart
        weightedSelfExceptionalProjectionChart).get (by rfl) *
      (weightedSelfExceptionalFaceTTPolynomial.normalizedSubstitution?
        (MvPolynomial.C (MvPolynomial.C 1))
        weightedSelfExceptionalSecondRadiusChart
        weightedSelfExceptionalProjectionChart).get (by rfl) -
      (weightedSelfExceptionalFaceBTPolynomial.normalizedSubstitution?
        (MvPolynomial.C (MvPolynomial.C 1))
        weightedSelfExceptionalSecondRadiusChart
        weightedSelfExceptionalProjectionChart).get (by rfl) ^ 2)

/-- The chart `bb` margin is the physical `bb` margin divided by `40²`. -/
theorem weightedSelfExceptionalFaceBBMarginChartPolynomial_eval
    (input : Fin 18 → ℝ) (u v : ℝ) :
    weightedSelfExceptionalFaceBBMarginChartPolynomial.eval input u v =
      (weightedSelfExceptionalFaceBBPolynomial.eval input 1
        (29 / 40 + u / 40) (-209 / 256 + v / 256) - 1 / 10000) / 1600 := by
  simp only [weightedSelfExceptionalFaceBBMarginChartPolynomial,
    NormalizedBivariatePolynomial.eval, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  rw [RadicalTrivariate.eval_normalizedSubstitution_get]
  simp only [NormalizedBivariatePolynomial.eval, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    weightedSelfExceptionalSecondRadiusChart,
    weightedSelfExceptionalProjectionChart]
  norm_num
  ring_nf

/-- The chart Hessian determinant is the physical determinant divided by `40² 256²`. -/
theorem weightedSelfExceptionalFaceDeterminantChartPolynomial_eval
    (input : Fin 18 → ℝ) (u v : ℝ) :
    weightedSelfExceptionalFaceDeterminantChartPolynomial.eval input u v =
      weightedSelfExceptionalFaceDeterminantPolynomial.eval input 1
        (29 / 40 + u / 40) (-209 / 256 + v / 256) / 104857600 := by
  simp only [weightedSelfExceptionalFaceDeterminantChartPolynomial,
    NormalizedBivariatePolynomial.eval, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_C]
  rw [RadicalTrivariate.eval_normalizedSubstitution_get,
    RadicalTrivariate.eval_normalizedSubstitution_get,
    RadicalTrivariate.eval_normalizedSubstitution_get]
  simp only [NormalizedBivariatePolynomial.eval, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    weightedSelfExceptionalSecondRadiusChart,
    weightedSelfExceptionalProjectionChart]
  simp only [weightedSelfExceptionalFaceDeterminantPolynomial,
    RadicalTrivariate.eval_add, RadicalTrivariate.eval_mul,
    RadicalTrivariate.eval_neg, RadicalTrivariate.eval_pow]
  norm_num
  ring_nf

private theorem exists_weightedSelfExceptionalFaceChart {b t : ℝ}
    (hbLower : (29 : ℝ) / 40 ≤ b) (hbUpper : b ≤ 3 / 4)
    (htLower : (-209 : ℝ) / 256 ≤ t) (htUpper : t ≤ -13 / 16) :
    ∃ u v : I,
      (29 : ℝ) / 40 + (u : ℝ) / 40 = b ∧
        (-209 : ℝ) / 256 + (v : ℝ) / 256 = t := by
  let u : I := ⟨40 * b - 29, by
    constructor <;> norm_num at hbLower hbUpper ⊢ <;> linarith⟩
  let v : I := ⟨256 * t + 209, by
    constructor <;> norm_num at htLower htUpper ⊢ <;> linarith⟩
  refine ⟨u, v, ?_, ?_⟩
  · simp only [u]
    ring
  · simp only [v]
    ring

private theorem weightedSelfExceptionalNegativeRadial_nonneg_of_leaf_certificate
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput (4 / 5) i))
    (hcertificate : intervalPolynomialSubdivisionCertifiesNonnegative .leaf
      (weightedSelfExceptionalNegativeRadialIntervalPolynomial box)
      weightedSelfExceptionalRadiusInterval
      weightedSelfExceptionalSecondRadiusInterval
      weightedSelfExceptionalProjectionInterval = true)
    {r b t : ℝ}
    (hrLower : weightedSelfExceptionalRadialLower b ≤ r) (hrUpper : r ≤ 1)
    (hbLower : (29 : ℝ) / 40 ≤ b) (hbUpper : b ≤ 3 / 4)
    (htLower : (-209 : ℝ) / 256 ≤ t) (htUpper : t ≤ -13 / 16) :
    0 ≤ weightedSelfExceptionalNegativeRadialPolynomial.eval
      (weightedSelfCoefficientInput (4 / 5)) r b t := by
  apply RadicalTrivariate.nonneg_of_interval_box_certificate
    weightedSelfExceptionalNegativeRadialPolynomial
    (weightedSelfExceptionalNegativeRadialIntervalPolynomial box)
    (weightedSelfCoefficientInput (4 / 5))
    (weightedSelfExceptionalNegativeRadialInterval_contains box hinput) .leaf hcertificate
  · have hrMem : (8191 : ℝ) / 8192 ≤ r ∧ r ≤ 1 := by
      constructor
      · rw [weightedSelfExceptionalRadialLower] at hrLower
        norm_num at hbUpper hrLower ⊢
        nlinarith [one_lt_cStar_and_cStar_lt_two.1]
      · exact hrUpper
    simpa [weightedSelfExceptionalRadiusInterval, RationalInterval.Contains] using hrMem
  · simpa [weightedSelfExceptionalSecondRadiusInterval,
      RationalInterval.Contains] using And.intro hbLower hbUpper
  · simpa [weightedSelfExceptionalProjectionInterval,
      RationalInterval.Contains] using And.intro htLower htUpper

private theorem weightedSelfExceptionalFaceBB_positive_of_bernstein_certificate
    {box : Fin 18 → RationalInterval}
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput (4 / 5) i))
    (certificate : NormalizedBivariatePolynomial.BernsteinCertificate box
      weightedSelfExceptionalFaceBBMarginChartPolynomial)
    (hcertificate : certificate.certifiesNonnegative = true)
    {b t : ℝ} (hbLower : (29 : ℝ) / 40 ≤ b) (hbUpper : b ≤ 3 / 4)
    (htLower : (-209 : ℝ) / 256 ≤ t) (htUpper : t ≤ -13 / 16) :
    0 < weightedSelfExceptionalFaceBBPolynomial.eval
      (weightedSelfCoefficientInput (4 / 5)) 1 b t := by
  obtain ⟨u, v, hu, hv⟩ :=
    exists_weightedSelfExceptionalFaceChart hbLower hbUpper htLower htUpper
  have hchart := NormalizedBivariatePolynomial.nonnegative_of_certificate
    certificate hinput hcertificate u v
  rw [weightedSelfExceptionalFaceBBMarginChartPolynomial_eval, hu, hv] at hchart
  norm_num at hchart ⊢
  linarith

private theorem weightedSelfExceptionalFaceDeterminant_nonneg_of_bernstein_certificate
    {box : Fin 18 → RationalInterval}
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput (4 / 5) i))
    (certificate : NormalizedBivariatePolynomial.BernsteinCertificate box
      weightedSelfExceptionalFaceDeterminantChartPolynomial)
    (hcertificate : certificate.certifiesNonnegative = true)
    {b t : ℝ} (hbLower : (29 : ℝ) / 40 ≤ b) (hbUpper : b ≤ 3 / 4)
    (htLower : (-209 : ℝ) / 256 ≤ t) (htUpper : t ≤ -13 / 16) :
    0 ≤ weightedSelfExceptionalFaceDeterminantPolynomial.eval
      (weightedSelfCoefficientInput (4 / 5)) 1 b t := by
  obtain ⟨u, v, hu, hv⟩ :=
    exists_weightedSelfExceptionalFaceChart hbLower hbUpper htLower htUpper
  have hchart := NormalizedBivariatePolynomial.nonnegative_of_certificate
    certificate hinput hcertificate u v
  rw [weightedSelfExceptionalFaceDeterminantChartPolynomial_eval, hu, hv] at hchart
  norm_num at hchart ⊢
  linarith

set_option maxHeartbeats 5000000 in
/-- A radial Horner check and two normalized Bernstein checks settle the exceptional box. -/
theorem weightedSelfDiscriminant_nonneg_on_exceptionalBox_of_bernstein_certificates
    (kappaDBox kappaCBox : RationalInterval)
    (hD : (weightedSelfCoefficientExpression (4 / 5) 10).certifiesWithin
      weightedSelfEndpointBox kappaDBox = true)
    (hC : (weightedSelfCoefficientExpression (4 / 5) 14).certifiesWithin
      weightedSelfEndpointBox kappaCBox = true)
    (hradialCertificate : intervalPolynomialSubdivisionCertifiesNonnegative .leaf
      (weightedSelfExceptionalNegativeRadialIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      weightedSelfExceptionalRadiusInterval
      weightedSelfExceptionalSecondRadiusInterval
      weightedSelfExceptionalProjectionInterval = true)
    (bbCertificate : NormalizedBivariatePolynomial.BernsteinCertificate
      (weightedSelfCoefficientBox kappaDBox kappaCBox)
      weightedSelfExceptionalFaceBBMarginChartPolynomial)
    (determinantCertificate : NormalizedBivariatePolynomial.BernsteinCertificate
      (weightedSelfCoefficientBox kappaDBox kappaCBox)
      weightedSelfExceptionalFaceDeterminantChartPolynomial)
    (hbbCertificate : bbCertificate.certifiesNonnegative = true)
    (hdeterminantCertificate : determinantCertificate.certifiesNonnegative = true)
    {r b t : ℝ}
    (hrLower : weightedSelfExceptionalRadialLower b ≤ r) (hrUpper : r ≤ 1)
    (hbLower : (29 : ℝ) / 40 ≤ b) (hbUpper : b ≤ 3 / 4)
    (htLower : (-209 : ℝ) / 256 ≤ t) (htUpper : t ≤ -13 / 16) :
    0 ≤ weightedSelfDiscriminant r b t (4 / 5) := by
  let box := weightedSelfCoefficientBox kappaDBox kappaCBox
  have hinputRaw := weightedSelfCoefficientInput_mem
    ((4 : ℚ) / 5) kappaDBox kappaCBox hD hC
  have hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput (4 / 5) i) := by
    intro i
    change (weightedSelfCoefficientBox kappaDBox kappaCBox i).Contains _
    convert hinputRaw i using 1
    norm_num
  apply weightedSelfDiscriminant_nonneg_on_exceptionalBox_of_polynomial_signs
  · intro r' b' t' hr'Lower hr'Upper hb'Lower hb'Upper ht'Lower ht'Upper
    exact weightedSelfExceptionalNegativeRadial_nonneg_of_leaf_certificate
      box hinput hradialCertificate hr'Lower hr'Upper hb'Lower hb'Upper ht'Lower ht'Upper
  · intro b' t' hb'Lower hb'Upper ht'Lower ht'Upper
    exact weightedSelfExceptionalFaceBB_positive_of_bernstein_certificate
      hinput bbCertificate hbbCertificate hb'Lower hb'Upper ht'Lower ht'Upper
  · intro b' t' hb'Lower hb'Upper ht'Lower ht'Upper
    exact weightedSelfExceptionalFaceDeterminant_nonneg_of_bernstein_certificate
      hinput determinantCertificate hdeterminantCertificate
      hb'Lower hb'Upper ht'Lower ht'Upper
  · exact hrLower
  · exact hrUpper
  · exact hbLower
  · exact hbUpper
  · exact htLower
  · exact htUpper

end Bescovitch
