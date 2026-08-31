/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.EndpointWeights
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef

/-!
# The weighted self inequality

This file proves the one-pair inequality for the exact endpoint weights.  The analytic
certificate retains a quartic remainder in each scalar norm tangent; these remainders supply
the curvature lost by the usual quadratic tangent bound.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Bescovitch

theorem mul_le_quadratic_tangent_sub_quartic {x weight d M : ℝ}
    (hx_zero : 0 ≤ x) (hweight : 0 ≤ weight) (hd : 0 < d) (hx : x ≤ M) :
    weight * x ≤ weight / (2 * d) * x ^ 2 + weight * d / 2 -
      weight / (2 * d * (M + d) ^ 2) * (x ^ 2 - d ^ 2) ^ 2 := by
  have hM : 0 ≤ M := hx_zero.trans hx
  have hsum : 0 < M + d := add_pos_of_nonneg_of_pos hM hd
  have hxSum : 0 ≤ x + d := add_nonneg hx_zero hd.le
  have hsumLe : x + d ≤ M + d := by
    simpa [add_comm] using add_le_add_right hx d
  have hsquare : (x + d) ^ 2 ≤ (M + d) ^ 2 :=
    (sq_le_sq₀ hxSum hsum.le).2 hsumLe
  have hproduct : (x ^ 2 - d ^ 2) ^ 2 ≤
      (x - d) ^ 2 * (M + d) ^ 2 := by
    nlinarith [sq_nonneg (x - d)]
  have hcoefficient : 0 ≤ weight / (2 * d * (M + d) ^ 2) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hproduct hcoefficient
  field_simp [hd.ne', hsum.ne'] at hscaled ⊢
  nlinarith [sq_nonneg (x - d)]

private theorem weighted_norm_tangent_with_remainder
    {E : Type*} [SeminormedAddCommGroup E] (x : E) {weight d M : ℝ}
    (hweight : 0 ≤ weight) (hd : 0 < d) (hx : ‖x‖ ≤ M) :
    weight * ‖x‖ ≤ weight / (2 * d) * ‖x‖ ^ 2 + weight * d / 2 -
      weight / (2 * d * (M + d) ^ 2) * (‖x‖ ^ 2 - d ^ 2) ^ 2 :=
  mul_le_quadratic_tangent_sub_quartic (norm_nonneg x) hweight hd hx

private theorem gram_three_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p q : E) :
    0 ≤ ‖e‖ ^ 2 * ‖p‖ ^ 2 * ‖q‖ ^ 2 - ‖e‖ ^ 2 * ⟪p, q⟫_ℝ ^ 2 -
      ⟪e, p⟫_ℝ ^ 2 * ‖q‖ ^ 2 + 2 * ⟪e, p⟫_ℝ * ⟪p, q⟫_ℝ * ⟪e, q⟫_ℝ -
      ⟪e, q⟫_ℝ ^ 2 * ‖p‖ ^ 2 := by
  let v : Fin 3 → E := ![e, p, q]
  have hdet := (Matrix.posSemidef_gram ℝ v).det_nonneg
  simp [Matrix.det_fin_three, Matrix.gram_apply, v, real_inner_comm] at hdet
  nlinarith

/-- The inner product forced by two radii and a chord length. -/
def chordInnerProduct (c r b : ℝ) : ℝ :=
  (r ^ 2 + b ^ 2 - c ^ 2) / 2

/-- The Gram radicand for the lowest feasible second projection. -/
def chordProjectionRadicand (c r b t : ℝ) : ℝ :=
  (1 - t ^ 2) * (r ^ 2 * b ^ 2 - chordInnerProduct c r b ^ 2)

/-- The lowest second projection compatible with the chord Gram matrix. -/
def chordLowerProjection (c r b t : ℝ) : ℝ :=
  (chordInnerProduct c r b * t - Real.sqrt (chordProjectionRadicand c r b t)) / r

private theorem chordLowerProjection_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p q : E) {c : ℝ} (he : ‖e‖ = 1)
    (hp : 0 < ‖p‖) (hchord : ‖p - q‖ = c) :
    -‖q‖ ≤ chordLowerProjection c ‖p‖ ‖q‖ (⟪e, p⟫_ℝ / ‖p‖) ∧
      chordLowerProjection c ‖p‖ ‖q‖ (⟪e, p⟫_ℝ / ‖p‖) ≤ ⟪e, q⟫_ℝ := by
  let r := ‖p‖
  let b := ‖q‖
  let t := ⟪e, p⟫_ℝ / r
  let k := chordInnerProduct c r b
  let R := chordProjectionRadicand c r b t
  have hr : 0 < r := by simpa [r] using hp
  have hinner : ⟪e, p⟫_ℝ = r * t := by
    dsimp [t]
    field_simp [hr.ne']
  have hk : ⟪p, q⟫_ℝ = k := by
    have hchordSq := congrArg (fun x : ℝ ↦ x ^ 2) hchord
    rw [norm_sub_sq_real] at hchordSq
    dsimp [k, chordInnerProduct, r, b]
    nlinarith
  have hgram := gram_three_nonneg e p q
  rw [he] at hgram
  simp only [one_pow, one_mul] at hgram
  have hsquare : (r * ⟪e, q⟫_ℝ - k * t) ^ 2 ≤ R := by
    dsimp [R, chordProjectionRadicand]
    rw [hinner, hk] at hgram
    nlinarith
  have hR : 0 ≤ R := (sq_nonneg (r * ⟪e, q⟫_ℝ - k * t)).trans hsquare
  have hsqrtSq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR
  have hlower : chordLowerProjection c r b t ≤ ⟪e, q⟫_ℝ := by
    rw [chordLowerProjection]
    change (k * t - Real.sqrt R) / r ≤ ⟪e, q⟫_ℝ
    apply (div_le_iff₀ hr).2
    nlinarith [Real.sqrt_nonneg R]
  have htAbs : |t| ≤ 1 := by
    have h := abs_real_inner_le_norm e p
    rw [he, one_mul] at h
    rw [abs_le]
    rw [abs_le] at h
    constructor <;> nlinarith
  have hkAbs : |k| ≤ r * b := by
    simpa [hk, r, b] using abs_real_inner_le_norm p q
  have hproductAbs : |k * t| ≤ r * b := by
    rw [abs_mul]
    calc
      |k| * |t| ≤ (r * b) * 1 := by gcongr
      _ = r * b := mul_one _
  have hsum : 0 ≤ r * b + k * t := by
    have := neg_le_of_abs_le hproductAbs
    linarith
  have hsqrtLe : Real.sqrt R ≤ r * b + k * t := by
    apply (Real.sqrt_le_iff).2
    refine ⟨hsum, ?_⟩
    dsimp [R, chordProjectionRadicand]
    nlinarith [sq_nonneg (r * b * t + k)]
  have hminus : -b ≤ chordLowerProjection c r b t := by
    rw [chordLowerProjection]
    change -b ≤ (k * t - Real.sqrt R) / r
    apply (le_div_iff₀ hr).2
    nlinarith
  simpa [r, b, t] using And.intro hminus hlower

private theorem chord_coordinate_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p q : E) {c : ℝ} (he : ‖e‖ = 1) (hc : 1 < c)
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hchord : ‖p - q‖ = c) :
    c - 1 ≤ ‖p‖ ∧ ‖p‖ ≤ 1 ∧ c - ‖q‖ ≤ ‖p‖ ∧ ‖q‖ ≤ 1 ∧
      -1 ≤ ⟪e, p⟫_ℝ / ‖p‖ ∧ ⟪e, p⟫_ℝ / ‖p‖ ≤ 1 := by
  have hsum : c ≤ ‖p‖ + ‖q‖ := by
    rw [← hchord]
    exact norm_sub_le p q
  have hpPos : 0 < ‖p‖ := by linarith
  have hinner := abs_real_inner_le_norm e p
  rw [he, one_mul, abs_le] at hinner
  refine ⟨by linarith, hp, by linarith, hq, ?_, ?_⟩
  · apply (le_div_iff₀ hpPos).2
    nlinarith
  · apply (div_le_iff₀ hpPos).2
    nlinarith

/-- A norm tangent retaining the quartic remainder used in the self certificate. -/
def quarticNormTangent (weight target cap squaredDistance : ℝ) : ℝ :=
  weight / (2 * target) * squaredDistance + weight * target / 2 -
    weight / (2 * target * (cap + target) ^ 2) *
      (squaredDistance - target ^ 2) ^ 2

private theorem weighted_sqrt_le_quarticNormTangent {weight target cap q : ℝ}
    (hweight : 0 ≤ weight) (htarget : 0 < target) (hq : 0 ≤ q)
    (hcap : Real.sqrt q ≤ cap) :
    weight * Real.sqrt q ≤ quarticNormTangent weight target cap q := by
  have h := mul_le_quadratic_tangent_sub_quartic (Real.sqrt_nonneg q)
    hweight htarget hcap
  rw [Real.sq_sqrt hq] at h
  exact h

private theorem endpointSecondDistance_pos :
    0 < endpointSecondDistance cStar certifiedEndpointPair.2 := by
  rw [endpointSecondDistance]
  have hc := cStar_mem_isolation_box.1
  have hB := certifiedEndpointPair_second_mem_isolation_box.2
  nlinarith [sq_nonneg (cStar - 1)]

private theorem endpointFirstAuxiliaryDistance_pos :
    0 < endpointFirstAuxiliaryDistance certifiedEndpointPair.2 := by
  rw [endpointFirstAuxiliaryDistance]
  exact Real.sqrt_pos.2 certifiedEndpointPair_radicands_pos.1

private theorem endpointMixedAuxiliaryDistance_pos :
    0 < endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2 := by
  rw [endpointMixedAuxiliaryDistance]
  apply Real.sqrt_pos.2
  rw [endpointSecondDistance, cStar_eq_certifiedEndpointPair_fst]
  exact certifiedEndpointPair_radicands_pos.2

/-- The quartic coordinate expression before choosing the lower Gram branch. -/
def weightedSelfCoordinateExpression (r b t y upper : ℝ) : ℝ :=
  let c := cStar
  let B := certifiedEndpointPair.2
  let D := endpointSecondDistance c B
  let A := endpointFirstAuxiliaryDistance B
  let C := endpointMixedAuxiliaryDistance c B
  let k := chordInnerProduct c r b
  let z := (k * t - y) / r
  let qB := 1 + 4 * r ^ 2 - 4 * r * t
  let qD := 1 + 4 * b ^ 2 - 4 * z
  let qA := 1 + r ^ 2 - 2 * r * t
  let qC := 1 + r ^ 2 + b ^ 2 - 2 * r * t - 2 * z + 2 * k
  quarticNormTangent (1 + endpointLambda) B 3 qB +
    quarticNormTangent 1 D (1 + 2 * upper) qD +
    quarticNormTangent endpointMu A 2 qA +
    quarticNormTangent endpointMu C (2 + upper) qC -
    weightedFirstPenalty c endpointLambda endpointMu * r -
    weightedSecondPenalty c endpointLambda endpointMu * b -
    weightedConstantTerm c endpointLambda endpointMu

/-- The quartic coordinate majorant on a bin with upper second radius `upper`. -/
def weightedSelfCoordinateMajorant (r b t upper : ℝ) : ℝ :=
  weightedSelfCoordinateExpression r b t
    (Real.sqrt (chordProjectionRadicand cStar r b t)) upper

/-- The constant coefficient after reducing the squared Gram ordinate. -/
def weightedSelfPolynomialP (r b t upper : ℝ) : ℝ :=
  let value := fun y ↦ r ^ 2 * weightedSelfCoordinateExpression r b t y upper
  value 0 + ((value 1 + value (-1)) / 2 - value 0) *
    chordProjectionRadicand cStar r b t

/-- The linear coefficient after reducing the squared Gram ordinate. -/
def weightedSelfPolynomialQ (r b t upper : ℝ) : ℝ :=
  let value := fun y ↦ r ^ 2 * weightedSelfCoordinateExpression r b t y upper
  (value 1 - value (-1)) / 2

/-- The discriminant controlling the reduced Gram branch. -/
def weightedSelfDiscriminant (r b t upper : ℝ) : ℝ :=
  weightedSelfPolynomialP r b t upper ^ 2 -
    weightedSelfPolynomialQ r b t upper ^ 2 * chordProjectionRadicand cStar r b t

/-- The coordinate expression is linear after reducing the squared Gram ordinate. -/
theorem weightedSelfCoordinateExpression_reduction (r b t y upper : ℝ)
    (hy : y ^ 2 = chordProjectionRadicand cStar r b t) :
    r ^ 2 * weightedSelfCoordinateExpression r b t y upper =
      weightedSelfPolynomialP r b t upper + weightedSelfPolynomialQ r b t upper * y := by
  simp only [weightedSelfPolynomialP, weightedSelfPolynomialQ]
  simp only [weightedSelfCoordinateExpression, quarticNormTangent]
  rw [← hy]
  ring

/-- The Gram radicand is nonnegative throughout the feasible scalar region. -/
theorem chordProjectionRadicand_nonneg_of_bounds {r b t : ℝ}
    (hr : cStar - b ≤ r) (hrUpper : r ≤ 1) (hbUpper : b ≤ 1)
    (htLower : -1 ≤ t) (htUpper : t ≤ 1) :
    0 ≤ chordProjectionRadicand cStar r b t := by
  have hc := one_lt_cStar_and_cStar_lt_two.1
  have hrZero : 0 ≤ r := by linarith
  have hbZero : 0 ≤ b := by linarith
  have hsum : cStar ≤ r + b := by linarith
  have hsumSq : cStar ^ 2 ≤ (r + b) ^ 2 :=
    (sq_le_sq₀ cStar_pos.le (add_nonneg hrZero hbZero)).2 hsum
  have hdiffLower : -cStar ≤ r - b := by linarith
  have hdiffUpper : r - b ≤ cStar := by linarith
  have hdiffSq : (r - b) ^ 2 ≤ cStar ^ 2 := by nlinarith
  have hkLower : -(r * b) ≤ chordInnerProduct cStar r b := by
    rw [chordInnerProduct]
    nlinarith
  have hkUpper : chordInnerProduct cStar r b ≤ r * b := by
    rw [chordInnerProduct]
    nlinarith
  have hkSq : chordInnerProduct cStar r b ^ 2 ≤ (r * b) ^ 2 := by
    have hminus : 0 ≤ r * b - chordInnerProduct cStar r b := sub_nonneg.mpr hkUpper
    have hplus : 0 ≤ r * b + chordInnerProduct cStar r b := by linarith
    have hproduct := mul_nonneg hminus hplus
    nlinarith
  have htSq : t ^ 2 ≤ 1 := by nlinarith
  rw [chordProjectionRadicand]
  have hfirst : 0 ≤ 1 - t ^ 2 := sub_nonneg.mpr htSq
  have hsecond : 0 ≤ r ^ 2 * b ^ 2 - chordInnerProduct cStar r b ^ 2 := by
    nlinarith
  positivity

/-- Signs of the reduced coefficients and discriminant imply the scalar majorant. -/
theorem weightedSelfCoordinateMajorant_nonpos_of_polynomial_signs
    {r b t upper : ℝ} (hr : 0 < r)
    (hR : 0 ≤ chordProjectionRadicand cStar r b t)
    (hP : weightedSelfPolynomialP r b t upper ≤ 0)
    (hQ : 0 ≤ weightedSelfPolynomialQ r b t upper)
    (hDelta : 0 ≤ weightedSelfDiscriminant r b t upper) :
    weightedSelfCoordinateMajorant r b t upper ≤ 0 := by
  let y := Real.sqrt (chordProjectionRadicand cStar r b t)
  have hyZero : 0 ≤ y := Real.sqrt_nonneg _
  have hySq : y ^ 2 = chordProjectionRadicand cStar r b t := Real.sq_sqrt hR
  have hQy : 0 ≤ weightedSelfPolynomialQ r b t upper * y := mul_nonneg hQ hyZero
  have hminusP : 0 ≤ -weightedSelfPolynomialP r b t upper := neg_nonneg.mpr hP
  have hsquares :
      (weightedSelfPolynomialQ r b t upper * y) ^ 2 ≤
        (-weightedSelfPolynomialP r b t upper) ^ 2 := by
    rw [weightedSelfDiscriminant] at hDelta
    nlinarith
  have hlinear := (sq_le_sq₀ hQy hminusP).1 hsquares
  have hreduction := weightedSelfCoordinateExpression_reduction r b t y upper hySq
  rw [weightedSelfCoordinateMajorant]
  change weightedSelfCoordinateExpression r b t y upper ≤ 0
  apply nonpos_of_mul_nonpos_right _ (sq_pos_of_pos hr)
  rw [hreduction]
  linarith

/-- The scalar weighted-self estimate on one interval of second radii. -/
def WeightedSelfRadiusBinBound (lower upper : ℝ) : Prop :=
  ∀ ⦃r b t : ℝ⦄,
    lower ≤ b → b ≤ upper → cStar - b ≤ r → r ≤ 1 → -1 ≤ t → t ≤ 1 →
      weightedSelfCoordinateMajorant r b t upper ≤ 0

theorem weightedPairScore_self_le_coordinateMajorant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e p q : E) (he : ‖e‖ = 1) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (hchord : ‖p - q‖ = cStar) {upper : ℝ} (hbUpper : ‖q‖ ≤ upper) :
    weightedPairScore e cStar endpointLambda endpointMu p q p q ≤
      weightedSelfCoordinateMajorant ‖p‖ ‖q‖ (⟪e, p⟫_ℝ / ‖p‖) upper := by
  let r := ‖p‖
  let b := ‖q‖
  let t := ⟪e, p⟫_ℝ / r
  let k := chordInnerProduct cStar r b
  let z := chordLowerProjection cStar r b t
  let qB := 1 + 4 * r ^ 2 - 4 * r * t
  let qD := 1 + 4 * b ^ 2 - 4 * z
  let qA := 1 + r ^ 2 - 2 * r * t
  let qC := 1 + r ^ 2 + b ^ 2 - 2 * r * t - 2 * z + 2 * k
  have hcoordinates := chord_coordinate_bounds e p q he one_lt_cStar_and_cStar_lt_two.1
    hp hq hchord
  have hcoordinateBounds :
      cStar - 1 ≤ r ∧ r ≤ 1 ∧ cStar - b ≤ r ∧ b ≤ 1 ∧ -1 ≤ t ∧ t ≤ 1 := by
    simpa [r, b, t] using hcoordinates
  have hrPos : 0 < r := by
    linarith [hcoordinateBounds.1, one_lt_cStar_and_cStar_lt_two.1]
  have hzBounds : -b ≤ z ∧ z ≤ ⟪e, q⟫_ℝ := by
    simpa [r, b, t, z] using
      chordLowerProjection_bounds e p q he (by simpa [r] using hrPos) hchord
  have hinner : ⟪e, p⟫_ℝ = r * t := by
    dsimp [t]
    field_simp [hrPos.ne']
  have hk : ⟪p, q⟫_ℝ = k := by
    have hchordSq := congrArg (fun x : ℝ ↦ x ^ 2) hchord
    rw [norm_sub_sq_real] at hchordSq
    dsimp [k, chordInnerProduct, r, b]
    nlinarith
  have hBsq : ‖e - p - p‖ ^ 2 = qB := by
    rw [show e - p - p = e - (p + p) by abel, norm_sub_sq_real, norm_add_sq_real]
    rw [he]
    simp only [one_pow, inner_add_right, real_inner_self_eq_norm_sq]
    dsimp [qB]
    rw [hinner]
    ring
  have hAsq : ‖e - p‖ ^ 2 = qA := by
    rw [norm_sub_sq_real, he]
    dsimp [qA]
    rw [hinner]
    ring
  have hDsq : ‖e - q - q‖ ^ 2 ≤ qD := by
    rw [show e - q - q = e - (q + q) by abel, norm_sub_sq_real, norm_add_sq_real]
    rw [he]
    simp only [one_pow, inner_add_right, real_inner_self_eq_norm_sq]
    dsimp [qD, b]
    nlinarith [hzBounds.2]
  have hCsq : ‖e - p - q‖ ^ 2 ≤ qC := by
    rw [show e - p - q = e - (p + q) by abel, norm_sub_sq_real, norm_add_sq_real]
    rw [he]
    simp only [one_pow, inner_add_right]
    dsimp [qC, r, b]
    rw [hinner, hk]
    nlinarith [hzBounds.2]
  have hqD : 0 ≤ qD := (sq_nonneg ‖e - q - q‖).trans hDsq
  have hqC : 0 ≤ qC := (sq_nonneg ‖e - p - q‖).trans hCsq
  have hBcap : ‖e - p - p‖ ≤ 3 := calc
    ‖e - p - p‖ ≤ ‖e - p‖ + ‖p‖ := norm_sub_le _ _
    _ ≤ (‖e‖ + ‖p‖) + ‖p‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (norm_sub_le e p) ‖p‖
    _ ≤ 3 := by rw [he]; linarith
  have hAcap : ‖e - p‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [he]; linarith)
  have hDcap : Real.sqrt qD ≤ 1 + 2 * upper := by
    have hsqrt : Real.sqrt qD ≤ 1 + 2 * b := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · dsimp [qD]
        nlinarith [hzBounds.1]
    dsimp [b] at hsqrt
    linarith
  have hkUpper : k ≤ r * b := by
    rw [← hk]
    exact real_inner_le_norm p q
  have hrtLower : -r ≤ r * t := by
    have := mul_nonneg (norm_nonneg p) (show 0 ≤ t + 1 by linarith)
    dsimp [r]
    nlinarith
  have hCcap : Real.sqrt qC ≤ 2 + upper := by
    have hsqrt : Real.sqrt qC ≤ 1 + r + b := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · dsimp [qC]
        nlinarith [hzBounds.1, hkUpper]
    dsimp [r, b] at hsqrt
    linarith [hcoordinateBounds.2.1]
  have hBtangent :
      (1 + endpointLambda) * ‖e - p - p‖ ≤
        quarticNormTangent (1 + endpointLambda) certifiedEndpointPair.2 3 qB := by
    have h := weighted_norm_tangent_with_remainder (e - p - p)
      (show 0 ≤ 1 + endpointLambda by linarith [endpointLambda_pos])
      (show 0 < certifiedEndpointPair.2 by
        linarith [certifiedEndpointPair_second_mem_isolation_box.1]) hBcap
    rw [hBsq] at h
    exact h
  have hDtangent :
      ‖e - q - q‖ ≤ quarticNormTangent 1
        (endpointSecondDistance cStar certifiedEndpointPair.2) (1 + 2 * upper) qD := by
    calc
      ‖e - q - q‖ ≤ Real.sqrt qD := Real.le_sqrt_of_sq_le hDsq
      _ = 1 * Real.sqrt qD := by ring
      _ ≤ _ := weighted_sqrt_le_quarticNormTangent (by norm_num)
        endpointSecondDistance_pos hqD hDcap
  have hAtangent :
      endpointMu * ‖e - p‖ ≤ quarticNormTangent endpointMu
        (endpointFirstAuxiliaryDistance certifiedEndpointPair.2) 2 qA := by
    have h := weighted_norm_tangent_with_remainder (e - p) endpointMu_pos.le
      endpointFirstAuxiliaryDistance_pos hAcap
    rw [hAsq] at h
    exact h
  have hCtangent :
      endpointMu * ‖e - p - q‖ ≤ quarticNormTangent endpointMu
        (endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2) (2 + upper) qC := by
    calc
      endpointMu * ‖e - p - q‖ ≤ endpointMu * Real.sqrt qC :=
        mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hCsq) endpointMu_pos.le
      _ ≤ _ := weighted_sqrt_le_quarticNormTangent endpointMu_pos.le
        endpointMixedAuxiliaryDistance_pos hqC hCcap
  calc
    weightedPairScore e cStar endpointLambda endpointMu p q p q =
        (1 + endpointLambda) * ‖e - p - p‖ + ‖e - q - q‖ +
          endpointMu * ‖e - p‖ + endpointMu * ‖e - p - q‖ -
          weightedFirstPenalty cStar endpointLambda endpointMu * r -
          weightedSecondPenalty cStar endpointLambda endpointMu * b -
          weightedConstantTerm cStar endpointLambda endpointMu := by
      simp only [weightedPairScore]
      dsimp [r, b]
      ring
    _ ≤ quarticNormTangent (1 + endpointLambda) certifiedEndpointPair.2 3 qB +
          quarticNormTangent 1 (endpointSecondDistance cStar certifiedEndpointPair.2)
            (1 + 2 * upper) qD +
          quarticNormTangent endpointMu
            (endpointFirstAuxiliaryDistance certifiedEndpointPair.2) 2 qA +
          quarticNormTangent endpointMu
            (endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2) (2 + upper) qC -
          weightedFirstPenalty cStar endpointLambda endpointMu * r -
          weightedSecondPenalty cStar endpointLambda endpointMu * b -
          weightedConstantTerm cStar endpointLambda endpointMu := by linarith
    _ = weightedSelfCoordinateMajorant ‖p‖ ‖q‖ (⟪e, p⟫_ℝ / ‖p‖) upper := by
      simp only [weightedSelfCoordinateMajorant]
      simp [weightedSelfCoordinateExpression, chordLowerProjection, r, b, t, k, z,
        qB, qD, qA, qC]

private theorem exists_weightedPairScore_self_chord_reduction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E) {c lambda mu : ℝ} {p₁ p₂ : E} (hc : 1 < c)
    (hp₁ : ‖p₁‖ ≤ 1) (hsep : c ≤ ‖p₁ - p₂‖) (hmu : 0 ≤ mu)
    (hpenalty : 2 + mu ≤ weightedSecondPenalty c lambda mu) :
    ∃ q : E, ‖p₁ - q‖ = c ∧ ‖q‖ ≤ ‖p₂‖ ∧
      weightedPairScore e c lambda mu p₁ p₂ p₁ p₂ ≤
        weightedPairScore e c lambda mu p₁ q p₁ q := by
  obtain ⟨a, ⟨ha_zero, ha_one⟩, ha⟩ :=
    exists_norm_sub_smul_eq (p := p₁) (q := p₂) (c := c) (hp₁.trans_lt hc) hsep
  refine ⟨a • p₂, ha, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha_zero]
    exact mul_le_of_le_one_left (norm_nonneg _) ha_one
  · exact (weightedPairScore_le_smul_second_left e c lambda mu p₁ p₂ p₁ p₂
      ha_zero ha_one hmu hpenalty).trans
      (weightedPairScore_le_smul_second_right e c lambda mu p₁ (a • p₂) p₁ p₂
        ha_zero ha_one hmu hpenalty)

/-- Seven scalar radius-bin estimates imply the weighted self inequality. -/
theorem weightedSelf_nonpos_of_radius_bin_bounds
    (h₀ : WeightedSelfRadiusBinBound (cStar - 1) (2 / 5))
    (h₁ : WeightedSelfRadiusBinBound (2 / 5) (1 / 2))
    (h₂ : WeightedSelfRadiusBinBound (1 / 2) (3 / 5))
    (h₃ : WeightedSelfRadiusBinBound (3 / 5) (7 / 10))
    (h₄ : WeightedSelfRadiusBinBound (7 / 10) (4 / 5))
    (h₅ : WeightedSelfRadiusBinBound (4 / 5) (9 / 10))
    (h₆ : WeightedSelfRadiusBinBound (9 / 10) 1)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e p₁ p₂ : E) (he : ‖e‖ = 1) (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1)
    (hsep : cStar ≤ ‖p₁ - p₂‖) :
    weightedPairScore e cStar endpointLambda endpointMu p₁ p₂ p₁ p₂ ≤ 0 := by
  obtain ⟨q, hchord, hqNorm, hscore⟩ :=
    exists_weightedPairScore_self_chord_reduction e one_lt_cStar_and_cStar_lt_two.1 hp₁ hsep
      endpointMu_pos.le endpoint_weight_reduction_margin
  have hq : ‖q‖ ≤ 1 := hqNorm.trans hp₂
  have hcoordinates := chord_coordinate_bounds e p₁ q he one_lt_cStar_and_cStar_lt_two.1
    hp₁ hq hchord
  have hbLower : cStar - 1 ≤ ‖q‖ := by
    linarith [hcoordinates.2.1, hcoordinates.2.2.1]
  have finish {lower upper : ℝ} (hbin : WeightedSelfRadiusBinBound lower upper)
      (hlower : lower ≤ ‖q‖) (hupper : ‖q‖ ≤ upper) :
      weightedPairScore e cStar endpointLambda endpointMu p₁ q p₁ q ≤ 0 := by
    refine (weightedPairScore_self_le_coordinateMajorant e p₁ q he hp₁ hq hchord hupper).trans
      (hbin hlower hupper ?_ hcoordinates.2.1 hcoordinates.2.2.2.2.1
        hcoordinates.2.2.2.2.2)
    exact hcoordinates.2.2.1
  apply hscore.trans
  by_cases hb₀ : ‖q‖ ≤ 2 / 5
  · exact finish h₀ hbLower hb₀
  by_cases hb₁ : ‖q‖ ≤ 1 / 2
  · exact finish h₁ (le_of_not_ge hb₀) hb₁
  by_cases hb₂ : ‖q‖ ≤ 3 / 5
  · exact finish h₂ (le_of_not_ge hb₁) hb₂
  by_cases hb₃ : ‖q‖ ≤ 7 / 10
  · exact finish h₃ (le_of_not_ge hb₂) hb₃
  by_cases hb₄ : ‖q‖ ≤ 4 / 5
  · exact finish h₄ (le_of_not_ge hb₃) hb₄
  by_cases hb₅ : ‖q‖ ≤ 9 / 10
  · exact finish h₅ (le_of_not_ge hb₄) hb₅
  · exact finish h₆ (le_of_not_ge hb₅) hq

end Bescovitch
