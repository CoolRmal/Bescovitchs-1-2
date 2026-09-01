/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.RationalChord
public import Bescovitch.SixPoint.WeightedCertificateBridge

/-!
# Quadratic majorant for the mixed weighted score

Dropping the nonpositive quartic remainder from each norm tangent gives the rational polynomial
majorant used by the adaptive mixed-score certificate.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- The elementary quadratic tangent to a weighted square root. -/
def quadraticNormTangent (weight target squaredDistance : ℝ) : ℝ :=
  weight / (2 * target) * squaredDistance + weight * target / 2

/-- Removing the quartic correction can only increase a nonnegative weighted tangent. -/
theorem quarticNormTangent_le_quadraticNormTangent {weight target cap q : ℝ}
    (hweight : 0 ≤ weight) (htarget : 0 < target) (hcap : 0 ≤ cap) :
    quarticNormTangent weight target cap q ≤ quadraticNormTangent weight target q := by
  have hden : 0 < 2 * target * (cap + target) ^ 2 := by positivity
  have hcorrection : 0 ≤ weight / (2 * target * (cap + target) ^ 2) *
      (q - target ^ 2) ^ 2 := mul_nonneg (div_nonneg hweight hden.le) (sq_nonneg _)
  rw [quarticNormTangent, quadraticNormTangent]
  nlinarith

/-- The mixed-score tangent majorant after all six quartic corrections are discarded. -/
def weightedPairScoreQuadraticMajorant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (c lambda mu : ℝ) (p₁ p₂ w₁ w₂ : E)
    (rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ : ℝ)
    (uP₁ uW₁ uP₂ uW₂ : E) (etaP₁ etaP₂ etaW₁ etaW₂ : ℝ) : ℝ :=
  quadraticNormTangent (mu / 2) rhoP (‖e - p₁‖ ^ 2) +
    quadraticNormTangent (mu / 2) rhoW (‖e - w₁‖ ^ 2) +
    quadraticNormTangent (1 + lambda) rho₁₁ (‖e - p₁ - w₁‖ ^ 2) +
    quadraticNormTangent 1 rho₂₂ (‖e - p₂ - w₂‖ ^ 2) +
    quadraticNormTangent (mu / 2) rho₁₂ (‖e - p₁ - w₂‖ ^ 2) +
    quadraticNormTangent (mu / 2) rho₂₁ (‖e - w₁ - p₂‖ ^ 2) -
    weightedFirstPenalty c lambda mu / 2 *
      (quadraticNormSupport uP₁ p₁ + quadraticNormSupport uW₁ w₁) -
    weightedSecondPenalty c lambda mu / 2 *
      (quadraticNormSupport uP₂ p₂ + quadraticNormSupport uW₂ w₂) -
    weightedConstantTerm c lambda mu +
    etaP₁ * (1 - ‖p₁‖ ^ 2) + etaP₂ * (1 - ‖p₂‖ ^ 2) +
    etaW₁ * (1 - ‖w₁‖ ^ 2) + etaW₂ * (1 - ‖w₂‖ ^ 2)

/-- The quartic mixed majorant is bounded by its quadratic relaxation. -/
theorem weightedPairScoreTangentMajorant_le_quadraticMajorant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (c lambda mu : ℝ) (p₁ p₂ w₁ w₂ : E)
    (rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ : ℝ)
    (uP₁ uW₁ uP₂ uW₂ : E) (etaP₁ etaP₂ etaW₁ etaW₂ : ℝ)
    (hmu : 0 ≤ mu) (hlambda : 0 ≤ 1 + lambda)
    (hrhoP : 0 < rhoP) (hrhoW : 0 < rhoW) (hrho₁₁ : 0 < rho₁₁)
    (hrho₂₂ : 0 < rho₂₂) (hrho₁₂ : 0 < rho₁₂) (hrho₂₁ : 0 < rho₂₁) :
    weightedPairScoreTangentMajorant e c lambda mu p₁ p₂ w₁ w₂
        rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
        etaP₁ etaP₂ etaW₁ etaW₂ ≤
      weightedPairScoreQuadraticMajorant e c lambda mu p₁ p₂ w₁ w₂
        rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
        etaP₁ etaP₂ etaW₁ etaW₂ := by
  have hP := quarticNormTangent_le_quadraticNormTangent
    (weight := mu / 2) (target := rhoP) (q := ‖e - p₁‖ ^ 2) (cap := 2)
    (div_nonneg hmu (by norm_num)) hrhoP (by norm_num)
  have hW := quarticNormTangent_le_quadraticNormTangent
    (weight := mu / 2) (target := rhoW) (q := ‖e - w₁‖ ^ 2) (cap := 2)
    (div_nonneg hmu (by norm_num)) hrhoW (by norm_num)
  have h₁₁ := quarticNormTangent_le_quadraticNormTangent
    (weight := 1 + lambda) (target := rho₁₁) (q := ‖e - p₁ - w₁‖ ^ 2) (cap := 3)
    hlambda hrho₁₁ (by norm_num)
  have h₂₂ := quarticNormTangent_le_quadraticNormTangent
    (weight := 1) (target := rho₂₂) (q := ‖e - p₂ - w₂‖ ^ 2) (cap := 3)
    (by norm_num) hrho₂₂ (by norm_num)
  have h₁₂ := quarticNormTangent_le_quadraticNormTangent
    (weight := mu / 2) (target := rho₁₂) (q := ‖e - p₁ - w₂‖ ^ 2) (cap := 3)
    (div_nonneg hmu (by norm_num)) hrho₁₂ (by norm_num)
  have h₂₁ := quarticNormTangent_le_quadraticNormTangent
    (weight := mu / 2) (target := rho₂₁) (q := ‖e - w₁ - p₂‖ ^ 2) (cap := 3)
    (div_nonneg hmu (by norm_num)) hrho₂₁ (by norm_num)
  rw [weightedPairScoreTangentMajorant, weightedPairScoreQuadraticMajorant]
  linarith

/-- The rational quadratic majorant on one lens chart. -/
def weightedLensQuadraticCertificateMajorant
    (sideP zP aP hP sideW zW aW hW : ℝ)
    (rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ : ℝ)
    (uP₁ uW₁ uP₂ uW₂ : (EuclideanSpace ℝ (Fin 2)))
    (etaP₁ etaP₂ etaW₁ etaW₂ : ℝ) : ℝ :=
  weightedPairScoreQuadraticMajorant !₂[1, 0]
    certificateChord certificateLambda certificateMu
    (chordChartFirst sideP aP hP zP)
    (chordChartSecond sideP certificateChord aP hP zP)
    (chordChartFirst sideW aW hW zW)
    (chordChartSecond sideW certificateChord aW hW zW)
    rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
    etaP₁ etaP₂ etaW₁ etaW₂ + 1 / 10 ^ 8

/-- The geometric certificate majorant is bounded by its rational quadratic relaxation. -/
theorem weightedLensCertificateMajorant_le_quadraticMajorant
    (sideP zP aP hP sideW zW aW hW : ℝ)
    (rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ : ℝ)
    (uP₁ uW₁ uP₂ uW₂ : (EuclideanSpace ℝ (Fin 2))) (etaP₁ etaP₂ etaW₁ etaW₂ : ℝ)
    (hrhoP : 0 < rhoP) (hrhoW : 0 < rhoW) (hrho₁₁ : 0 < rho₁₁)
    (hrho₂₂ : 0 < rho₂₂) (hrho₁₂ : 0 < rho₁₂) (hrho₂₁ : 0 < rho₂₁) :
    weightedLensCertificateMajorant sideP zP aP hP sideW zW aW hW
        rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
        etaP₁ etaP₂ etaW₁ etaW₂ ≤
      weightedLensQuadraticCertificateMajorant sideP zP aP hP sideW zW aW hW
        rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
        etaP₁ etaP₂ etaW₁ etaW₂ := by
  rw [weightedLensCertificateMajorant, weightedLensQuadraticCertificateMajorant]
  have h := weightedPairScoreTangentMajorant_le_quadraticMajorant !₂[1, 0]
    certificateChord certificateLambda certificateMu
    (chordChartFirst sideP aP hP zP)
    (chordChartSecond sideP certificateChord aP hP zP)
    (chordChartFirst sideW aW hW zW)
    (chordChartSecond sideW certificateChord aW hW zW)
    rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
    etaP₁ etaP₂ etaW₁ etaW₂
    certificateMu_nonneg (by norm_num [certificateLambda])
    hrhoP hrhoW hrho₁₁ hrho₂₂ hrho₁₂ hrho₂₁
  simpa only [add_comm] using add_le_add_right h (1 / 10 ^ 8)

/-- The rational quadratic certificate directly bounds the exact endpoint score. -/
theorem weightedPairScore_le_lensQuadraticCertificateMajorant
    (sideP zP aP hP sideW zW aW hW : ℝ)
    (rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ : ℝ)
    (uP₁ uW₁ uP₂ uW₂ : (EuclideanSpace ℝ (Fin 2))) (etaP₁ etaP₂ etaW₁ etaW₂ : ℝ)
    (hsideP : sideP ^ 2 = 1) (hsideW : sideW ^ 2 = 1)
    (hPFirst : aP ^ 2 + hP ^ 2 ≤ 1) (hPSecond : (aP - barC) ^ 2 + hP ^ 2 ≤ 1)
    (hWFirst : aW ^ 2 + hW ^ 2 ≤ 1) (hWSecond : (aW - barC) ^ 2 + hW ^ 2 ≤ 1)
    (hrhoP : 0 < rhoP) (hrhoW : 0 < rhoW) (hrho₁₁ : 0 < rho₁₁)
    (hrho₂₂ : 0 < rho₂₂) (hrho₁₂ : 0 < rho₁₂) (hrho₂₁ : 0 < rho₂₁)
    (huP₁ : ‖uP₁‖ ≤ 1) (huW₁ : ‖uW₁‖ ≤ 1)
    (huP₂ : ‖uP₂‖ ≤ 1) (huW₂ : ‖uW₂‖ ≤ 1)
    (hetaP₁ : 0 ≤ etaP₁) (hetaP₂ : 0 ≤ etaP₂)
    (hetaW₁ : 0 ≤ etaW₁) (hetaW₂ : 0 ≤ etaW₂) :
    weightedPairScore !₂[1, 0] barC endpointLambda endpointMu
        (chordChartFirst sideP aP hP zP) (chordChartSecond sideP barC aP hP zP)
        (chordChartFirst sideW aW hW zW) (chordChartSecond sideW barC aW hW zW) ≤
      weightedLensQuadraticCertificateMajorant sideP zP aP hP sideW zW aW hW
        rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
        etaP₁ etaP₂ etaW₁ etaW₂ := by
  exact (weightedPairScore_le_lensCertificateMajorant sideP zP aP hP sideW zW aW hW
    rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
    etaP₁ etaP₂ etaW₁ etaW₂
    hsideP hsideW hPFirst hPSecond hWFirst hWSecond hrhoP hrhoW hrho₁₁ hrho₂₂ hrho₁₂
    hrho₂₁ huP₁ huW₁ huP₂ huW₂ hetaP₁ hetaP₂ hetaW₁ hetaW₂).trans
      (weightedLensCertificateMajorant_le_quadraticMajorant sideP zP aP hP sideW zW aW hW
        rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
        etaP₁ etaP₂ etaW₁ etaW₂
        hrhoP hrhoW hrho₁₁ hrho₂₂ hrho₁₂ hrho₂₁)

end Bescovitch
