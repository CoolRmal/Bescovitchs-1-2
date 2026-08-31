/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelf
public import Bescovitch.SixPoint.WeightedTangent

/-!
# Polynomial majorant for the mixed weighted score

Six upper norm tangents and four lower norm supports turn the mixed score into a polynomial.
Nonnegative multiples of the four unit-disk slacks may then be added before certification.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Bescovitch

/-- The tangent majorant used by the exact mixed-score certificate. -/
def weightedPairScoreTangentMajorant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (c lambda mu : ℝ) (p₁ p₂ w₁ w₂ : E)
    (rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ : ℝ)
    (uP₁ uW₁ uP₂ uW₂ : E) (etaP₁ etaP₂ etaW₁ etaW₂ : ℝ) : ℝ :=
  quarticNormTangent (mu / 2) rhoP 2 (‖e - p₁‖ ^ 2) +
    quarticNormTangent (mu / 2) rhoW 2 (‖e - w₁‖ ^ 2) +
    quarticNormTangent (1 + lambda) rho₁₁ 3 (‖e - p₁ - w₁‖ ^ 2) +
    quarticNormTangent 1 rho₂₂ 3 (‖e - p₂ - w₂‖ ^ 2) +
    quarticNormTangent (mu / 2) rho₁₂ 3 (‖e - p₁ - w₂‖ ^ 2) +
    quarticNormTangent (mu / 2) rho₂₁ 3 (‖e - w₁ - p₂‖ ^ 2) -
    weightedFirstPenalty c lambda mu / 2 *
      (quadraticNormSupport uP₁ p₁ + quadraticNormSupport uW₁ w₁) -
    weightedSecondPenalty c lambda mu / 2 *
      (quadraticNormSupport uP₂ p₂ + quadraticNormSupport uW₂ w₂) -
    weightedConstantTerm c lambda mu +
    etaP₁ * (1 - ‖p₁‖ ^ 2) + etaP₂ * (1 - ‖p₂‖ ^ 2) +
    etaW₁ * (1 - ‖w₁‖ ^ 2) + etaW₂ * (1 - ‖w₂‖ ^ 2)

private theorem weighted_norm_le_quarticNormTangent
    {E : Type*} [NormedAddCommGroup E] (v : E) {weight target cap : ℝ}
    (hweight : 0 ≤ weight) (htarget : 0 < target) (hcap : ‖v‖ ≤ cap) :
    weight * ‖v‖ ≤ quarticNormTangent weight target cap (‖v‖ ^ 2) := by
  simpa only [quarticNormTangent] using
    mul_le_quadratic_tangent_sub_quartic (norm_nonneg v) hweight htarget hcap

private theorem unitDiskSlack_nonneg
    {E : Type*} [NormedAddCommGroup E] (v : E) (hv : ‖v‖ ≤ 1) :
    0 ≤ 1 - ‖v‖ ^ 2 := by
  apply sub_nonneg.mpr
  simpa only [one_pow] using
    (sq_le_sq₀ (norm_nonneg v) (by norm_num)).2 hv

/-- The tangent expression pointwise majorizes the mixed weighted score. -/
theorem weightedPairScore_le_tangentMajorant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (c lambda mu : ℝ) (p₁ p₂ w₁ w₂ : E)
    (rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ : ℝ)
    (uP₁ uW₁ uP₂ uW₂ : E) (etaP₁ etaP₂ etaW₁ etaW₂ : ℝ)
    (he : ‖e‖ ≤ 1) (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hmu : 0 ≤ mu) (hlambda : 0 ≤ 1 + lambda)
    (hfirstPenalty : 0 ≤ weightedFirstPenalty c lambda mu)
    (hsecondPenalty : 0 ≤ weightedSecondPenalty c lambda mu)
    (hrhoP : 0 < rhoP) (hrhoW : 0 < rhoW) (hrho₁₁ : 0 < rho₁₁)
    (hrho₂₂ : 0 < rho₂₂) (hrho₁₂ : 0 < rho₁₂) (hrho₂₁ : 0 < rho₂₁)
    (huP₁ : ‖uP₁‖ ≤ 1) (huW₁ : ‖uW₁‖ ≤ 1)
    (huP₂ : ‖uP₂‖ ≤ 1) (huW₂ : ‖uW₂‖ ≤ 1)
    (hetaP₁ : 0 ≤ etaP₁) (hetaP₂ : 0 ≤ etaP₂)
    (hetaW₁ : 0 ≤ etaW₁) (hetaW₂ : 0 ≤ etaW₂) :
    weightedPairScore e c lambda mu p₁ p₂ w₁ w₂ ≤
      weightedPairScoreTangentMajorant e c lambda mu p₁ p₂ w₁ w₂
        rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
        etaP₁ etaP₂ etaW₁ etaW₂ := by
  have heP₁ : ‖e - p₁‖ ≤ 2 := (norm_sub_le e p₁).trans (by linarith)
  have heW₁ : ‖e - w₁‖ ≤ 2 := (norm_sub_le e w₁).trans (by linarith)
  have heP₁W₁ : ‖e - p₁ - w₁‖ ≤ 3 :=
    (norm_sub_le (e - p₁) w₁).trans (by linarith [norm_sub_le e p₁])
  have heP₂W₂ : ‖e - p₂ - w₂‖ ≤ 3 :=
    (norm_sub_le (e - p₂) w₂).trans (by linarith [norm_sub_le e p₂])
  have heP₁W₂ : ‖e - p₁ - w₂‖ ≤ 3 :=
    (norm_sub_le (e - p₁) w₂).trans (by linarith [norm_sub_le e p₁])
  have heW₁P₂ : ‖e - w₁ - p₂‖ ≤ 3 :=
    (norm_sub_le (e - w₁) p₂).trans (by linarith [norm_sub_le e w₁])
  have hP := weighted_norm_le_quarticNormTangent (weight := mu / 2)
    (e - p₁) (by positivity) hrhoP heP₁
  have hW := weighted_norm_le_quarticNormTangent (weight := mu / 2)
    (e - w₁) (by positivity) hrhoW heW₁
  have h₁₁ := weighted_norm_le_quarticNormTangent (e - p₁ - w₁)
    hlambda hrho₁₁ heP₁W₁
  have h₂₂ := weighted_norm_le_quarticNormTangent (weight := 1) (e - p₂ - w₂)
    (by norm_num) hrho₂₂ heP₂W₂
  have h₁₂ := weighted_norm_le_quarticNormTangent (weight := mu / 2) (e - p₁ - w₂)
    (by positivity) hrho₁₂ heP₁W₂
  have h₂₁ := weighted_norm_le_quarticNormTangent (weight := mu / 2) (e - w₁ - p₂)
    (by positivity) hrho₂₁ heW₁P₂
  have hsP₁ := quadraticNormSupport_le_norm uP₁ p₁ huP₁ hp₁
  have hsW₁ := quadraticNormSupport_le_norm uW₁ w₁ huW₁ hw₁
  have hsP₂ := quadraticNormSupport_le_norm uP₂ p₂ huP₂ hp₂
  have hsW₂ := quadraticNormSupport_le_norm uW₂ w₂ huW₂ hw₂
  have hslackP₁ : 0 ≤ etaP₁ * (1 - ‖p₁‖ ^ 2) := by
    exact mul_nonneg hetaP₁ (unitDiskSlack_nonneg p₁ hp₁)
  have hslackP₂ : 0 ≤ etaP₂ * (1 - ‖p₂‖ ^ 2) := by
    exact mul_nonneg hetaP₂ (unitDiskSlack_nonneg p₂ hp₂)
  have hslackW₁ : 0 ≤ etaW₁ * (1 - ‖w₁‖ ^ 2) := by
    exact mul_nonneg hetaW₁ (unitDiskSlack_nonneg w₁ hw₁)
  have hslackW₂ : 0 ≤ etaW₂ * (1 - ‖w₂‖ ^ 2) := by
    exact mul_nonneg hetaW₂ (unitDiskSlack_nonneg w₂ hw₂)
  have hradialFirst :
      -(weightedFirstPenalty c lambda mu / 2 * (‖p₁‖ + ‖w₁‖)) ≤
        -(weightedFirstPenalty c lambda mu / 2 *
          (quadraticNormSupport uP₁ p₁ + quadraticNormSupport uW₁ w₁)) := by
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left (add_le_add hsP₁ hsW₁)
      (div_nonneg hfirstPenalty (by norm_num))
  have hradialSecond :
      -(weightedSecondPenalty c lambda mu / 2 * (‖p₂‖ + ‖w₂‖)) ≤
        -(weightedSecondPenalty c lambda mu / 2 *
          (quadraticNormSupport uP₂ p₂ + quadraticNormSupport uW₂ w₂)) := by
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left (add_le_add hsP₂ hsW₂)
      (div_nonneg hsecondPenalty (by norm_num))
  rw [weightedPairScore, weightedPairScoreTangentMajorant]
  linarith

end Bescovitch
