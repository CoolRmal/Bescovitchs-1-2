/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedReduction

/-!
# Crossed form of the weighted score

The mixed weighted score is the average of two crossed self-scores, less the convexity losses
from averaging the corresponding endpoint vectors.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- The loss in the triangle inequality when two vectors are averaged. -/
def midpointLoss {E : Type*} [NormedAddCommGroup E] (x y : E) : ℝ :=
  (‖x‖ + ‖y‖ - ‖x + y‖) / 2

/-- The midpoint loss is nonnegative. -/
theorem midpointLoss_nonneg {E : Type*} [NormedAddCommGroup E] (x y : E) :
    0 ≤ midpointLoss x y := by
  rw [midpointLoss, div_nonneg_iff]
  exact Or.inl ⟨sub_nonneg.mpr (norm_add_le x y), by norm_num⟩

/-- The norm of an average is the average norm minus its midpoint loss. -/
theorem norm_average_eq_average_norm_sub_midpointLoss
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) :
    ‖(1 / 2 : ℝ) • (x + y)‖ = (‖x‖ + ‖y‖) / 2 - midpointLoss x y := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    midpointLoss]
  ring

/-- The mixed score is an average of crossed self-scores minus two midpoint losses. -/
theorem weightedPairScore_eq_crossed_self_average_sub_midpointLosses
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E) (c lambda mu : ℝ) (p₁ p₂ w₁ w₂ : E) :
    weightedPairScore e c lambda mu p₁ p₂ w₁ w₂ =
      (weightedPairScore e c lambda mu p₁ w₂ p₁ w₂ +
        weightedPairScore e c lambda mu w₁ p₂ w₁ p₂) / 2 -
      (1 + lambda) * midpointLoss (e - 2 • p₁) (e - 2 • w₁) -
      midpointLoss (e - 2 • p₂) (e - 2 • w₂) := by
  have hfirst :
      ‖e - p₁ - w₁‖ = (‖e - 2 • p₁‖ + ‖e - 2 • w₁‖) / 2 -
        midpointLoss (e - 2 • p₁) (e - 2 • w₁) := by
    rw [← norm_average_eq_average_norm_sub_midpointLoss]
    congr 1
    module
  have hsecond :
      ‖e - p₂ - w₂‖ = (‖e - 2 • p₂‖ + ‖e - 2 • w₂‖) / 2 -
        midpointLoss (e - 2 • p₂) (e - 2 • w₂) := by
    rw [← norm_average_eq_average_norm_sub_midpointLoss]
    congr 1
    module
  rw [weightedPairScore, weightedPairScore, weightedPairScore, hfirst, hsecond]
  rw [show e - p₁ - p₁ = e - 2 • p₁ by module,
    show e - p₂ - p₂ = e - 2 • p₂ by module,
    show e - w₁ - w₁ = e - 2 • w₁ by module,
    show e - w₂ - w₂ = e - 2 • w₂ by module]
  ring

/-- Long crossed chords reduce the mixed inequality to two self inequalities. -/
theorem weightedPairScore_nonpos_of_crossed_self_nonpos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E) {c lambda mu : ℝ} {p₁ p₂ w₁ w₂ : E}
    (hlambda : -1 ≤ lambda)
    (hleft : weightedPairScore e c lambda mu p₁ w₂ p₁ w₂ ≤ 0)
    (hright : weightedPairScore e c lambda mu w₁ p₂ w₁ p₂ ≤ 0) :
    weightedPairScore e c lambda mu p₁ p₂ w₁ w₂ ≤ 0 := by
  rw [weightedPairScore_eq_crossed_self_average_sub_midpointLosses]
  have hfirst := midpointLoss_nonneg (e - 2 • p₁) (e - 2 • w₁)
  have hsecond := midpointLoss_nonneg (e - 2 • p₂) (e - 2 • w₂)
  have hcoefficient : 0 ≤ 1 + lambda := by linarith
  nlinarith [mul_nonneg hcoefficient hfirst]

end Bescovitch
