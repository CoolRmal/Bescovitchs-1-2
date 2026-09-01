/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.D4
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.RemainderSlack
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.LowerCurvature
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.UpperCurvature

/-!
# Bernstein sign checks for the quartic model
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_0 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_1 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_2 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_3 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_4 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_5 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_6 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_7 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_8 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_9 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_10 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_11 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_nonnegative_row_12 :
    bernsteinRowNonnegativeN 12 27720 d4PowerPayload 12 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_0 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_1 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_2 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_3 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_4 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_5 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_6 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_7 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_8 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_9 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_10 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_11 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_nonnegative_row_12 :
    bernsteinRowNonnegativeN 12 27720 remainderLinearSlackPowerPayload 12 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_0 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_1 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_2 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_3 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_4 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_5 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_6 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_7 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_8 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_9 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_10 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_11 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_nonnegative_row_12 :
    bernsteinRowNonnegativeN 12 27720 lowerCurvaturePowerPayload 12 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_0 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_1 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_2 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_3 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_4 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_5 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_6 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_7 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_8 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_9 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_10 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_11 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_nonnegative_row_12 :
    bernsteinRowNonnegativeN 12 27720 upperCurvaturePowerPayload 12 = true := by
  with_unfolding_all rfl

/-- Certified nonnegative Bernstein coefficients. -/
theorem d4_bernstein_nonnegative (i j : Fin 13) :
    0 ≤ bernsteinInteger 12 27720 d4PowerPayload i j := by
  fin_cases i
  · exact of_decide_eq_true d4_nonnegative_row_0 j
  · exact of_decide_eq_true d4_nonnegative_row_1 j
  · exact of_decide_eq_true d4_nonnegative_row_2 j
  · exact of_decide_eq_true d4_nonnegative_row_3 j
  · exact of_decide_eq_true d4_nonnegative_row_4 j
  · exact of_decide_eq_true d4_nonnegative_row_5 j
  · exact of_decide_eq_true d4_nonnegative_row_6 j
  · exact of_decide_eq_true d4_nonnegative_row_7 j
  · exact of_decide_eq_true d4_nonnegative_row_8 j
  · exact of_decide_eq_true d4_nonnegative_row_9 j
  · exact of_decide_eq_true d4_nonnegative_row_10 j
  · exact of_decide_eq_true d4_nonnegative_row_11 j
  · exact of_decide_eq_true d4_nonnegative_row_12 j

/-- Certified nonnegative Bernstein coefficients. -/
theorem remainder_linear_slack_bernstein_nonnegative (i j : Fin 13) :
    0 ≤ bernsteinInteger 12 27720 remainderLinearSlackPowerPayload i j := by
  fin_cases i
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_0 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_1 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_2 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_3 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_4 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_5 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_6 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_7 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_8 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_9 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_10 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_11 j
  · exact of_decide_eq_true remainder_linear_slack_nonnegative_row_12 j

/-- Certified nonnegative Bernstein coefficients. -/
theorem lower_curvature_bernstein_nonnegative (i j : Fin 13) :
    0 ≤ bernsteinInteger 12 27720 lowerCurvaturePowerPayload i j := by
  fin_cases i
  · exact of_decide_eq_true lower_curvature_nonnegative_row_0 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_1 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_2 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_3 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_4 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_5 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_6 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_7 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_8 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_9 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_10 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_11 j
  · exact of_decide_eq_true lower_curvature_nonnegative_row_12 j

/-- Certified nonnegative Bernstein coefficients. -/
theorem upper_curvature_bernstein_nonnegative (i j : Fin 13) :
    0 ≤ bernsteinInteger 12 27720 upperCurvaturePowerPayload i j := by
  fin_cases i
  · exact of_decide_eq_true upper_curvature_nonnegative_row_0 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_1 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_2 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_3 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_4 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_5 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_6 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_7 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_8 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_9 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_10 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_11 j
  · exact of_decide_eq_true upper_curvature_nonnegative_row_12 j

end

end WeightedSelfTaylorBin4
end Bescovitch
