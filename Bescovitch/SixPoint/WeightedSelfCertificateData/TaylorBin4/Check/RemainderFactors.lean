/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.D4
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.RemainderSlack
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.UpperCurvature

/-!
# Factor checks for the quartic remainder
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

set_option maxRecDepth 100000 in
/-- The exact denominator exponent of the stored quartic coefficient. -/
theorem d4_actual_exponent : bin4D4.exponent = 564 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_0 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_1 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_2 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_3 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_4 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_5 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_6 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_7 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_8 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_9 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_10 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_11 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_row_12 :
    rowEq13 bin4D4.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload) 12 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem d4_shape_check : matrixHasShape 13 bin4D4.numerator = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
/-- The exact denominator exponent of the stored affine remainder slack. -/
theorem remainder_linear_slack_actual_exponent : bin4RemainderLinearSlack.exponent = 568 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_0 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_1 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_2 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_3 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_4 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_5 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_6 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_7 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_8 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_9 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_10 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_11 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_row_12 :
    rowEq13 bin4RemainderLinearSlack.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135) remainderLinearSlackPowerPayload) 12 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem remainder_linear_slack_shape_check :
    matrixHasShape 13 bin4RemainderLinearSlack.numerator = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
/-- The exact denominator exponent of the stored upper-curvature slack. -/
theorem upper_curvature_actual_exponent : bin4UpperCurvature.exponent = 574 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_0 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_1 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_2 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_3 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_4 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_5 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_6 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_7 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_8 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_9 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_10 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_11 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_row_12 :
    rowEq13 bin4UpperCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload) 12 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem upper_curvature_shape_check :
    matrixHasShape 13 bin4UpperCurvature.numerator = true := by
  with_unfolding_all rfl

/-- Certified remainder-factor data. -/
theorem d4_coefficients (i j : Fin 13) :
    (bin4D4.numerator).coefficient i j =
      (IntBivariate.scaleInt ((2 : ℤ) ^ 172) d4PowerPayload).coefficient i j := by
  fin_cases i
  · exact of_decide_eq_true d4_row_0 j
  · exact of_decide_eq_true d4_row_1 j
  · exact of_decide_eq_true d4_row_2 j
  · exact of_decide_eq_true d4_row_3 j
  · exact of_decide_eq_true d4_row_4 j
  · exact of_decide_eq_true d4_row_5 j
  · exact of_decide_eq_true d4_row_6 j
  · exact of_decide_eq_true d4_row_7 j
  · exact of_decide_eq_true d4_row_8 j
  · exact of_decide_eq_true d4_row_9 j
  · exact of_decide_eq_true d4_row_10 j
  · exact of_decide_eq_true d4_row_11 j
  · exact of_decide_eq_true d4_row_12 j

/-- Certified remainder-factor data. -/
theorem d4_row_shape :
    (bin4D4.numerator).length = 13 ∧ ∀ row ∈ (bin4D4.numerator), row.length = 13 :=
  of_decide_eq_true d4_shape_check

/-- Certified remainder-factor data. -/
theorem remainder_linear_slack_coefficients (i j : Fin 13) :
    (bin4RemainderLinearSlack.numerator).coefficient i j =
      (IntBivariate.scaleInt ((2 : ℤ) ^ 135)
        remainderLinearSlackPowerPayload).coefficient i j := by
  fin_cases i
  · exact of_decide_eq_true remainder_linear_slack_row_0 j
  · exact of_decide_eq_true remainder_linear_slack_row_1 j
  · exact of_decide_eq_true remainder_linear_slack_row_2 j
  · exact of_decide_eq_true remainder_linear_slack_row_3 j
  · exact of_decide_eq_true remainder_linear_slack_row_4 j
  · exact of_decide_eq_true remainder_linear_slack_row_5 j
  · exact of_decide_eq_true remainder_linear_slack_row_6 j
  · exact of_decide_eq_true remainder_linear_slack_row_7 j
  · exact of_decide_eq_true remainder_linear_slack_row_8 j
  · exact of_decide_eq_true remainder_linear_slack_row_9 j
  · exact of_decide_eq_true remainder_linear_slack_row_10 j
  · exact of_decide_eq_true remainder_linear_slack_row_11 j
  · exact of_decide_eq_true remainder_linear_slack_row_12 j

/-- Certified remainder-factor data. -/
theorem remainder_linear_slack_row_shape :
    (bin4RemainderLinearSlack.numerator).length = 13 ∧
      ∀ row ∈ (bin4RemainderLinearSlack.numerator), row.length = 13 :=
  of_decide_eq_true remainder_linear_slack_shape_check

/-- Certified remainder-factor data. -/
theorem upper_curvature_coefficients (i j : Fin 13) :
    (bin4UpperCurvature.numerator).coefficient i j =
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) upperCurvaturePowerPayload).coefficient i j := by
  fin_cases i
  · exact of_decide_eq_true upper_curvature_row_0 j
  · exact of_decide_eq_true upper_curvature_row_1 j
  · exact of_decide_eq_true upper_curvature_row_2 j
  · exact of_decide_eq_true upper_curvature_row_3 j
  · exact of_decide_eq_true upper_curvature_row_4 j
  · exact of_decide_eq_true upper_curvature_row_5 j
  · exact of_decide_eq_true upper_curvature_row_6 j
  · exact of_decide_eq_true upper_curvature_row_7 j
  · exact of_decide_eq_true upper_curvature_row_8 j
  · exact of_decide_eq_true upper_curvature_row_9 j
  · exact of_decide_eq_true upper_curvature_row_10 j
  · exact of_decide_eq_true upper_curvature_row_11 j
  · exact of_decide_eq_true upper_curvature_row_12 j

/-- Certified remainder-factor data. -/
theorem upper_curvature_row_shape :
    bin4UpperCurvature.numerator.length = 13 ∧
      ∀ row ∈ bin4UpperCurvature.numerator, row.length = 13 :=
  of_decide_eq_true upper_curvature_shape_check

end

end WeightedSelfTaylorBin4
end Bescovitch
