/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.CenterValue
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.CenterSlope
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.LowerCurvature

/-!
# Factor checks for the quadratic model
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

set_option maxRecDepth 100000 in
/-- The exact denominator exponent of the stored center-value polynomial. -/
theorem center_value_actual_exponent : bin4CenterValue.exponent = 584 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_0 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_1 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_2 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_3 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_4 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_5 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_6 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_7 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_8 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_9 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_10 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_11 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_row_12 :
    rowEq13 bin4CenterValue.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload) 12 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_value_shape_check : matrixHasShape 13 bin4CenterValue.numerator = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
/-- The exact denominator exponent of the stored center-slope polynomial. -/
theorem center_slope_actual_exponent : bin4CenterSlope.exponent = 579 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_0 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_1 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_2 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_3 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_4 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_5 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_6 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_7 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_8 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_9 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_10 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_11 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_row_12 :
    rowEq13 bin4CenterSlope.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload) 12 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem center_slope_shape_check : matrixHasShape 13 bin4CenterSlope.numerator = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
/-- The exact denominator exponent of the stored lower-curvature polynomial. -/
theorem lower_curvature_actual_exponent : bin4LowerCurvature.exponent = 574 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_0 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_1 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_2 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_3 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_4 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_5 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_6 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_7 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_8 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_9 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_10 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_11 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_row_12 :
    rowEq13 bin4LowerCurvature.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload) 12 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem lower_curvature_shape_check :
    matrixHasShape 13 bin4LowerCurvature.numerator = true := by
  with_unfolding_all rfl

/-- Certified model-factor data. -/
theorem center_value_coefficients (i j : Fin 13) :
    (bin4CenterValue.numerator).coefficient i j =
      (IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload).coefficient i j := by
  fin_cases i
  · exact of_decide_eq_true center_value_row_0 j
  · exact of_decide_eq_true center_value_row_1 j
  · exact of_decide_eq_true center_value_row_2 j
  · exact of_decide_eq_true center_value_row_3 j
  · exact of_decide_eq_true center_value_row_4 j
  · exact of_decide_eq_true center_value_row_5 j
  · exact of_decide_eq_true center_value_row_6 j
  · exact of_decide_eq_true center_value_row_7 j
  · exact of_decide_eq_true center_value_row_8 j
  · exact of_decide_eq_true center_value_row_9 j
  · exact of_decide_eq_true center_value_row_10 j
  · exact of_decide_eq_true center_value_row_11 j
  · exact of_decide_eq_true center_value_row_12 j

/-- Certified model-factor data. -/
theorem center_value_row_shape :
    (bin4CenterValue.numerator).length = 13 ∧
      ∀ row ∈ (bin4CenterValue.numerator), row.length = 13 :=
  of_decide_eq_true center_value_shape_check

/-- Certified model-factor data. -/
theorem center_slope_coefficients (i j : Fin 13) :
    (bin4CenterSlope.numerator).coefficient i j =
      (IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload).coefficient i j := by
  fin_cases i
  · exact of_decide_eq_true center_slope_row_0 j
  · exact of_decide_eq_true center_slope_row_1 j
  · exact of_decide_eq_true center_slope_row_2 j
  · exact of_decide_eq_true center_slope_row_3 j
  · exact of_decide_eq_true center_slope_row_4 j
  · exact of_decide_eq_true center_slope_row_5 j
  · exact of_decide_eq_true center_slope_row_6 j
  · exact of_decide_eq_true center_slope_row_7 j
  · exact of_decide_eq_true center_slope_row_8 j
  · exact of_decide_eq_true center_slope_row_9 j
  · exact of_decide_eq_true center_slope_row_10 j
  · exact of_decide_eq_true center_slope_row_11 j
  · exact of_decide_eq_true center_slope_row_12 j

/-- Certified model-factor data. -/
theorem center_slope_row_shape :
    (bin4CenterSlope.numerator).length = 13 ∧
      ∀ row ∈ (bin4CenterSlope.numerator), row.length = 13 :=
  of_decide_eq_true center_slope_shape_check

/-- Certified model-factor data. -/
theorem lower_curvature_coefficients (i j : Fin 13) :
    (bin4LowerCurvature.numerator).coefficient i j =
      (IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload).coefficient i j := by
  fin_cases i
  · exact of_decide_eq_true lower_curvature_row_0 j
  · exact of_decide_eq_true lower_curvature_row_1 j
  · exact of_decide_eq_true lower_curvature_row_2 j
  · exact of_decide_eq_true lower_curvature_row_3 j
  · exact of_decide_eq_true lower_curvature_row_4 j
  · exact of_decide_eq_true lower_curvature_row_5 j
  · exact of_decide_eq_true lower_curvature_row_6 j
  · exact of_decide_eq_true lower_curvature_row_7 j
  · exact of_decide_eq_true lower_curvature_row_8 j
  · exact of_decide_eq_true lower_curvature_row_9 j
  · exact of_decide_eq_true lower_curvature_row_10 j
  · exact of_decide_eq_true lower_curvature_row_11 j
  · exact of_decide_eq_true lower_curvature_row_12 j

/-- Certified model-factor data. -/
theorem lower_curvature_row_shape :
    (bin4LowerCurvature.numerator).length = 13 ∧
      ∀ row ∈ (bin4LowerCurvature.numerator), row.length = 13 :=
  of_decide_eq_true lower_curvature_shape_check

end

end WeightedSelfTaylorBin4
end Bescovitch
