/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.NegativeP

/-!
# Checks for the three negative-P Bernstein factors
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

set_option maxRecDepth 100000 in
/-- The exact denominator exponent of the left negative-`P` margin polynomial. -/
theorem negative_p_left_actual_exponent :
    bin4NegativePLeftMargin.exponent = 282 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_row_0 :
    rowEqN 7 bin4NegativePLeftMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePLeftMarginPayload) 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_row_1 :
    rowEqN 7 bin4NegativePLeftMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePLeftMarginPayload) 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_row_2 :
    rowEqN 7 bin4NegativePLeftMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePLeftMarginPayload) 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_row_3 :
    rowEqN 7 bin4NegativePLeftMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePLeftMarginPayload) 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_row_4 :
    rowEqN 7 bin4NegativePLeftMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePLeftMarginPayload) 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_row_5 :
    rowEqN 7 bin4NegativePLeftMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePLeftMarginPayload) 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_row_6 :
    rowEqN 7 bin4NegativePLeftMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePLeftMarginPayload) 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
private theorem negative_p_left_shape_check :
    matrixHasShape 7 bin4NegativePLeftMargin.numerator = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
/-- The exact denominator exponent of the middle negative-`P` margin polynomial. -/
theorem negative_p_middle_actual_exponent :
    bin4NegativePMiddleMargin.exponent = 283 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_row_0 :
    rowEqN 7 bin4NegativePMiddleMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 5) negativePMiddleMarginPayload) 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_row_1 :
    rowEqN 7 bin4NegativePMiddleMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 5) negativePMiddleMarginPayload) 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_row_2 :
    rowEqN 7 bin4NegativePMiddleMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 5) negativePMiddleMarginPayload) 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_row_3 :
    rowEqN 7 bin4NegativePMiddleMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 5) negativePMiddleMarginPayload) 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_row_4 :
    rowEqN 7 bin4NegativePMiddleMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 5) negativePMiddleMarginPayload) 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_row_5 :
    rowEqN 7 bin4NegativePMiddleMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 5) negativePMiddleMarginPayload) 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_row_6 :
    rowEqN 7 bin4NegativePMiddleMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 5) negativePMiddleMarginPayload) 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
private theorem negative_p_middle_shape_check :
    matrixHasShape 7 bin4NegativePMiddleMargin.numerator = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
/-- The exact denominator exponent of the right negative-`P` margin polynomial. -/
theorem negative_p_right_actual_exponent :
    bin4NegativePRightMargin.exponent = 282 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_row_0 :
    rowEqN 7 bin4NegativePRightMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePRightMarginPayload) 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_row_1 :
    rowEqN 7 bin4NegativePRightMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePRightMarginPayload) 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_row_2 :
    rowEqN 7 bin4NegativePRightMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePRightMarginPayload) 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_row_3 :
    rowEqN 7 bin4NegativePRightMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePRightMarginPayload) 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_row_4 :
    rowEqN 7 bin4NegativePRightMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePRightMarginPayload) 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_row_5 :
    rowEqN 7 bin4NegativePRightMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePRightMarginPayload) 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_row_6 :
    rowEqN 7 bin4NegativePRightMargin.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePRightMarginPayload) 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
private theorem negative_p_right_shape_check :
    matrixHasShape 7 bin4NegativePRightMargin.numerator = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_nonnegative_row_0 :
    bernsteinRowNonnegativeN 6 60 negativePLeftMarginPayload 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_nonnegative_row_1 :
    bernsteinRowNonnegativeN 6 60 negativePLeftMarginPayload 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_nonnegative_row_2 :
    bernsteinRowNonnegativeN 6 60 negativePLeftMarginPayload 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_nonnegative_row_3 :
    bernsteinRowNonnegativeN 6 60 negativePLeftMarginPayload 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_nonnegative_row_4 :
    bernsteinRowNonnegativeN 6 60 negativePLeftMarginPayload 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_nonnegative_row_5 :
    bernsteinRowNonnegativeN 6 60 negativePLeftMarginPayload 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_left_nonnegative_row_6 :
    bernsteinRowNonnegativeN 6 60 negativePLeftMarginPayload 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_nonnegative_row_0 :
    bernsteinRowNonnegativeN 6 60 negativePMiddleMarginPayload 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_nonnegative_row_1 :
    bernsteinRowNonnegativeN 6 60 negativePMiddleMarginPayload 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_nonnegative_row_2 :
    bernsteinRowNonnegativeN 6 60 negativePMiddleMarginPayload 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_nonnegative_row_3 :
    bernsteinRowNonnegativeN 6 60 negativePMiddleMarginPayload 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_nonnegative_row_4 :
    bernsteinRowNonnegativeN 6 60 negativePMiddleMarginPayload 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_nonnegative_row_5 :
    bernsteinRowNonnegativeN 6 60 negativePMiddleMarginPayload 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_middle_nonnegative_row_6 :
    bernsteinRowNonnegativeN 6 60 negativePMiddleMarginPayload 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_nonnegative_row_0 :
    bernsteinRowNonnegativeN 6 60 negativePRightMarginPayload 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_nonnegative_row_1 :
    bernsteinRowNonnegativeN 6 60 negativePRightMarginPayload 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_nonnegative_row_2 :
    bernsteinRowNonnegativeN 6 60 negativePRightMarginPayload 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_nonnegative_row_3 :
    bernsteinRowNonnegativeN 6 60 negativePRightMarginPayload 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_nonnegative_row_4 :
    bernsteinRowNonnegativeN 6 60 negativePRightMarginPayload 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_nonnegative_row_5 :
    bernsteinRowNonnegativeN 6 60 negativePRightMarginPayload 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_right_nonnegative_row_6 :
    bernsteinRowNonnegativeN 6 60 negativePRightMarginPayload 6 = true := by
  with_unfolding_all rfl

/-- Certified negative-P data. -/
theorem negative_p_left_coefficients (i j : Fin 7) :
    bin4NegativePLeftMargin.numerator.coefficient i j =
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePLeftMarginPayload).coefficient i j := by
  fin_cases i
  · exact of_decide_eq_true negative_p_left_row_0 j
  · exact of_decide_eq_true negative_p_left_row_1 j
  · exact of_decide_eq_true negative_p_left_row_2 j
  · exact of_decide_eq_true negative_p_left_row_3 j
  · exact of_decide_eq_true negative_p_left_row_4 j
  · exact of_decide_eq_true negative_p_left_row_5 j
  · exact of_decide_eq_true negative_p_left_row_6 j

/-- Certified negative-P data. -/
theorem negative_p_left_row_shape :
    bin4NegativePLeftMargin.numerator.length = 7 ∧
      ∀ row ∈ bin4NegativePLeftMargin.numerator, row.length = 7 :=
  of_decide_eq_true negative_p_left_shape_check

/-- Certified negative-P data. -/
theorem negative_p_left_bernstein_nonnegative (i j : Fin 7) :
    0 ≤ bernsteinInteger 6 60 negativePLeftMarginPayload i j := by
  fin_cases i
  · exact of_decide_eq_true negative_p_left_nonnegative_row_0 j
  · exact of_decide_eq_true negative_p_left_nonnegative_row_1 j
  · exact of_decide_eq_true negative_p_left_nonnegative_row_2 j
  · exact of_decide_eq_true negative_p_left_nonnegative_row_3 j
  · exact of_decide_eq_true negative_p_left_nonnegative_row_4 j
  · exact of_decide_eq_true negative_p_left_nonnegative_row_5 j
  · exact of_decide_eq_true negative_p_left_nonnegative_row_6 j

/-- Certified negative-P data. -/
theorem negative_p_middle_coefficients (i j : Fin 7) :
    bin4NegativePMiddleMargin.numerator.coefficient i j =
      (IntBivariate.scaleInt ((2 : ℤ) ^ 5) negativePMiddleMarginPayload).coefficient i j := by
  fin_cases i
  · exact of_decide_eq_true negative_p_middle_row_0 j
  · exact of_decide_eq_true negative_p_middle_row_1 j
  · exact of_decide_eq_true negative_p_middle_row_2 j
  · exact of_decide_eq_true negative_p_middle_row_3 j
  · exact of_decide_eq_true negative_p_middle_row_4 j
  · exact of_decide_eq_true negative_p_middle_row_5 j
  · exact of_decide_eq_true negative_p_middle_row_6 j

/-- Certified negative-P data. -/
theorem negative_p_middle_row_shape :
    bin4NegativePMiddleMargin.numerator.length = 7 ∧
      ∀ row ∈ bin4NegativePMiddleMargin.numerator, row.length = 7 :=
  of_decide_eq_true negative_p_middle_shape_check

/-- Certified negative-P data. -/
theorem negative_p_middle_bernstein_nonnegative (i j : Fin 7) :
    0 ≤ bernsteinInteger 6 60 negativePMiddleMarginPayload i j := by
  fin_cases i
  · exact of_decide_eq_true negative_p_middle_nonnegative_row_0 j
  · exact of_decide_eq_true negative_p_middle_nonnegative_row_1 j
  · exact of_decide_eq_true negative_p_middle_nonnegative_row_2 j
  · exact of_decide_eq_true negative_p_middle_nonnegative_row_3 j
  · exact of_decide_eq_true negative_p_middle_nonnegative_row_4 j
  · exact of_decide_eq_true negative_p_middle_nonnegative_row_5 j
  · exact of_decide_eq_true negative_p_middle_nonnegative_row_6 j

/-- Certified negative-P data. -/
theorem negative_p_right_coefficients (i j : Fin 7) :
    bin4NegativePRightMargin.numerator.coefficient i j =
      (IntBivariate.scaleInt ((2 : ℤ) ^ 4) negativePRightMarginPayload).coefficient i j := by
  fin_cases i
  · exact of_decide_eq_true negative_p_right_row_0 j
  · exact of_decide_eq_true negative_p_right_row_1 j
  · exact of_decide_eq_true negative_p_right_row_2 j
  · exact of_decide_eq_true negative_p_right_row_3 j
  · exact of_decide_eq_true negative_p_right_row_4 j
  · exact of_decide_eq_true negative_p_right_row_5 j
  · exact of_decide_eq_true negative_p_right_row_6 j

/-- Certified negative-P data. -/
theorem negative_p_right_row_shape :
    bin4NegativePRightMargin.numerator.length = 7 ∧
      ∀ row ∈ bin4NegativePRightMargin.numerator, row.length = 7 :=
  of_decide_eq_true negative_p_right_shape_check

/-- Certified negative-P data. -/
theorem negative_p_right_bernstein_nonnegative (i j : Fin 7) :
    0 ≤ bernsteinInteger 6 60 negativePRightMarginPayload i j := by
  fin_cases i
  · exact of_decide_eq_true negative_p_right_nonnegative_row_0 j
  · exact of_decide_eq_true negative_p_right_nonnegative_row_1 j
  · exact of_decide_eq_true negative_p_right_nonnegative_row_2 j
  · exact of_decide_eq_true negative_p_right_nonnegative_row_3 j
  · exact of_decide_eq_true negative_p_right_nonnegative_row_4 j
  · exact of_decide_eq_true negative_p_right_nonnegative_row_5 j
  · exact of_decide_eq_true negative_p_right_nonnegative_row_6 j

end

end WeightedSelfTaylorBin4
end Bescovitch
