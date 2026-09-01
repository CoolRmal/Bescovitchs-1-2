/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.Budget

/-!
# Checks for the completed-square budget
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

set_option maxRecDepth 100000 in
/-- The exact denominator exponent of the stored completed-square budget. -/
theorem stored_budget_actual_exponent : storedBudget.exponent = 1158 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_0 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_1 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_2 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_3 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_4 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_5 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_6 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_7 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_8 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_9 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_10 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_11 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_12 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 12 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_13 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 13 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_14 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 14 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_15 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 15 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_16 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 16 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_17 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 17 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_18 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 18 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_19 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 19 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_20 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 20 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_21 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 21 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_22 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 22 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_23 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 23 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_row_24 :
    rowEqN 25 storedBudget.numerator
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload) 24 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem stored_budget_shape_check : matrixHasShape 25 storedBudget.numerator = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_0 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 0 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_1 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 1 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_2 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 2 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_3 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 3 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_4 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 4 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_5 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 5 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_6 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 6 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_7 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 7 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_8 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 8 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_9 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 9 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_10 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 10 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_11 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 11 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_12 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 12 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_13 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 13 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_14 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 14 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_15 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 15 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_16 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 16 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_17 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 17 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_18 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 18 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_19 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 19 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_20 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 20 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_21 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 21 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_22 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 22 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_23 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 23 = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem budget_nonnegative_row_24 :
    bernsteinRowNonnegativeN 24 1070845776 budgetFactorPayload 24 = true := by
  with_unfolding_all rfl

/-- Certified completed-square budget data. -/
theorem stored_budget_coefficients (i j : Fin 25) :
    (storedBudget.numerator).coefficient i j =
      (IntBivariate.scaleInt ((2 : ℤ) ^ 127) budgetFactorPayload).coefficient i j := by
  fin_cases i
  · exact of_decide_eq_true stored_budget_row_0 j
  · exact of_decide_eq_true stored_budget_row_1 j
  · exact of_decide_eq_true stored_budget_row_2 j
  · exact of_decide_eq_true stored_budget_row_3 j
  · exact of_decide_eq_true stored_budget_row_4 j
  · exact of_decide_eq_true stored_budget_row_5 j
  · exact of_decide_eq_true stored_budget_row_6 j
  · exact of_decide_eq_true stored_budget_row_7 j
  · exact of_decide_eq_true stored_budget_row_8 j
  · exact of_decide_eq_true stored_budget_row_9 j
  · exact of_decide_eq_true stored_budget_row_10 j
  · exact of_decide_eq_true stored_budget_row_11 j
  · exact of_decide_eq_true stored_budget_row_12 j
  · exact of_decide_eq_true stored_budget_row_13 j
  · exact of_decide_eq_true stored_budget_row_14 j
  · exact of_decide_eq_true stored_budget_row_15 j
  · exact of_decide_eq_true stored_budget_row_16 j
  · exact of_decide_eq_true stored_budget_row_17 j
  · exact of_decide_eq_true stored_budget_row_18 j
  · exact of_decide_eq_true stored_budget_row_19 j
  · exact of_decide_eq_true stored_budget_row_20 j
  · exact of_decide_eq_true stored_budget_row_21 j
  · exact of_decide_eq_true stored_budget_row_22 j
  · exact of_decide_eq_true stored_budget_row_23 j
  · exact of_decide_eq_true stored_budget_row_24 j

/-- Certified completed-square budget data. -/
theorem stored_budget_row_shape :
    (storedBudget.numerator).length = 25 ∧
      ∀ row ∈ (storedBudget.numerator), row.length = 25 :=
  of_decide_eq_true stored_budget_shape_check

/-- Certified completed-square budget data. -/
theorem budget_bernstein_nonnegative (i j : Fin 25) :
    0 ≤ bernsteinInteger 24 1070845776 budgetFactorPayload i j := by
  fin_cases i
  · exact of_decide_eq_true budget_nonnegative_row_0 j
  · exact of_decide_eq_true budget_nonnegative_row_1 j
  · exact of_decide_eq_true budget_nonnegative_row_2 j
  · exact of_decide_eq_true budget_nonnegative_row_3 j
  · exact of_decide_eq_true budget_nonnegative_row_4 j
  · exact of_decide_eq_true budget_nonnegative_row_5 j
  · exact of_decide_eq_true budget_nonnegative_row_6 j
  · exact of_decide_eq_true budget_nonnegative_row_7 j
  · exact of_decide_eq_true budget_nonnegative_row_8 j
  · exact of_decide_eq_true budget_nonnegative_row_9 j
  · exact of_decide_eq_true budget_nonnegative_row_10 j
  · exact of_decide_eq_true budget_nonnegative_row_11 j
  · exact of_decide_eq_true budget_nonnegative_row_12 j
  · exact of_decide_eq_true budget_nonnegative_row_13 j
  · exact of_decide_eq_true budget_nonnegative_row_14 j
  · exact of_decide_eq_true budget_nonnegative_row_15 j
  · exact of_decide_eq_true budget_nonnegative_row_16 j
  · exact of_decide_eq_true budget_nonnegative_row_17 j
  · exact of_decide_eq_true budget_nonnegative_row_18 j
  · exact of_decide_eq_true budget_nonnegative_row_19 j
  · exact of_decide_eq_true budget_nonnegative_row_20 j
  · exact of_decide_eq_true budget_nonnegative_row_21 j
  · exact of_decide_eq_true budget_nonnegative_row_22 j
  · exact of_decide_eq_true budget_nonnegative_row_23 j
  · exact of_decide_eq_true budget_nonnegative_row_24 j

end

end WeightedSelfTaylorBin4
end Bescovitch
