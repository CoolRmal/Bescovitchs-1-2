/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Check.ModelFactors
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Check.RemainderFactors
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Check.Signs
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Check.Budget
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.Budget

/-!
# Semantic interpretation of the Taylor certificate
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

private def rowsHaveLength (n : ℕ) : IntBivariate → Bool
  | [] => true
  | row :: rows => decide (row.length = n) && rowsHaveLength n rows

private def fastMatrixHasShape (n : ℕ) (p : IntBivariate) : Bool :=
  decide (p.length = n) && rowsHaveLength n p

private theorem rowsHaveLength_sound {n : ℕ} {p : IntBivariate}
    (h : rowsHaveLength n p = true) : ∀ row ∈ p, row.length = n := by
  induction p with
  | nil => simp
  | cons head tail ih =>
      simp only [rowsHaveLength, Bool.and_eq_true] at h
      intro row hrow
      simp only [List.mem_cons] at hrow
      rcases hrow with rfl | hrow
      · exact of_decide_eq_true h.1
      · exact ih h.2 row hrow

private theorem fastMatrixHasShape_sound {n : ℕ} {p : IntBivariate}
    (h : fastMatrixHasShape n p = true) :
    p.length = n ∧ ∀ row ∈ p, row.length = n := by
  simp only [fastMatrixHasShape, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, rowsHaveLength_sound h.2⟩

set_option maxRecDepth 100000 in
private theorem center_value_payload_shape_check :
    fastMatrixHasShape 13 centerValuePowerPayload = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
private theorem center_slope_payload_shape_check :
    fastMatrixHasShape 13 centerSlopePowerPayload = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
private theorem lower_curvature_payload_shape_check :
    fastMatrixHasShape 13 lowerCurvaturePowerPayload = true := by
  with_unfolding_all rfl

private theorem center_value_payload_shape :
    centerValuePowerPayload.length = 13 ∧
      ∀ row ∈ centerValuePowerPayload, row.length = 13 :=
  fastMatrixHasShape_sound center_value_payload_shape_check

private theorem center_slope_payload_shape :
    centerSlopePowerPayload.length = 13 ∧
      ∀ row ∈ centerSlopePowerPayload, row.length = 13 :=
  fastMatrixHasShape_sound center_slope_payload_shape_check

private theorem lower_curvature_payload_shape :
    lowerCurvaturePowerPayload.length = 13 ∧
      ∀ row ∈ lowerCurvaturePowerPayload, row.length = 13 :=
  fastMatrixHasShape_sound lower_curvature_payload_shape_check

open scoped BigOperators unitInterval

/-- Casting the recursive integer sum agrees with the corresponding finite real sum. -/
theorem intSum_cast' (n : ℕ) (f : Fin n → ℤ) :
    ((intSum n f : ℤ) : ℝ) = ∑ i, (f i : ℝ) := by
  induction n with
  | zero => simp [intSum]
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [intSum, Int.cast_add]
      rw [ih]

private theorem bernsteinFirstInteger_cast (degree : ℕ) (binomialLcm : ℤ)
    (hdiv : ∀ h : Fin (degree + 1), (Nat.choose degree h : ℤ) ∣ binomialLcm)
    (p : IntBivariate) (i j : Fin (degree + 1)) :
    ((bernsteinFirstInteger degree binomialLcm p i j : ℤ) : ℝ) =
      (binomialLcm : ℝ) *
        powerToBernstein degree (fun h ↦ (p.coefficient h j : ℝ)) i := by
  rw [bernsteinFirstInteger, intSum_cast', powerToBernstein, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs
  · norm_num only [Int.cast_mul, Int.cast_natCast]
    rw [Int.cast_div (hdiv h)]
    · norm_num only [Int.cast_natCast]
      ring
    · exact_mod_cast Nat.choose_ne_zero (Nat.lt_succ_iff.mp h.isLt)
  · simp

/-- Integer Bernstein conversion agrees with exact real conversion after positive scaling. -/
theorem bernsteinInteger_cast (degree : ℕ) (binomialLcm : ℤ)
    (hdiv : ∀ h : Fin (degree + 1), (Nat.choose degree h : ℤ) ∣ binomialLcm)
    (p : IntBivariate) (i j : Fin (degree + 1)) :
    ((bernsteinInteger degree binomialLcm p i j : ℤ) : ℝ) =
      (binomialLcm : ℝ) ^ 2 *
        powerTensorToBernstein
          (fun h k ↦ (p.coefficient h k : ℝ)) i j := by
  rw [bernsteinInteger, intSum_cast', powerTensorToBernstein, powerToBernstein,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs
  · norm_num only [Int.cast_mul, Int.cast_natCast]
    rw [bernsteinFirstInteger_cast degree binomialLcm hdiv, Int.cast_div (hdiv h)]
    · norm_num only [Int.cast_natCast]
      ring
    · exact_mod_cast Nat.choose_ne_zero (Nat.lt_succ_iff.mp h.isLt)
  · simp

private theorem binomial_lcm_12_divides (h : Fin 13) :
    (Nat.choose 12 h : ℤ) ∣ 27720 := by
  fin_cases h <;> norm_num [Nat.choose]

private theorem converted12_nonnegative
    (power : IntBivariate)
    (hnonnegative : ∀ i j : Fin 13, 0 ≤ bernsteinInteger 12 27720 power i j)
    (i j : Fin 13) :
    0 ≤ powerTensorToBernstein
      (fun h k ↦ (power.coefficient h k : ℝ)) i j := by
  have hcast : (0 : ℝ) ≤ (bernsteinInteger 12 27720 power i j : ℝ) := by
    exact_mod_cast hnonnegative i j
  rw [bernsteinInteger_cast 12 27720 binomial_lcm_12_divides] at hcast
  norm_num at hcast ⊢
  nlinarith

private theorem power12_nonnegative
    (power : IntBivariate)
    (hnonnegative : ∀ i j : Fin 13, 0 ≤ bernsteinInteger 12 27720 power i j)
    (x y : I) :
    0 ≤ paddedPowerTensorEval
      (fun i : Fin 13 ↦ fun j : Fin 13 ↦ (power.coefficient i j : ℝ)) x y := by
  exact paddedPowerTensorEval_nonneg_of_bernstein
    (converted12_nonnegative power hnonnegative) x y

/-- The stored degree-twelve representation of the quartic coefficient is nonnegative. -/
theorem d4_power_nonnegative (x y : I) :
    0 ≤ paddedPowerTensorEval
      (fun i : Fin 13 ↦ fun j : Fin 13 ↦ (d4PowerPayload.coefficient i j : ℝ)) x y := by
  exact power12_nonnegative d4PowerPayload d4_bernstein_nonnegative x y

/-- The stored affine remainder-slack polynomial is nonnegative. -/
theorem remainder_linear_slack_power_nonnegative (x y : I) :
    0 ≤ paddedPowerTensorEval
      (fun i : Fin 13 ↦ fun j : Fin 13 ↦
        (remainderLinearSlackPowerPayload.coefficient i j : ℝ)) x y := by
  exact power12_nonnegative remainderLinearSlackPowerPayload
    remainder_linear_slack_bernstein_nonnegative x y

/-- The stored lower-curvature polynomial is nonnegative. -/
theorem lower_curvature_power_nonnegative (x y : I) :
    0 ≤ paddedPowerTensorEval
      (fun i : Fin 13 ↦ fun j : Fin 13 ↦
        (lowerCurvaturePowerPayload.coefficient i j : ℝ)) x y := by
  exact power12_nonnegative lowerCurvaturePowerPayload
    lower_curvature_bernstein_nonnegative x y

/-- The stored upper-curvature slack polynomial is nonnegative. -/
theorem upper_curvature_power_nonnegative (x y : I) :
    0 ≤ paddedPowerTensorEval
      (fun i : Fin 13 ↦ fun j : Fin 13 ↦
        (upperCurvaturePowerPayload.coefficient i j : ℝ)) x y := by
  exact power12_nonnegative upperCurvaturePowerPayload
    upper_curvature_bernstein_nonnegative x y

private theorem binomial_lcm_24_divides (h : Fin 25) :
    (Nat.choose 24 h : ℤ) ∣ 1070845776 := by
  fin_cases h <;> norm_num [Nat.choose]

private theorem budget_converted_nonnegative (i j : Fin 25) :
    0 ≤ powerTensorToBernstein
      (fun h k ↦ (budgetFactorPayload.coefficient h k : ℝ)) i j := by
  have hcast : (0 : ℝ) ≤
      (bernsteinInteger 24 1070845776 budgetFactorPayload i j : ℝ) := by
    exact_mod_cast budget_bernstein_nonnegative i j
  rw [bernsteinInteger_cast 24 1070845776 binomial_lcm_24_divides] at hcast
  norm_num at hcast ⊢
  nlinarith

/-- The stored completed-square budget polynomial is nonnegative. -/
theorem budget_power_nonnegative (x y : I) :
    0 ≤ paddedPowerTensorEval
      (fun i : Fin 25 ↦ fun j : Fin 25 ↦
        (budgetFactorPayload.coefficient i j : ℝ)) x y := by
  exact paddedPowerTensorEval_nonneg_of_bernstein budget_converted_nonnegative x y

private theorem padded_eval_scaleInt (degree : ℕ) (a : ℤ) (p : IntBivariate)
    (x y : I) :
    paddedPowerTensorEval
        (fun i : Fin (degree + 1) ↦ fun j : Fin (degree + 1) ↦
          ((IntBivariate.scaleInt a p).coefficient i j : ℝ)) x y =
      (a : ℝ) * paddedPowerTensorEval
        (fun i : Fin (degree + 1) ↦ fun j : Fin (degree + 1) ↦
          (p.coefficient i j : ℝ)) x y := by
  simp only [IntBivariate.coefficient_scaleInt, Int.cast_mul]
  unfold paddedPowerTensorEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Interpret a scaled coefficient identity as equality with a padded power tensor. -/
theorem scaled_eval_eq_payload {degree actualExponent payloadExponent shift : ℕ}
    (p : ScaledPolynomial) (payload : IntBivariate)
    (hexponent : p.exponent = actualExponent)
    (hexponents : actualExponent = payloadExponent + shift)
    (hshape : p.numerator.length = degree + 1 ∧
      ∀ row ∈ p.numerator, row.length = degree + 1)
    (hcoeff : ∀ i j : Fin (degree + 1), p.numerator.coefficient i j =
      (IntBivariate.scaleInt ((2 : ℤ) ^ shift) payload).coefficient i j)
    (x y : I) :
    ScaledPolynomial.eval p x y =
      paddedPowerTensorEval
        (fun i : Fin (degree + 1) ↦ fun j : Fin (degree + 1) ↦
          (payload.coefficient i j : ℝ)) x y / (2 : ℝ) ^ payloadExponent := by
  rw [ScaledPolynomial.eval, hexponent, hexponents]
  rw [IntBivariate.eval_eq_paddedPowerTensorEval_of_coefficients degree p.numerator
    (fun i j ↦ p.numerator.coefficient i j) hshape.1 hshape.2 (fun _ _ ↦ rfl)]
  simp_rw [hcoeff]
  rw [padded_eval_scaleInt, pow_add]
  norm_num only [Int.cast_pow, Int.cast_ofNat]
  field_simp

/-- Evaluate the certified polynomial for the discriminant's center value. -/
theorem center_value_eval (x y : I) :
    ScaledPolynomial.eval bin4CenterValue x y =
      paddedPowerTensorEval
        (fun i : Fin 13 ↦ fun j : Fin 13 ↦
          (centerValuePowerPayload.coefficient i j : ℝ)) x y / (2 : ℝ) ^ 560 := by
  exact scaled_eval_eq_payload bin4CenterValue centerValuePowerPayload
    center_value_actual_exponent (by norm_num) center_value_row_shape
    center_value_coefficients x y

/-- Evaluate the certified polynomial for the discriminant's center slope. -/
theorem center_slope_eval (x y : I) :
    ScaledPolynomial.eval bin4CenterSlope x y =
      paddedPowerTensorEval
        (fun i : Fin 13 ↦ fun j : Fin 13 ↦
          (centerSlopePowerPayload.coefficient i j : ℝ)) x y / (2 : ℝ) ^ 516 := by
  exact scaled_eval_eq_payload bin4CenterSlope centerSlopePowerPayload
    center_slope_actual_exponent (by norm_num) center_slope_row_shape
    center_slope_coefficients x y

/-- Evaluate the certified lower-curvature polynomial. -/
theorem lower_curvature_eval (x y : I) :
    ScaledPolynomial.eval bin4LowerCurvature x y =
      paddedPowerTensorEval
        (fun i : Fin 13 ↦ fun j : Fin 13 ↦
          (lowerCurvaturePowerPayload.coefficient i j : ℝ)) x y / (2 : ℝ) ^ 476 := by
  exact scaled_eval_eq_payload bin4LowerCurvature lowerCurvaturePowerPayload
    lower_curvature_actual_exponent (by norm_num) lower_curvature_row_shape
    lower_curvature_coefficients x y

/-- Evaluate the certified quartic coefficient. -/
theorem d4_eval (x y : I) :
    ScaledPolynomial.eval bin4D4 x y =
      paddedPowerTensorEval
        (fun i : Fin 13 ↦ fun j : Fin 13 ↦
          (d4PowerPayload.coefficient i j : ℝ)) x y / (2 : ℝ) ^ 392 := by
  exact scaled_eval_eq_payload bin4D4 d4PowerPayload
    d4_actual_exponent (by norm_num) d4_row_shape d4_coefficients x y

/-- Evaluate the certified affine remainder-slack polynomial. -/
theorem remainder_linear_slack_eval (x y : I) :
    ScaledPolynomial.eval bin4RemainderLinearSlack x y =
      paddedPowerTensorEval
        (fun i : Fin 13 ↦ fun j : Fin 13 ↦
          (remainderLinearSlackPowerPayload.coefficient i j : ℝ)) x y /
        (2 : ℝ) ^ 433 := by
  exact scaled_eval_eq_payload bin4RemainderLinearSlack
    remainderLinearSlackPowerPayload remainder_linear_slack_actual_exponent (by norm_num)
    remainder_linear_slack_row_shape remainder_linear_slack_coefficients x y

/-- Evaluate the certified upper-curvature slack polynomial. -/
theorem upper_curvature_eval (x y : I) :
    ScaledPolynomial.eval bin4UpperCurvature x y =
      paddedPowerTensorEval
        (fun i : Fin 13 ↦ fun j : Fin 13 ↦
          (upperCurvaturePowerPayload.coefficient i j : ℝ)) x y /
        (2 : ℝ) ^ 476 := by
  exact scaled_eval_eq_payload bin4UpperCurvature upperCurvaturePowerPayload
    upper_curvature_actual_exponent (by norm_num) upper_curvature_row_shape
    upper_curvature_coefficients x y

/-- Evaluate the stored completed-square budget polynomial. -/
theorem budget_eval (x y : I) :
    ScaledPolynomial.eval storedBudget x y =
      paddedPowerTensorEval
        (fun i : Fin 25 ↦ fun j : Fin 25 ↦
          (budgetFactorPayload.coefficient i j : ℝ)) x y / (2 : ℝ) ^ 1031 := by
  exact scaled_eval_eq_payload (degree := 24) (actualExponent := 1158)
    (payloadExponent := 1031) (shift := 127) storedBudget budgetFactorPayload
    stored_budget_actual_exponent (by norm_num) stored_budget_row_shape
    stored_budget_coefficients x y

private theorem scaleInt_shape {n : ℕ} {p : IntBivariate} (a : ℤ)
    (hshape : p.length = n ∧ ∀ row ∈ p, row.length = n) :
    (IntBivariate.scaleInt a p).length = n ∧
      ∀ row ∈ IntBivariate.scaleInt a p, row.length = n := by
  constructor
  · simpa [IntBivariate.scaleInt] using hshape.1
  · intro row hrow
    simp only [IntBivariate.scaleInt, List.mem_map] at hrow
    obtain ⟨source, hsource, rfl⟩ := hrow
    simpa using hshape.2 source hsource

private theorem stored_center_value_eval (x y : I) :
    ScaledPolynomial.eval storedCenterValue x y =
      paddedPowerTensorEval
        (fun i : Fin 13 ↦ fun j : Fin 13 ↦
          (centerValuePowerPayload.coefficient i j : ℝ)) x y / (2 : ℝ) ^ 560 := by
  exact scaled_eval_eq_payload (degree := 12) (actualExponent := 584)
    (payloadExponent := 560) (shift := 24) storedCenterValue centerValuePowerPayload
    rfl (by norm_num) (by
      simpa only [storedCenterValue] using
        scaleInt_shape ((2 : ℤ) ^ 24) center_value_payload_shape)
    (fun _ _ ↦ rfl) x y

private theorem stored_center_slope_eval (x y : I) :
    ScaledPolynomial.eval storedCenterSlope x y =
      paddedPowerTensorEval
        (fun i : Fin 13 ↦ fun j : Fin 13 ↦
          (centerSlopePowerPayload.coefficient i j : ℝ)) x y / (2 : ℝ) ^ 516 := by
  exact scaled_eval_eq_payload (degree := 12) (actualExponent := 579)
    (payloadExponent := 516) (shift := 63) storedCenterSlope centerSlopePowerPayload
    rfl (by norm_num) (by
      simpa only [storedCenterSlope] using
        scaleInt_shape ((2 : ℤ) ^ 63) center_slope_payload_shape)
    (fun _ _ ↦ rfl) x y

private theorem stored_lower_curvature_eval (x y : I) :
    ScaledPolynomial.eval storedLowerCurvature x y =
      paddedPowerTensorEval
        (fun i : Fin 13 ↦ fun j : Fin 13 ↦
          (lowerCurvaturePowerPayload.coefficient i j : ℝ)) x y /
        (2 : ℝ) ^ 476 := by
  exact scaled_eval_eq_payload (degree := 12) (actualExponent := 574)
    (payloadExponent := 476) (shift := 98) storedLowerCurvature
    lowerCurvaturePowerPayload rfl (by norm_num) (by
      simpa only [storedLowerCurvature] using
        scaleInt_shape ((2 : ℤ) ^ 98) lower_curvature_payload_shape)
    (fun _ _ ↦ rfl) x y

/-- The stored budget represents the exact dyadic completed-square expression. -/
theorem stored_budget_eval_eq_bin4_budget (x y : I) :
    ScaledPolynomial.eval storedBudget x y =
      ScaledPolynomial.eval bin4Budget x y := by
  simp only [storedBudget, bin4Budget, ScaledPolynomial.eval_add_notation,
    ScaledPolynomial.eval_neg_notation, ScaledPolynomial.eval_mul_notation,
    ScaledPolynomial.eval_pow_notation, ScaledPolynomial.eval_dyadic]
  rw [stored_center_value_eval, center_value_eval, stored_center_slope_eval,
    center_slope_eval, stored_lower_curvature_eval, lower_curvature_eval]

end

end WeightedSelfTaylorBin4
end Bescovitch
