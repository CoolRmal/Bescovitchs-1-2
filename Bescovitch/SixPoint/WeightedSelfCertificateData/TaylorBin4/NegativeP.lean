/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Check.NegativeP
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Certificate
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Nominal

/-!
# Nominal negative-P certificate
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

open scoped unitInterval

private theorem binomial_lcm_6_divides (h : Fin 7) :
    (Nat.choose 6 h : ℤ) ∣ 60 := by
  fin_cases h <;> norm_num [Nat.choose]

private theorem power6_nonnegative
    (power : IntBivariate)
    (hnonnegative : ∀ i j : Fin 7, 0 ≤ bernsteinInteger 6 60 power i j)
    (x y : I) :
    0 ≤ paddedPowerTensorEval
      (fun i : Fin 7 ↦ fun j : Fin 7 ↦ (power.coefficient i j : ℝ)) x y := by
  apply paddedPowerTensorEval_nonneg_of_bernstein
  intro i j
  have hcast : (0 : ℝ) ≤ (bernsteinInteger 6 60 power i j : ℝ) := by
    exact_mod_cast hnonnegative i j
  rw [bernsteinInteger_cast 6 60 binomial_lcm_6_divides] at hcast
  norm_num at hcast ⊢
  nlinarith

private theorem negative_p_left_margin_eval (x y : I) :
    ScaledPolynomial.eval bin4NegativePLeftMargin x y =
      paddedPowerTensorEval
        (fun i : Fin 7 ↦ fun j : Fin 7 ↦
          (negativePLeftMarginPayload.coefficient i j : ℝ)) x y / (2 : ℝ) ^ 278 := by
  exact scaled_eval_eq_payload (degree := 6) (actualExponent := 282)
    (payloadExponent := 278) (shift := 4) bin4NegativePLeftMargin
    negativePLeftMarginPayload negative_p_left_actual_exponent (by norm_num)
    negative_p_left_row_shape negative_p_left_coefficients x y

private theorem negative_p_middle_margin_eval (x y : I) :
    ScaledPolynomial.eval bin4NegativePMiddleMargin x y =
      paddedPowerTensorEval
        (fun i : Fin 7 ↦ fun j : Fin 7 ↦
          (negativePMiddleMarginPayload.coefficient i j : ℝ)) x y / (2 : ℝ) ^ 278 := by
  exact scaled_eval_eq_payload (degree := 6) (actualExponent := 283)
    (payloadExponent := 278) (shift := 5) bin4NegativePMiddleMargin
    negativePMiddleMarginPayload negative_p_middle_actual_exponent (by norm_num)
    negative_p_middle_row_shape negative_p_middle_coefficients x y

private theorem negative_p_right_margin_eval (x y : I) :
    ScaledPolynomial.eval bin4NegativePRightMargin x y =
      paddedPowerTensorEval
        (fun i : Fin 7 ↦ fun j : Fin 7 ↦
          (negativePRightMarginPayload.coefficient i j : ℝ)) x y / (2 : ℝ) ^ 278 := by
  exact scaled_eval_eq_payload (degree := 6) (actualExponent := 282)
    (payloadExponent := 278) (shift := 4) bin4NegativePRightMargin
    negativePRightMarginPayload negative_p_right_actual_exponent (by norm_num)
    negative_p_right_row_shape negative_p_right_coefficients x y

private theorem negative_p_left_margin_nonnegative (x y : I) :
    0 ≤ ScaledPolynomial.eval bin4NegativePLeftMargin x y := by
  rw [negative_p_left_margin_eval]
  exact div_nonneg
    (power6_nonnegative negativePLeftMarginPayload
      negative_p_left_bernstein_nonnegative x y)
    (by positivity)

private theorem negative_p_middle_margin_nonnegative (x y : I) :
    0 ≤ ScaledPolynomial.eval bin4NegativePMiddleMargin x y := by
  rw [negative_p_middle_margin_eval]
  exact div_nonneg
    (power6_nonnegative negativePMiddleMarginPayload
      negative_p_middle_bernstein_nonnegative x y)
    (by positivity)

private theorem negative_p_right_margin_nonnegative (x y : I) :
    0 ≤ ScaledPolynomial.eval bin4NegativePRightMargin x y := by
  rw [negative_p_right_margin_eval]
  exact div_nonneg
    (power6_nonnegative negativePRightMarginPayload
      negative_p_right_bernstein_nonnegative x y)
    (by positivity)

private theorem negative_p_left_lower_bound (x y : I) :
    (29 / 100 : ℝ) ≤ ScaledPolynomial.eval bin4NegativePLeft x y := by
  have h := negative_p_left_margin_nonnegative x y
  simp only [bin4NegativePLeftMargin,
    ScaledPolynomial.eval_add_notation, ScaledPolynomial.eval_neg_notation,
    ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_dyadic] at h
  norm_num at h ⊢
  linarith

private theorem negative_p_middle_lower_bound (x y : I) :
    (29 / 100 : ℝ) ≤ ScaledPolynomial.eval bin4NegativePMiddle x y := by
  have h := negative_p_middle_margin_nonnegative x y
  simp only [bin4NegativePMiddleMargin,
    ScaledPolynomial.eval_add_notation, ScaledPolynomial.eval_neg_notation,
    ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_dyadic] at h
  norm_num at h ⊢
  linarith

private theorem negative_p_right_lower_bound (x y : I) :
    (29 / 100 : ℝ) ≤ ScaledPolynomial.eval bin4NegativePRight x y := by
  have h := negative_p_right_margin_nonnegative x y
  simp only [bin4NegativePRightMargin,
    ScaledPolynomial.eval_add_notation, ScaledPolynomial.eval_neg_notation,
    ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_dyadic] at h
  norm_num at h ⊢
  linarith

/-- The nominal quadratic coefficient `-P` has a uniform margin on the hard bin. -/
theorem bin4_nominal_negative_p_lower_bound (x y z : I) :
    (29 / 100 : ℝ) ≤ -(bin4NominalFormula x y z).p := by
  have hleft := negative_p_left_lower_bound x y
  have hmiddle := negative_p_middle_lower_bound x y
  have hright := negative_p_right_lower_bound x y
  have hz0 : (0 : ℝ) ≤ z := z.property.1
  have hz1 : (z : ℝ) ≤ 1 := z.property.2
  have hweight0 : 0 ≤ (1 - (z : ℝ)) ^ 2 := sq_nonneg _
  have hweight1 : 0 ≤ 2 * (z : ℝ) * (1 - z) := by positivity
  have hweight2 : 0 ≤ (z : ℝ) ^ 2 := sq_nonneg _
  have hweighted :
      (29 / 100 : ℝ) * ((1 - z) ^ 2 + 2 * z * (1 - z) + z ^ 2) ≤
        ScaledPolynomial.eval bin4NegativePLeft x y * (1 - z) ^ 2 +
          ScaledPolynomial.eval bin4NegativePMiddle x y * (2 * z * (1 - z)) +
          ScaledPolynomial.eval bin4NegativePRight x y * z ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hleft) hweight0,
      mul_nonneg (sub_nonneg.mpr hmiddle) hweight1,
      mul_nonneg (sub_nonneg.mpr hright) hweight2]
  rw [bin4_nominal_p_eq]
  simp only [bin4NegativePLeft, bin4NegativePMiddle, bin4NegativePRight,
    ScaledPolynomial.eval_add_notation, ScaledPolynomial.eval_neg_notation,
    ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_dyadic] at hweighted ⊢
  norm_num at hweighted ⊢
  nlinarith

end

end WeightedSelfTaylorBin4
end Bescovitch
