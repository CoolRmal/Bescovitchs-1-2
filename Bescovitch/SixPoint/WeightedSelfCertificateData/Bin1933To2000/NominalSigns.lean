/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Formula
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PFactor
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PSign
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QFactor
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RadicandFactor
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DiscriminantFactor
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DiscriminantSign

/-!
# Nominal sign margins on the radius bin `[1933/5000, 2/5]`
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

open DyadicTrivariatePolynomial

noncomputable section

open scoped unitInterval

private theorem negative_p_eval_eq_aux (x y z : ℝ) :
    negativeP.eval x y z = storedNegativeP.eval x y z := by
  rcases negative_p_factor with ⟨he, hp, hq, hcoeff⟩
  rcases fits_degree_box_sound hp with ⟨hp0, hp1, hp2⟩
  rcases fits_degree_box_sound hq with ⟨hq0, hq1, hq2⟩
  exact ScaledPolynomial.eval_eq_of_tensor negativeP storedNegativeP
    he hp0 hp1 hp2 hq0 hq1 hq2 hcoeff x y z

private theorem q_eval_eq_aux (x y z : ℝ) :
    formula.q.eval x y z = storedQ.eval x y z := by
  rcases q_factor with ⟨he, hp, hq, hcoeff⟩
  rcases fits_degree_box_sound hp with ⟨hp0, hp1, hp2⟩
  rcases fits_degree_box_sound hq with ⟨hq0, hq1, hq2⟩
  exact ScaledPolynomial.eval_eq_of_tensor formula.q storedQ
    he hp0 hp1 hp2 hq0 hq1 hq2 hcoeff x y z

private theorem radicand_eval_eq_aux (x y z : ℝ) :
    formula.radicand.eval x y z = storedRadicand.eval x y z := by
  rcases radicand_factor with ⟨he, hp, hq, hcoeff⟩
  rcases fits_degree_box_sound hp with ⟨hp0, hp1, hp2⟩
  rcases fits_degree_box_sound hq with ⟨hq0, hq1, hq2⟩
  exact ScaledPolynomial.eval_eq_of_tensor formula.radicand storedRadicand
    he hp0 hp1 hp2 hq0 hq1 hq2 hcoeff x y z

private theorem discriminant_payload_eval_eq_aux (x y z : ℝ) :
    storedDiscriminant.eval x y z = storedDiscriminantPayload.eval x y z := by
  rcases discriminant_factor with ⟨he, hp, hq, hcoeff⟩
  rcases fits_degree_box_sound hp with ⟨hp0, hp1, hp2⟩
  rcases fits_degree_box_sound hq with ⟨hq0, hq1, hq2⟩
  exact ScaledPolynomial.eval_eq_of_tensor storedDiscriminant
    storedDiscriminantPayload he hp0 hp1 hp2 hq0 hq1 hq2 hcoeff x y z

private theorem negative_p_margin_nonnegative_aux (x y z : I) :
    0 ≤ negativePMargin.eval x y z := by
  rcases negative_p_margin_certificate with ⟨hfit, htree⟩
  rcases fits_degree_box_sound hfit with ⟨h0, h1, h2⟩
  exact negativePMargin.eval_nonnegative_of_tensor h0 h1 h2 .leaf htree x y z

private theorem discriminant_margin_nonnegative_aux (x y z : I) :
    0 ≤ discriminantMargin.eval x y z := by
  rcases discriminant_margin_certificate with ⟨hfit, htree⟩
  rcases fits_degree_box_sound hfit with ⟨h0, h1, h2⟩
  exact discriminantMargin.eval_nonnegative_of_tensor h0 h1 h2 .leaf htree x y z

private theorem stored_negative_p_lower_aux (x y z : I) :
    (9 / 100 : ℝ) ≤ storedNegativeP.eval x y z := by
  have h := negative_p_margin_nonnegative_aux x y z
  simp only [negativePMargin, ScaledPolynomial.eval_add_notation,
    ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_neg_notation,
    ScaledPolynomial.eval_dyadic] at h
  norm_num at h ⊢
  linarith

private theorem stored_discriminant_lower_aux (x y z : I) :
    (9 / 1000 : ℝ) ≤ storedDiscriminantPayload.eval x y z := by
  have h := discriminant_margin_nonnegative_aux x y z
  simp only [discriminantMargin, ScaledPolynomial.eval_add_notation,
    ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_neg_notation,
    ScaledPolynomial.eval_dyadic] at h
  norm_num at h ⊢
  linarith

/-- The nominal negative P has margin `9/100` throughout the first radius bin. -/
theorem nominal_negative_p_lower (x y z : I) :
    (9 / 100 : ℝ) ≤ -formula.p.eval x y z := by
  have heq := negative_p_eval_eq_aux x y z
  have hlower := stored_negative_p_lower_aux x y z
  rw [negativeP, ScaledPolynomial.eval_neg_notation] at heq
  linarith

/-- The nominal discriminant has margin `9/1000` throughout the first radius bin. -/
theorem nominal_discriminant_lower (x y z : I) :
    (9 / 1000 : ℝ) ≤ formula.p.eval x y z ^ 2 -
      formula.q.eval x y z ^ 2 * formula.radicand.eval x y z := by
  have hp := negative_p_eval_eq_aux x y z
  have hq := q_eval_eq_aux x y z
  have hr := radicand_eval_eq_aux x y z
  have hd := discriminant_payload_eval_eq_aux x y z
  have hlower := stored_discriminant_lower_aux x y z
  rw [negativeP, ScaledPolynomial.eval_neg_notation] at hp
  simp only [storedDiscriminant, ScaledPolynomial.eval_add_notation,
    ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_neg_notation] at hd
  rw [← hd] at hlower
  have hp2 : formula.p.eval x y z ^ 2 = storedNegativeP.eval x y z ^ 2 := by
    calc
      formula.p.eval x y z ^ 2 = (-formula.p.eval x y z) ^ 2 := by ring
      _ = storedNegativeP.eval x y z ^ 2 := congrArg (· ^ 2) hp
  rw [hq, hr, hp2]
  simpa only [pow_two, sub_eq_add_neg, mul_assoc] using hlower

end

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
