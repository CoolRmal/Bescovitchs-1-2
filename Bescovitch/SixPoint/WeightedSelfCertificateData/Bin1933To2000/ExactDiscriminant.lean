/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateCore
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.NegativePError
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.NegativePMagnitudes
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.QError
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.RadicandError
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.NominalSigns

/-!
# Exact discriminant sign on `[1933/5000, 2/5]`
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

noncomputable section

open DyadicTrivariatePolynomial
open scoped unitInterval

private theorem discriminant_error (x y z : I) :
    |weightedSelfDiscriminant
        (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
        (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
        (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t (2 / 5) -
      (formula.p.eval x y z ^ 2 -
        formula.q.eval x y z ^ 2 * formula.radicand.eval x y z)| <
      (1 / 2 ^ 27 : ℝ) := by
  let exactData := weightedSelfRealFormula
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t (2 / 5)
  let p₀ := formula.p.eval x y z
  let q₀ := formula.q.eval x y z
  let r₀ := formula.radicand.eval x y z
  have hep : |exactData.p - p₀| < (7 / 10 ^ 10 : ℝ) := by
    simpa only [exactData, p₀] using exact_p_error x y z
  obtain ⟨hp, hp₀⟩ := p_magnitude_bounds x y z
  obtain ⟨heq, hq, hq₀⟩ := q_error_and_magnitude_bounds x y z
  obtain ⟨her, hr₀⟩ := radicand_error_and_nominal_magnitude x y z
  have hraw :=
    WeightedSelfApproximation.Approximation.discriminant_difference_abs_lt_of_bounds
    hp hp₀ hq hq₀ hr₀ hep heq her
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hbudget :
      ((483 / 100 + 483 / 100) * (7 / 10 ^ 10) +
        (227 / 100) ^ 2 * (7 / 10 ^ 12) +
        (29 / 500) * (227 / 100 + 227 / 100) * (7 / 10 ^ 11) : ℝ) <
        1 / 2 ^ 27 := by
    norm_num
  have hraw' : |(exactData.p ^ 2 - exactData.q ^ 2 * exactData.radicand) -
      (p₀ ^ 2 - q₀ ^ 2 * r₀)| < (1 / 2 ^ 27 : ℝ) := hraw.trans hbudget
  have hrPos := weightedSelfRealChart_first_pos
    (lower := (1933 / 5000 : ℝ)) (upper := (2 / 5 : ℝ))
    (z := (z : ℝ)) (by norm_num) (by norm_num) x.property y.property
  have hformula := weightedSelfRealFormula_eq_weightedSelf
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t (2 / 5) hrPos.ne'
  dsimp only [exactData, p₀, q₀, r₀] at hraw'
  rw [hformula.1, hformula.2.1, hformula.2.2] at hraw'
  simpa only [weightedSelfDiscriminant] using hraw'

/-- The exact discriminant is nonnegative throughout this affine cube. -/
theorem exact_discriminant_nonnegative (x y z : I) :
    0 ≤ weightedSelfDiscriminant
      (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
      (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
      (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t (2 / 5) := by
  have hnominal := nominal_discriminant_lower x y z
  have herror := discriminant_error x y z
  have hlower := neg_lt_of_abs_lt herror
  norm_num at hlower ⊢
  linarith

end

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
