/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Payload.NegativeP
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R00
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R01
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R02
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R03
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R04
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R05
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R06
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R07
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R08
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R09
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R10
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R11
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PS.R12
import Mathlib.Tactic.FinCases

/-!
# Bernstein sign certificate for negative P
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

open DyadicTrivariatePolynomial

private theorem negative_p_margin_coefficients_nonnegative :
    ∀ i j k, 0 ≤ IntegerTensorBernstein.convertPowerTensor
      (powerTensor negativePMargin.numerator) i j k := by
  intro i
  fin_cases i
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_00
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_01
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_02
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_03
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_04
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_05
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_06
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_07
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_08
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_09
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_10
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_11
  · exact IntegerTensorBernstein.rowNonnegative_sound negative_p_margin_row_12

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_margin_fits :
    fitsDegreeBox negativePMargin.numerator = true := by
  with_unfolding_all rfl

/-- The `-P` margin fits the degree box and has nonnegative Bernstein coefficients. -/
theorem negative_p_margin_certificate :
    fitsDegreeBox negativePMargin.numerator = true ∧
      IntegerTensorBernstein.SubdivisionNonnegative .leaf
        (IntegerTensorBernstein.convertPowerTensor
          (powerTensor negativePMargin.numerator)) :=
  ⟨negative_p_margin_fits, negative_p_margin_coefficients_nonnegative⟩

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
