/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Payload.Discriminant
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R00
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R01
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R02
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R03
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R04
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R05
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R06
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R07
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R08
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R09
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R10
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R11
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DS.R12
import Mathlib.Tactic.FinCases

/-!
# Bernstein sign certificate for the discriminant
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

open DyadicTrivariatePolynomial

private theorem discriminant_margin_coefficients_nonnegative :
    ∀ i j k, 0 ≤ IntegerTensorBernstein.convertPowerTensor
      (powerTensor discriminantMargin.numerator) i j k := by
  intro i
  fin_cases i
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_00
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_01
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_02
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_03
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_04
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_05
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_06
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_07
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_08
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_09
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_10
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_11
  · exact IntegerTensorBernstein.rowNonnegative_sound discriminant_margin_row_12

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem discriminant_margin_fits :
    fitsDegreeBox discriminantMargin.numerator = true := by
  with_unfolding_all rfl

/-- The discriminant margin fits the degree box and has nonnegative Bernstein coefficients. -/
theorem discriminant_margin_certificate :
    fitsDegreeBox discriminantMargin.numerator = true ∧
      IntegerTensorBernstein.SubdivisionNonnegative .leaf
        (IntegerTensorBernstein.convertPowerTensor
          (powerTensor discriminantMargin.numerator)) :=
  ⟨discriminant_margin_fits, discriminant_margin_coefficients_nonnegative⟩

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
