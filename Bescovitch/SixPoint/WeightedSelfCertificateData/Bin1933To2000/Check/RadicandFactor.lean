/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Payload.QRadicand
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R00
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R01
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R02
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R03
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R04
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R05
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R06
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R07
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R08
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R09
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R10
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R11
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.RF.R12
import Mathlib.Tactic.FinCases

/-!
# Exact radicand coefficient check
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

open DyadicTrivariatePolynomial

private theorem radicand_coefficients :
    ∀ i j k, powerTensor formula.radicand.numerator i j k =
      powerTensor storedRadicand.numerator i j k := by
  intro i
  fin_cases i
  · exact tensor_row_eq_sound radicand_factor_row_00
  · exact tensor_row_eq_sound radicand_factor_row_01
  · exact tensor_row_eq_sound radicand_factor_row_02
  · exact tensor_row_eq_sound radicand_factor_row_03
  · exact tensor_row_eq_sound radicand_factor_row_04
  · exact tensor_row_eq_sound radicand_factor_row_05
  · exact tensor_row_eq_sound radicand_factor_row_06
  · exact tensor_row_eq_sound radicand_factor_row_07
  · exact tensor_row_eq_sound radicand_factor_row_08
  · exact tensor_row_eq_sound radicand_factor_row_09
  · exact tensor_row_eq_sound radicand_factor_row_10
  · exact tensor_row_eq_sound radicand_factor_row_11
  · exact tensor_row_eq_sound radicand_factor_row_12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem radicand_exponent :
    formula.radicand.exponent = storedRadicand.exponent := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem radicand_source_fits :
    fitsDegreeBox formula.radicand.numerator = true := by
  with_unfolding_all rfl

private theorem stored_radicand_fits :
    fitsDegreeBox storedRadicand.numerator = true := by
  with_unfolding_all rfl

/-- The computed radicand has the stored scaled coefficients. -/
theorem radicand_factor :
    formula.radicand.exponent = storedRadicand.exponent ∧
      fitsDegreeBox formula.radicand.numerator = true ∧
      fitsDegreeBox storedRadicand.numerator = true ∧
      ∀ i j k, powerTensor formula.radicand.numerator i j k =
        powerTensor storedRadicand.numerator i j k :=
  ⟨radicand_exponent, radicand_source_fits,
    stored_radicand_fits, radicand_coefficients⟩

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
