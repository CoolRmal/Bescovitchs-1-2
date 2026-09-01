/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Payload.NegativeP
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R00
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R01
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R02
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R03
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R04
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R05
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R06
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R07
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R08
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R09
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R10
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R11
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.PF.R12
import Mathlib.Tactic.FinCases

/-!
# Exact negative-P coefficient check
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

open DyadicTrivariatePolynomial

private theorem negative_p_coefficients :
    ∀ i j k, powerTensor negativeP.numerator i j k =
      powerTensor storedNegativeP.numerator i j k := by
  intro i
  fin_cases i
  · exact tensor_row_eq_sound negative_p_factor_row_00
  · exact tensor_row_eq_sound negative_p_factor_row_01
  · exact tensor_row_eq_sound negative_p_factor_row_02
  · exact tensor_row_eq_sound negative_p_factor_row_03
  · exact tensor_row_eq_sound negative_p_factor_row_04
  · exact tensor_row_eq_sound negative_p_factor_row_05
  · exact tensor_row_eq_sound negative_p_factor_row_06
  · exact tensor_row_eq_sound negative_p_factor_row_07
  · exact tensor_row_eq_sound negative_p_factor_row_08
  · exact tensor_row_eq_sound negative_p_factor_row_09
  · exact tensor_row_eq_sound negative_p_factor_row_10
  · exact tensor_row_eq_sound negative_p_factor_row_11
  · exact tensor_row_eq_sound negative_p_factor_row_12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_exponent :
    negativeP.exponent = storedNegativeP.exponent := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem negative_p_source_fits : fitsDegreeBox negativeP.numerator = true := by
  with_unfolding_all rfl

private theorem stored_negative_p_fits :
    fitsDegreeBox storedNegativeP.numerator = true := by
  with_unfolding_all rfl

/-- The computed polynomial `-P` has the stored scaled coefficients. -/
theorem negative_p_factor :
    negativeP.exponent = storedNegativeP.exponent ∧
      fitsDegreeBox negativeP.numerator = true ∧
      fitsDegreeBox storedNegativeP.numerator = true ∧
      ∀ i j k, powerTensor negativeP.numerator i j k =
        powerTensor storedNegativeP.numerator i j k :=
  ⟨negative_p_exponent, negative_p_source_fits, stored_negative_p_fits,
    negative_p_coefficients⟩

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
