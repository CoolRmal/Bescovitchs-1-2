/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Payload.Discriminant
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R00
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R01
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R02
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R03
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R04
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R05
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R06
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R07
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R08
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R09
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R10
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R11
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.DF.R12
import Mathlib.Tactic.FinCases

/-!
# Exact discriminant coefficient check
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

open DyadicTrivariatePolynomial

private theorem discriminant_coefficients :
    ∀ i j k, powerTensor storedDiscriminant.numerator i j k =
      powerTensor storedDiscriminantPayload.numerator i j k := by
  intro i
  fin_cases i
  · exact tensor_row_eq_sound discriminant_factor_row_00
  · exact tensor_row_eq_sound discriminant_factor_row_01
  · exact tensor_row_eq_sound discriminant_factor_row_02
  · exact tensor_row_eq_sound discriminant_factor_row_03
  · exact tensor_row_eq_sound discriminant_factor_row_04
  · exact tensor_row_eq_sound discriminant_factor_row_05
  · exact tensor_row_eq_sound discriminant_factor_row_06
  · exact tensor_row_eq_sound discriminant_factor_row_07
  · exact tensor_row_eq_sound discriminant_factor_row_08
  · exact tensor_row_eq_sound discriminant_factor_row_09
  · exact tensor_row_eq_sound discriminant_factor_row_10
  · exact tensor_row_eq_sound discriminant_factor_row_11
  · exact tensor_row_eq_sound discriminant_factor_row_12

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem discriminant_exponent :
    storedDiscriminant.exponent = storedDiscriminantPayload.exponent := by
  with_unfolding_all rfl

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem discriminant_source_fits :
    fitsDegreeBox storedDiscriminant.numerator = true := by
  with_unfolding_all rfl

private theorem discriminant_payload_fits :
    fitsDegreeBox storedDiscriminantPayload.numerator = true := by
  with_unfolding_all rfl

/-- The factored discriminant has the stored scaled power coefficients. -/
theorem discriminant_factor :
    storedDiscriminant.exponent = storedDiscriminantPayload.exponent ∧
      fitsDegreeBox storedDiscriminant.numerator = true ∧
      fitsDegreeBox storedDiscriminantPayload.numerator = true ∧
      ∀ i j k, powerTensor storedDiscriminant.numerator i j k =
        powerTensor storedDiscriminantPayload.numerator i j k :=
  ⟨discriminant_exponent, discriminant_source_fits, discriminant_payload_fits,
    discriminant_coefficients⟩

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
