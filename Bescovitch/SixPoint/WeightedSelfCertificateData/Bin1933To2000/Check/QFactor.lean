/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Payload.QRadicand
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R00
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R01
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R02
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R03
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R04
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R05
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R06
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R07
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R08
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R09
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R10
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R11
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Check.QF.R12
import Mathlib.Tactic.FinCases

/-!
# Exact polynomial `Q` coefficient check
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

open DyadicTrivariatePolynomial

private theorem q_coefficients :
    ∀ i j k, powerTensor formula.q.numerator i j k =
      powerTensor storedQ.numerator i j k := by
  intro i
  fin_cases i
  · exact tensor_row_eq_sound q_factor_row_00
  · exact tensor_row_eq_sound q_factor_row_01
  · exact tensor_row_eq_sound q_factor_row_02
  · exact tensor_row_eq_sound q_factor_row_03
  · exact tensor_row_eq_sound q_factor_row_04
  · exact tensor_row_eq_sound q_factor_row_05
  · exact tensor_row_eq_sound q_factor_row_06
  · exact tensor_row_eq_sound q_factor_row_07
  · exact tensor_row_eq_sound q_factor_row_08
  · exact tensor_row_eq_sound q_factor_row_09
  · exact tensor_row_eq_sound q_factor_row_10
  · exact tensor_row_eq_sound q_factor_row_11
  · exact tensor_row_eq_sound q_factor_row_12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem q_exponent :
    formula.q.exponent = storedQ.exponent := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem q_source_fits :
    fitsDegreeBox formula.q.numerator = true := by
  with_unfolding_all rfl

private theorem stored_q_fits :
    fitsDegreeBox storedQ.numerator = true := by
  with_unfolding_all rfl

/-- The computed polynomial `Q` has the stored scaled coefficients. -/
theorem q_factor :
    formula.q.exponent = storedQ.exponent ∧
      fitsDegreeBox formula.q.numerator = true ∧
      fitsDegreeBox storedQ.numerator = true ∧
      ∀ i j k, powerTensor formula.q.numerator i j k =
        powerTensor storedQ.numerator i j k :=
  ⟨q_exponent, q_source_fits,
    stored_q_fits, q_coefficients⟩

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
