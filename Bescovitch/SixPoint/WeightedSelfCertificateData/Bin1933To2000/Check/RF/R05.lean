/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Payload.QRadicand

/-!
# Exact radicand coefficient row 5
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

open DyadicTrivariatePolynomial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- This row of the computed radicand agrees with its stored coefficients. -/
theorem radicand_factor_row_05 :
    tensorRowEq formula.radicand.numerator storedRadicand.numerator 5 = true := by
  with_unfolding_all rfl

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
