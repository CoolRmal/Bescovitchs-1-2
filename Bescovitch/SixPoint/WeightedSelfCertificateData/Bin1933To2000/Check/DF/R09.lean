/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Payload.Discriminant

/-!
# Exact discriminant coefficient row 9
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

open DyadicTrivariatePolynomial

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- This discriminant row agrees with its stored power coefficients. -/
theorem discriminant_factor_row_09 :
    tensorRowEq storedDiscriminant.numerator
      storedDiscriminantPayload.numerator 9 = true := by
  with_unfolding_all rfl

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
