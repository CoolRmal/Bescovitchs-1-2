/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Payload.Discriminant

/-!
# Bernstein sign row 7 for the discriminant
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

open DyadicTrivariatePolynomial

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- This Bernstein row for the discriminant margin is nonnegative. -/
theorem discriminant_margin_row_07 :
    IntegerTensorBernstein.rowNonnegative
      (IntegerTensorBernstein.convertPowerTensor
        (powerTensor discriminantMargin.numerator)) 7 = true := by
  with_unfolding_all rfl

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
