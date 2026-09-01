/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateCore
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.ExactNegativeP
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.ExactDiscriminant
import Bescovitch.SixPoint.WeightedSelfCertificateData.Boxes

/-!
# Exact weighted-self certificate on `[1933/5000, 2/5]`
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths

open Internal

/-- The weighted-self estimate holds on the radius interval `[1933/5000, 2/5]`. -/
theorem weightedSelfRadiusBinBound_1933_div_5000_two_fifths :
    WeightedSelfRadiusBinBound (1933 / 5000) (2 / 5) := by
  apply weightedSelfRadiusBinBound_of_real_chart_signs
    (1933 / 5000) (2 / 5) (by norm_num) (by norm_num)
  · exact exact_negative_p
  · intro x y z
    convert weightedSelfPolynomialQ_nonneg_on_certificate_bin (0 : Fin 7) x y z using 1
    all_goals norm_num [weightedSelfBinLower, weightedSelfBinUpper]
  · exact exact_discriminant_nonnegative

end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
