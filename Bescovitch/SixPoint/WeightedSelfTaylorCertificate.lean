/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateCore
import Bescovitch.SixPoint.WeightedSelfCertificateData.Boxes
import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Perturbation

/-!
# Weighted-self Taylor certificate on `[3/5, 7/10]`
-/

@[expose] public section

open scoped unitInterval

namespace Bescovitch

open WeightedSelfTaylorBin4

/-- The ordinary weighted-self estimate on the radius bin `[3/5, 7/10]`. -/
theorem weightedSelfRadiusBinBound_three_fifths_seven_tenths :
    WeightedSelfRadiusBinBound (3 / 5) (7 / 10) := by
  apply weightedSelfRadiusBinBound_of_real_chart_signs
  · norm_num
  · norm_num
  · exact bin4_exact_negative_p
  · intro x y z
    simpa [weightedSelfBinLower, weightedSelfBinUpper] using
      weightedSelfPolynomialQ_nonneg_on_certificate_bin 3 x y z
  · exact bin4_exact_discriminant_nonnegative

end Bescovitch
