/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedCertificateData.Cap1Cap0PosNeg
public import Bescovitch.SixPoint.WeightedMixedStrictCertificate

/-!
# Mixed root-box certificate for the chart `(1, 0, 1, -1)`
-/

@[expose] public section

namespace Bescovitch

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The adaptive tree certifies the mixed inequality on the chart `(1, 0, 1, -1)`. -/
theorem weightedMixedRootBoxBound_10PosNeg :
    WeightedMixedRootBoxBound true false 1 (-1) :=
  weightedMixedRootBoxBound_of_tree_check true false 1 (-1)
    weightedMixedTreeCap1Cap0SidePosSideNeg (by with_unfolding_all rfl)

end Bescovitch
