/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedCertificateData.Cap0Cap0PosPos
public import Bescovitch.SixPoint.WeightedMixedStrictCertificate

/-!
# Mixed root-box certificate for the chart `(0, 0, 1, 1)`
-/

@[expose] public section

namespace Bescovitch

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The adaptive tree certifies the mixed inequality on the chart `(0, 0, 1, 1)`. -/
theorem weightedMixedRootBoxBound_00PosPos :
    WeightedMixedRootBoxBound false false 1 1 :=
  weightedMixedRootBoxBound_of_tree_check false false 1 1
    weightedMixedTreeCap0Cap0SidePosSidePos (by with_unfolding_all rfl)

end Bescovitch
