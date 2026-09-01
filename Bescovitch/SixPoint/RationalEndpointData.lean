/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.EndpointTightBounds
public import Bescovitch.SixPoint.EndpointWeights
public import Bescovitch.SixPoint.RationalChord

/-!
# Rational tangent data for the retargeted argument

The self majorant is taken tangent to the norm at an auxiliary distance `B`.  At the exact
endpoint that distance is the second coordinate of the isolated endpoint pair; away from the
endpoint any nearby value will do, since the tangent is a valid upper bound wherever it is taken.
Choosing it rational removes the last dependence of the weighted layer on the exact endpoint.

The weight-reduction margin is restated at the rational chord.  It has room to spare there: the
second penalty grows with the chord, so enlarging the chord only helps.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- The rational auxiliary distance at which the self majorant is taken tangent. -/
def barB : ℝ := 2873744161801660 / 10 ^ 15

/-- The rational tangent distance lies in the isolation box of the exact one. -/
theorem barB_mem_isolation_box :
    2873744161801659 / 10 ^ 15 < barB ∧ barB < 2873744161801662 / 10 ^ 15 := by
  constructor <;> norm_num [barB]

/-- Both radicands of the rational tangent configuration are positive. -/
theorem barB_radicands_pos :
    0 < (barB ^ 2 - 1) / 2 ∧
      0 < (barB ^ 2 + (4 * barC ^ 2 - 2 * barC - barB) ^ 2) / 2 - barC ^ 2 := by
  constructor <;> norm_num [barB, barC]

/-- The rational chord leaves the weight-reduction margin. -/
theorem barC_weight_reduction_margin :
    2 + endpointMu ≤ weightedSecondPenalty barC endpointLambda endpointMu := by
  have hlambda := endpointLambda_tight_bounds.1
  have hmu := endpointMu_tight_bounds
  rw [weightedSecondPenalty]
  norm_num [barC] at hlambda hmu ⊢
  nlinarith [hmu.1, hmu.2, hlambda]

end Bescovitch
