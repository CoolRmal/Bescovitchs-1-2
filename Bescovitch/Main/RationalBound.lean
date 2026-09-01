/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Main.Bound
public import Bescovitch.SixPoint.EndpointPacking
public import Bescovitch.SixPoint.WeightedMixedRootAssembly

/-!
# The planar bound from the ten mixed root boxes

Above the sharp constant the self inequality is no longer needed to close the equality chart, so
the ten strict mixed root boxes are the whole analytic input.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- The ten mixed root boxes bound the planar rectifiability threshold. -/
theorem sigmaOne_plane_le_barS_of_mixed_root_box_bounds
    (h00NegNeg : WeightedMixedRootBoxBound false false (-1) (-1))
    (h00PosNeg : WeightedMixedRootBoxBound false false 1 (-1))
    (h00PosPos : WeightedMixedRootBoxBound false false 1 1)
    (h01NegNeg : WeightedMixedRootBoxBound false true (-1) (-1))
    (h01PosNeg : WeightedMixedRootBoxBound false true 1 (-1))
    (h10PosNeg : WeightedMixedRootBoxBound true false 1 (-1))
    (h10PosPos : WeightedMixedRootBoxBound true false 1 1)
    (h11NegNeg : WeightedMixedRootBoxBound true true (-1) (-1))
    (h11PosNeg : WeightedMixedRootBoxBound true true 1 (-1))
    (h11PosPos : WeightedMixedRootBoxBound true true 1 1) :
    sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 6934 / 10000 := by
  have hchart : WeightedLensChartBound :=
    weightedLensChartBound_of_canonical_mixed_root_box_bounds h00NegNeg h00PosNeg h00PosPos
      h01NegNeg h01PosNeg h10PosNeg h10PosPos h11NegNeg h11PosNeg h11PosPos
  have hfinite : SixPointFiniteProperty barS :=
    sixPointFiniteProperty_barS_of_weightedGeometricBound
      (weightedGeometricBound_of_lensChartBound hchart)
  have hbound := hfinite.sigmaOne_plane_le barS_pos barS_lt_one
  rwa [barS_eq] at hbound

end Bescovitch
