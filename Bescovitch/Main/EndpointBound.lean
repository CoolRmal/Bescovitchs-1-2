/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Main.Bound
public import Bescovitch.SixPoint.EndpointPacking

/-!
# The planar bound from the weighted endpoint inequality

This module joins the finite six-point theorem to the geometric-measure-theory transfer.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- The weighted geometric bound implies the desired bound for the planar density threshold. -/
theorem sigmaOne_plane_le_sStar_of_weightedGeometricBound
    (hweighted : WeightedGeometricBound) : sigmaOne Plane ≤ sStar :=
  sigmaOne_plane_le_sStar_of_sixPointFiniteProperty
    (sixPointFiniteProperty_sStar_of_weightedGeometricBound hweighted)

end Bescovitch
