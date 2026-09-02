/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.EndpointBridge
public import Bescovitch.Main.RationalBound

/-!
# Solution: the planar Besicovitch threshold

The planar bound follows from the six-point finite property at `6934/10000`, which the thirty
Gram certificates establish; the companion bound records that the exact six-point endpoint lies
below the same rational number.
-/

@[expose] public section

namespace Bescovitch

/-- The planar one-dimensional rectifiability threshold is below the previous record. -/
theorem sigma_one_plane_le_6934_div_10000 :
    sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 6934 / 10000 :=
  sigmaOne_plane_le_barS

/-- The exact six-point endpoint is at most `0.6934`. -/
theorem sStar_le_6934_div_10000 : sStar ≤ 6934 / 10000 :=
  sStar_le_6934_div_10000_certified

end Bescovitch
