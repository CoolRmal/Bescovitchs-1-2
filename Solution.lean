/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Besicovitch.Certificates.EndpointBridge
public import Besicovitch.Example.LowerBound
public import Besicovitch.Main.RationalBound

/-!
# Solution: the planar Besicovitch threshold

The planar bound follows from the six-point finite property at `6934/10000`, which the thirty
Gram certificates establish.  The same argument forces one-rectifiability at every threshold
above that constant.  The companion bound records that the exact six-point endpoint lies below the
same rational number.
-/

@[expose] public section

open scoped ENNReal

namespace Besicovitch

/-- Every threshold strictly above `6934 / 10000` forces one-rectifiability in the plane. -/
theorem forcesOneRectifiability_plane_of_gt (β : ℝ) (hβ : 6934 / 10000 < β) :
    ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal β) :=
  forcesOneRectifiability_plane_of_barS_lt (by rw [barS_eq]; exact hβ)

/-- The planar threshold is at least `1 / 2`: Besicovitch's purely unrectifiable graph has lower
density `1 / 2`. -/
theorem one_half_le_sigma_one_plane :
    (1 / 2 : ℝ) ≤ sigmaOne (EuclideanSpace ℝ (Fin 2)) :=
  Example.one_half_le_sigmaOne_plane

/-- The planar threshold is at most `6934 / 10000`, below the published record `7 / 10`. -/
theorem sigma_one_plane_le_6934_div_10000 :
    sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 6934 / 10000 :=
  sigmaOne_plane_le_barS

/-- The exact six-point endpoint is at most `0.6934`. -/
theorem sStar_le_6934_div_10000 : sStar ≤ 6934 / 10000 :=
  sStar_le_6934_div_10000_certified

end Besicovitch
