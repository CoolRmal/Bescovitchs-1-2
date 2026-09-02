/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Besicovitch.Certificates.EndpointBridge
public import Besicovitch.Main.RationalBound

/-!
# Solution: the planar Besicovitch threshold

The planar bound follows from the six-point finite property at `6934/10000`, which the thirty
Gram certificates establish.  The same argument forces one-rectifiability at every threshold
above that constant, which makes the admissible set nonempty; with the trivial lower bound `0`
this shows `sigmaOne` is the genuine infimum rather than the value Lean assigns to an empty or
unbounded set.  The companion bound records that the exact six-point endpoint lies below the
same rational number.
-/

@[expose] public section

open scoped ENNReal

namespace Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Forcing is monotone in the threshold: a larger density hypothesis is a stronger one. -/
theorem forcesOneRectifiability_mono {β β' : ℝ≥0∞} (h : β ≤ β')
    (hβ : ForcesOneRectifiability X β) : ForcesOneRectifiability X β' :=
  ForcesOneRectifiability.mono X h hβ

/-- The admissible thresholds are bounded below, by `0`. -/
theorem admissibleThresholds_bddBelow :
    BddBelow {β : ℝ | 0 ≤ β ∧ ForcesOneRectifiability X (ENNReal.ofReal β)} :=
  bddBelow_admissibleThresholds X

/-- Every threshold strictly above `6934 / 10000` forces one-rectifiability in the plane. -/
theorem forcesOneRectifiability_plane_of_gt (β : ℝ) (hβ : 6934 / 10000 < β) :
    ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal β) :=
  forcesOneRectifiability_plane_of_barS_lt (by rw [barS_eq]; exact hβ)

/-- The planar admissible set is nonempty. -/
theorem admissibleThresholds_plane_nonempty :
    {β : ℝ | 0 ≤ β ∧
      ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal β)}.Nonempty :=
  ⟨7 / 10, by norm_num, forcesOneRectifiability_plane_of_gt _ (by norm_num)⟩

/-- `sigmaOne` of the plane is the greatest lower bound of its admissible thresholds. -/
theorem isGLB_sigmaOne_plane :
    IsGLB {β : ℝ | 0 ≤ β ∧
        ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal β)}
      (sigmaOne (EuclideanSpace ℝ (Fin 2))) := by
  unfold sigmaOne
  exact isGLB_csInf admissibleThresholds_plane_nonempty admissibleThresholds_bddBelow

/-- The planar one-dimensional rectifiability threshold is below the published record `7/10`. -/
theorem sigma_one_plane_le_6934_div_10000 :
    sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 6934 / 10000 :=
  sigmaOne_plane_le_barS

/-- The exact six-point endpoint is at most `0.6934`. -/
theorem sStar_le_6934_div_10000 : sStar ≤ 6934 / 10000 :=
  sStar_le_6934_div_10000_certified

end Besicovitch
