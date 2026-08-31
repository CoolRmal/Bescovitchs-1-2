/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Geometry.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Convex enlargements

This file records the two elementary enlargements used in the continuum argument: thickening a
set by a multiple of its diameter, and replacing an open set by its open convex hull.
-/

@[expose] public section

noncomputable section

open Bornology Set

namespace Bescovitch

/-- The `p`-diameter thickening of a set. -/
def diameterThickening (p : ℝ) (s : Set Plane) : Set Plane :=
  Metric.thickening (p * Metric.diam s) s

/-- Diameter thickenings are open. -/
theorem isOpen_diameterThickening (p : ℝ) (s : Set Plane) :
    IsOpen (diameterThickening p s) :=
  Metric.isOpen_thickening

/-- A nonnegative `p`-diameter thickening has diameter at most `(2p + 1)` times the original. -/
theorem diam_diameterThickening_le {p : ℝ} (hp : 0 ≤ p) (s : Set Plane) :
    Metric.diam (diameterThickening p s) ≤ (2 * p + 1) * Metric.diam s := by
  rw [diameterThickening]
  calc
    Metric.diam (Metric.thickening (p * Metric.diam s) s) ≤
        Metric.diam s + 2 * (p * Metric.diam s) :=
      Metric.diam_thickening_le s (mul_nonneg hp Metric.diam_nonneg)
    _ = (2 * p + 1) * Metric.diam s := by ring

/-- A set is contained in every positive-radius diameter thickening. -/
theorem subset_diameterThickening {p : ℝ} {s : Set Plane}
    (hpositive : 0 < p * Metric.diam s) : s ⊆ diameterThickening p s := by
  exact Metric.self_subset_thickening hpositive s

/-- A bounded set meeting `s` lies in the `p`-diameter thickening of `s` when its diameter is
smaller than the thickening radius. -/
theorem subset_diameterThickening_of_inter_nonempty {u s : Set Plane} {p : ℝ}
    (hu : IsBounded u) (hus : (u ∩ s).Nonempty)
    (hdiam : Metric.diam u < p * Metric.diam s) : u ⊆ diameterThickening p s := by
  obtain ⟨y, hyu, hys⟩ := hus
  intro x hxu
  rw [diameterThickening, Metric.mem_thickening_iff]
  exact ⟨y, hys, (Metric.dist_le_diam_of_mem hu hxu hyu).trans_lt hdiam⟩

/-- The interior of the convex hull of a set. -/
def openConvexHull (s : Set Plane) : Set Plane :=
  interior (convexHull ℝ s)

/-- The open convex hull is open. -/
theorem isOpen_openConvexHull (s : Set Plane) : IsOpen (openConvexHull s) :=
  isOpen_interior

/-- The open convex hull is convex. -/
theorem convex_openConvexHull (s : Set Plane) : Convex ℝ (openConvexHull s) :=
  (convex_convexHull ℝ s).interior

/-- An open set is contained in its open convex hull. -/
theorem subset_openConvexHull {s : Set Plane} (hs : IsOpen s) : s ⊆ openConvexHull s := by
  exact hs.subset_interior_iff.mpr (subset_convexHull ℝ s)

/-- Passing from an open set to its open convex hull does not change its diameter. -/
theorem diam_openConvexHull {s : Set Plane} (hs : IsOpen s) :
    Metric.diam (openConvexHull s) = Metric.diam s := by
  have hsubset : s ⊆ openConvexHull s := subset_openConvexHull hs
  by_cases hbounded : IsBounded s
  · have hconvexHull_bounded : IsBounded (convexHull ℝ s) := by simpa using hbounded
    have hopen_bounded : IsBounded (openConvexHull s) :=
      hconvexHull_bounded.subset interior_subset
    apply le_antisymm
    · calc
        Metric.diam (openConvexHull s) ≤ Metric.diam (convexHull ℝ s) :=
          Metric.diam_mono interior_subset hconvexHull_bounded
        _ = Metric.diam s := convexHull_diam s
    · exact Metric.diam_mono hsubset hopen_bounded
  · have hopen_unbounded : ¬IsBounded (openConvexHull s) := fun h ↦ hbounded (h.subset hsubset)
    rw [Metric.diam_eq_zero_of_unbounded hbounded,
      Metric.diam_eq_zero_of_unbounded hopen_unbounded]

end Bescovitch
