/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Geometry.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# One-dimensional lower density

This file defines the normalization used in the Besicovitch one-half problem.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace Bescovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The lower one-density of `s` at `x`, normalized by the diameter `2 * r` of a ball. -/
def lowerOneDensity (s : Set X) (x : X) : ℝ≥0∞ :=
  liminf (fun r : ℝ ↦ μH[1] (s ∩ Metric.ball x r) / ENNReal.ofReal (2 * r))
    (nhdsWithin 0 (Ioi 0))

end Bescovitch
