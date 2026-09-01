/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Challenge: the planar Besicovitch threshold

This file contains every transparent definition occurring in the theorem statement.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory NNReal Topology

namespace Bescovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The lower one-density of `s` at `x`, normalized by the diameter `2 * r` of a ball. -/
def lowerOneDensity (s : Set X) (x : X) : ℝ≥0∞ :=
  liminf (fun r : ℝ ↦ μH[1] (s ∩ Metric.ball x r) / ENNReal.ofReal (2 * r))
    (nhdsWithin 0 (Ioi 0))

/-- A set is countably one-rectifiable if Lipschitz curves cover it up to Hausdorff null measure. -/
def IsCountablyOneRectifiable (s : Set X) : Prop :=
  ∃ f : ℕ → ℝ → X,
    (∀ i, ∃ K : ℝ≥0, LipschitzWith K (f i)) ∧ μH[1] (s \ ⋃ i, range (f i)) = 0

/-- Every finite-measure set with lower density at least `β` is one-rectifiable. -/
def ForcesOneRectifiability (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (β : ℝ≥0∞) : Prop :=
  ∀ s : Set X, MeasurableSet s → μH[1] s < ∞ →
    (∀ᵐ x ∂μH[1].restrict s, β ≤ lowerOneDensity s x) →
      IsCountablyOneRectifiable s

/-- The least nonnegative real threshold forcing one-rectifiability in `X`. -/
def sigmaOne (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : ℝ :=
  sInf {β : ℝ | 0 ≤ β ∧ ForcesOneRectifiability X (ENNReal.ofReal β)}

/-- The planar one-dimensional rectifiability threshold is below the previous record. -/
theorem sigma_one_plane_le_699_div_1000 :
    sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 699 / 1000 := by
  sorry

end Bescovitch
