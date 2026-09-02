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

namespace Besicovitch

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

/-- The infimum of the nonnegative real thresholds forcing one-rectifiability in `X`.

It is an infimum, not a minimum: attainment at `sigmaOne X` itself is not claimed.  Lean's
`sInf` on `ℝ` returns `0` for the empty set and for a set with no lower bound, so this number
is meaningful only once the admissible set is shown nonempty and bounded below.  The theorems
below establish both, so the bound on `sigmaOne` cannot hold vacuously. -/
def sigmaOne (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : ℝ :=
  sInf {β : ℝ | 0 ≤ β ∧ ForcesOneRectifiability X (ENNReal.ofReal β)}

/-- Forcing is monotone in the threshold: a larger density hypothesis is a stronger one.

Consequently the admissible set is closed upwards and, once nonempty, has no upper bound.  So
"bounded above" is not the condition that protects `sigmaOne` from a junk value; bounded below
is, and that is `admissibleThresholds_bddBelow`. -/
theorem forcesOneRectifiability_mono {β β' : ℝ≥0∞} (h : β ≤ β')
    (hβ : ForcesOneRectifiability X β) : ForcesOneRectifiability X β' := by
  sorry

/-- The admissible thresholds are bounded below, by `0`.

With nonemptiness this is exactly what makes `sInf` return the true infimum; otherwise
`Real.sInf_of_not_bddBelow` would give `0` regardless of the set. -/
theorem admissibleThresholds_bddBelow :
    BddBelow {β : ℝ | 0 ≤ β ∧ ForcesOneRectifiability X (ENNReal.ofReal β)} := by
  sorry

/-- Every threshold strictly above `6934 / 10000` forces one-rectifiability in the plane.

This is the substantive content behind the bound on `sigmaOne`: it exhibits genuine admissible
thresholds instead of relying on the value of an infimum.  The argument produces thresholds
with a strict margin, so nothing is claimed at the constant itself. -/
theorem forcesOneRectifiability_plane_of_gt (β : ℝ) (hβ : 6934 / 10000 < β) :
    ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal β) := by
  sorry

/-- The planar admissible set is nonempty.

Without this, `sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 6934 / 10000` could hold vacuously, since
`Real.sInf_empty : sInf ∅ = 0`. -/
theorem admissibleThresholds_plane_nonempty :
    {β : ℝ | 0 ≤ β ∧
      ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal β)}.Nonempty := by
  sorry

/-- `sigmaOne` of the plane is the greatest lower bound of its admissible thresholds.

This is the statement that the number is not a junk value: it is the genuine infimum of a
nonempty set bounded below, the two conditions under which Lean's real `sInf` agrees with the
mathematical infimum. -/
theorem isGLB_sigmaOne_plane :
    IsGLB {β : ℝ | 0 ≤ β ∧
        ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal β)}
      (sigmaOne (EuclideanSpace ℝ (Fin 2))) := by
  sorry

/-- The planar one-dimensional rectifiability threshold is below the published record `7/10`. -/
theorem sigma_one_plane_le_6934_div_10000 :
    sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 6934 / 10000 := by
  sorry

end Besicovitch
