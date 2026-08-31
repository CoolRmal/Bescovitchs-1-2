/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Rectifiability.Defs

/-!
# The one-dimensional rectifiability threshold

This file defines the density implication and its optimal threshold in a metric space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace Bescovitch

variable (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- At threshold `β`, every finite-measure set with lower density at least `β` is rectifiable. -/
def ForcesOneRectifiability (β : ℝ) : Prop :=
  ∀ s : Set X, MeasurableSet s → μH[1] s < ∞ →
    (∀ᵐ x ∂μH[1].restrict s, ENNReal.ofReal β ≤ lowerOneDensity s x) →
      IsCountablyOneRectifiable s

/-- The least nonnegative lower-density threshold forcing one-rectifiability in `X`. -/
def sigmaOne : ℝ :=
  sInf {β : ℝ | 0 ≤ β ∧ ForcesOneRectifiability X β}

end Bescovitch
