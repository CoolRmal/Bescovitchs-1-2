/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Measure.Density

/-!
# One-dimensional rectifiability

The definitions use countably many global Lipschitz images of the real line, modulo a null set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped MeasureTheory NNReal

namespace Bescovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A set is countably one-rectifiable if Lipschitz curves cover it up to Hausdorff null measure. -/
def IsCountablyOneRectifiable (s : Set X) : Prop :=
  ∃ f : ℕ → ℝ → X,
    (∀ i, ∃ K : ℝ≥0, LipschitzWith K (f i)) ∧ μH[1] (s \ ⋃ i, range (f i)) = 0

/-- A set is purely one-unrectifiable if it meets every rectifiable set in a null set. -/
def IsPurelyOneUnrectifiable (s : Set X) : Prop :=
  ∀ t, IsCountablyOneRectifiable t → μH[1] (s ∩ t) = 0

end Bescovitch
