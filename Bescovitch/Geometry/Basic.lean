/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Plane geometry

This file fixes the Euclidean plane used throughout the formalization.
-/

@[expose] public section

namespace Bescovitch

/-- The Euclidean plane with its usual ℓ² metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

end Bescovitch
