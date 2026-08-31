/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# The six-point endpoint

This file gives an exact radical-system definition of the constant `sStar`.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- The isolated radical system whose first coordinate is twice the six-point endpoint. -/
def IsEndpointPair (c B : ℝ) : Prop :=
  let D := 4 * c ^ 2 - 2 * c - B
  let b := (2 * B - 3 * c ^ 2 + 2 * c - 1) / (c + 1)
  let A := Real.sqrt ((B ^ 2 - 1) / 2)
  let C := Real.sqrt ((B ^ 2 + D ^ 2) / 2 - c ^ 2)
  let x := (5 - B ^ 2) / 4
  let z := (1 + 4 * b ^ 2 - D ^ 2) / 4
  let k := (1 + b ^ 2 - c ^ 2) / 2
  13866128436518096 / 10 ^ 16 < c ∧ c < 13866128436518100 / 10 ^ 16 ∧
    2873744161801659 / 10 ^ 15 < B ∧ B < 2873744161801662 / 10 ^ 15 ∧
    A + C = 3 * c * b + c ^ 2 - 1 ∧
    (k - x * z) ^ 2 = (1 - x ^ 2) * (b ^ 2 - z ^ 2) ∧
    x < 0 ∧ z < 0 ∧ k - x * z < 0

/-- Twice the optimal six-point constant, defined by its isolated exact system. -/
def cStar : ℝ :=
  sInf {c : ℝ | ∃ B : ℝ, IsEndpointPair c B}

/-- The optimal two-colour six-point constant. -/
def sStar : ℝ :=
  cStar / 2

end Bescovitch
