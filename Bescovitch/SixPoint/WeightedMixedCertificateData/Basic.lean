/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Int.Basic

/-!
# Data for the mixed weighted certificate

The mixed-score proof uses an adaptive dyadic tree.  A certified leaf stores six positive tangent
parameters, four rational support slopes, and four nonnegative disk-slack multipliers.
-/

@[expose] public section

namespace Bescovitch

/-- The integer numerators stored at one certified leaf; every denominator is `4096`. -/
structure WeightedMixedLeaf where
  /-- Numerators of the six positive tangent parameters. -/
  rhoNumerator : Fin 6 → ℕ
  /-- Numerators of the four stereographic support slopes. -/
  supportSlopeNumerator : Fin 4 → ℤ
  /-- Numerators of the four nonnegative disk-slack multipliers. -/
  slackNumerator : Fin 4 → ℕ

/-- An adaptive dyadic partition whose leaves are either infeasible or exactly certified. -/
inductive WeightedMixedTree where
  | outside
  | certified (data : WeightedMixedLeaf)
  | split (left right : WeightedMixedTree)

end Bescovitch
