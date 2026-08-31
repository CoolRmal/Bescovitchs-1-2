/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Rat.Defs

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

namespace WeightedMixedLeaf

/-- A positive tangent parameter represented by a leaf. -/
def rho (data : WeightedMixedLeaf) (i : Fin 6) : ℚ := data.rhoNumerator i / 4096

/-- A stereographic support slope represented by a leaf. -/
def supportSlope (data : WeightedMixedLeaf) (i : Fin 4) : ℚ :=
  data.supportSlopeNumerator i / 4096

/-- A nonnegative disk-slack multiplier represented by a leaf. -/
def slack (data : WeightedMixedLeaf) (i : Fin 4) : ℚ := data.slackNumerator i / 4096

end WeightedMixedLeaf

/-- An adaptive dyadic partition whose leaves are either infeasible or exactly certified. -/
inductive WeightedMixedTree where
  | outside
  | certified (data : WeightedMixedLeaf)
  | split (left right : WeightedMixedTree)

/-- A compact constructor for the generated integer data at one certified tree leaf. -/
def weightedMixedCertified
    (r0 r1 r2 r3 r4 r5 : ℕ) (s0 s1 s2 s3 : ℤ) (e0 e1 e2 e3 : ℕ) :
    WeightedMixedTree :=
  .certified {
    rhoNumerator
      | 0 => r0
      | 1 => r1
      | 2 => r2
      | 3 => r3
      | 4 => r4
      | 5 => r5
    supportSlopeNumerator
      | 0 => s0
      | 1 => s1
      | 2 => s2
      | 3 => s3
    slackNumerator
      | 0 => e0
      | 1 => e1
      | 2 => e2
      | 3 => e3 }

end Bescovitch
