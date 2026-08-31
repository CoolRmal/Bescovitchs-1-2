/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedCross
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Tangent bounds for the mixed weighted score

The norm has a quadratic lower support on the unit ball.  In the plane, its Gram remainder is
the square of the component perpendicular to the chosen supporting direction.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Bescovitch

/-- A linear norm support strengthened by half of its Gram remainder. -/
theorem inner_add_half_gram_remainder_le_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u v : E)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ⟪u, v⟫_ℝ + (‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2) / 2 ≤ ‖v‖ := by
  have hinner := abs_real_inner_le_norm u v
  have huv : ‖u‖ * ‖v‖ ≤ ‖v‖ := by
    exact mul_le_of_le_one_left (norm_nonneg v) hu
  have hlower : -‖v‖ ≤ ⟪u, v⟫_ℝ := (neg_le_of_abs_le (hinner.trans huv))
  have hupper : ⟪u, v⟫_ℝ ≤ ‖v‖ := (le_of_abs_le (hinner.trans huv))
  have huSq : ‖u‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg u, sq_nonneg (1 - ‖u‖)]
  have hgramUpper :
      ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 := by
    nlinarith [sq_nonneg ‖v‖]
  have hfactor : 0 ≤ (‖v‖ - ⟪u, v⟫_ℝ) * (2 - ‖v‖ - ⟪u, v⟫_ℝ) := by
    apply mul_nonneg <;> linarith
  nlinarith

end Bescovitch
