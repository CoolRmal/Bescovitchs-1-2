/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Real.Basic

/-!
# Symmetric concavity on a product

The local mixed certificate is symmetric in its two chords.  Concavity therefore moves its
maximum to the diagonal by averaging a pair of parameters with its swap.
-/

@[expose] public section

namespace Bescovitch

/-- A swap-symmetric concave function on a product is bounded by its value at the diagonal
midpoint. -/
theorem le_diagonal_midpoint_of_swap_symmetric_concaveOn
    {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E} {f : E → E → ℝ}
    (hconcave : ConcaveOn ℝ (s ×ˢ s) fun p ↦ f p.1 p.2)
    (hsymmetric : ∀ x ∈ s, ∀ y ∈ s, f x y = f y x)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    f x y ≤ f ((1 / 2 : ℝ) • (x + y)) ((1 / 2 : ℝ) • (x + y)) := by
  have h := hconcave.2 (show (x, y) ∈ s ×ˢ s from ⟨hx, hy⟩)
    (show (y, x) ∈ s ×ˢ s from ⟨hy, hx⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  change (1 / 2 : ℝ) • f x y + (1 / 2 : ℝ) • f y x ≤
    f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
      ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • x) at h
  rw [hsymmetric y hy x hx] at h
  have hleft : (1 / 2 : ℝ) • f x y + (1 / 2 : ℝ) • f x y = f x y := by
    norm_num
    ring
  have hfirst : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = (1 / 2 : ℝ) • (x + y) := by
    module
  have hsecond : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • x = (1 / 2 : ℝ) • (x + y) := by
    module
  rwa [hleft, hfirst, hsecond] at h

end Bescovitch
