/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Sigma.Defs

/-!
# Basic facts about the one-dimensional rectifiability threshold

The forcing property is monotone in its density threshold. The infimum lemmas below keep the
nonemptiness and lower-bound requirements visible whenever they are mathematically needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace Bescovitch

variable (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Increasing the density threshold preserves the rectifiability-forcing property. -/
theorem ForcesOneRectifiability.mono {a b : ℝ} (ha : ForcesOneRectifiability X a)
    (hab : a ≤ b) : ForcesOneRectifiability X b := by
  intro s hs hfinite hdensity
  apply ha s hs hfinite
  filter_upwards [hdensity] with x hx
  exact (ENNReal.ofReal_le_ofReal hab).trans hx

/-- An admissible nonnegative threshold bounds `sigmaOne` from above. -/
theorem sigmaOne_le_of_forces {b : ℝ} (hb : 0 ≤ b) (hforce : ForcesOneRectifiability X b) :
    sigmaOne X ≤ b := by
  apply csInf_le
  · exact ⟨0, fun _ h ↦ h.1⟩
  · exact ⟨hb, hforce⟩

/-- If an admissible threshold exists, then `sigmaOne` is nonnegative. -/
theorem sigmaOne_nonneg
    (hne : ∃ b : ℝ, 0 ≤ b ∧ ForcesOneRectifiability X b) : 0 ≤ sigmaOne X := by
  apply le_csInf hne
  intro b hb
  exact hb.1

/-- Forcing rectifiability at every threshold above `b` proves `sigmaOne ≤ b`. -/
theorem sigmaOne_le_of_forall_gt {b : ℝ} (hb : 0 ≤ b)
    (hforce : ∀ c, b < c → ForcesOneRectifiability X c) : sigmaOne X ≤ b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply sigmaOne_le_of_forces X (add_nonneg hb hε.le)
  exact hforce (b + ε) (lt_add_of_pos_right b hε)

end Bescovitch
