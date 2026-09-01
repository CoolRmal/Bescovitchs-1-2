/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedChart
public import Bescovitch.SixPoint.WeightedMixedSymmetry
import Bescovitch.SixPoint.WeightedMixedRootCover

/-!
# Assembly of the mixed root boxes

A bound on each exact rational root box gives the mixed inequality on every lens chart.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- Bounds on all rational root boxes imply the mixed inequality on all lens charts. -/
theorem weightedLensChartBound_of_mixed_root_box_bounds
    (hroot : ∀ capP capW sideP sideW,
      WeightedMixedRootBoxBound capP capW sideP sideW) :
    WeightedLensChartBound := by
  intro sideP zP aP hP sideW zW aW hW hsideP hsideW hzPZero hzPOne
    hzWNegOne hzWOne hPFirst hPSecond hWFirst hWSecond
  let x : Fin 6 → ℝ := ![aP, hP, zP, aW, hW, zW]
  obtain ⟨capP, capW, hx⟩ := exists_weighted_mixed_root_box aP hP zP aW hW zW
    ⟨hzPZero, hzPOne⟩ ⟨hzWNegOne, hzWOne⟩ hPFirst hPSecond hWFirst hWSecond
  obtain ⟨sidePQ, hsidePQ, hsidePQSq⟩ :
      ∃ side : ℚ, (side : ℝ) = sideP ∧ (side : ℝ) ^ 2 = 1 := by
    rcases hsideP with rfl | rfl
    · exact ⟨1, by norm_num, by norm_num⟩
    · exact ⟨-1, by norm_num, by norm_num⟩
  obtain ⟨sideWQ, hsideWQ, hsideWQSq⟩ :
      ∃ side : ℚ, (side : ℝ) = sideW ∧ (side : ℝ) ^ 2 = 1 := by
    rcases hsideW with rfl | rfl
    · exact ⟨1, by norm_num, by norm_num⟩
    · exact ⟨-1, by norm_num, by norm_num⟩
  have hbound := hroot capP capW sidePQ sideWQ x hsidePQSq hsideWQSq hx
    hPFirst hPSecond hWFirst hWSecond
  rw [hsidePQ, hsideWQ] at hbound
  simpa [x] using hbound

private theorem rat_eq_one_or_neg_one_of_cast_sq_eq_one {side : ℚ}
    (hside : (side : ℝ) ^ 2 = 1) : side = 1 ∨ side = -1 := by
  rcases sq_eq_one_iff.mp hside with h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (by exact_mod_cast h)

/-- One representative from each pair-transposition orbit suffices for all mixed root boxes. -/
theorem weightedLensChartBound_of_canonical_mixed_root_box_bounds
    (h00NegNeg : WeightedMixedRootBoxBound false false (-1) (-1))
    (h00PosNeg : WeightedMixedRootBoxBound false false 1 (-1))
    (h00PosPos : WeightedMixedRootBoxBound false false 1 1)
    (h01NegNeg : WeightedMixedRootBoxBound false true (-1) (-1))
    (h01PosNeg : WeightedMixedRootBoxBound false true 1 (-1))
    (h10PosNeg : WeightedMixedRootBoxBound true false 1 (-1))
    (h10PosPos : WeightedMixedRootBoxBound true false 1 1)
    (h11NegNeg : WeightedMixedRootBoxBound true true (-1) (-1))
    (h11PosNeg : WeightedMixedRootBoxBound true true 1 (-1))
    (h11PosPos : WeightedMixedRootBoxBound true true 1 1) :
    WeightedLensChartBound := by
  apply weightedLensChartBound_of_mixed_root_box_bounds
  intro capP capW sideP sideW x hsideP hsideW hx
    hPFirst hPSecond hWFirst hWSecond
  rcases rat_eq_one_or_neg_one_of_cast_sq_eq_one hsideP with hp | hp <;>
    rcases rat_eq_one_or_neg_one_of_cast_sq_eq_one hsideW with hw | hw
  all_goals subst sideP; subst sideW
  all_goals cases capP <;> cases capW
  all_goals first
    | exact h00NegNeg x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h00PosNeg x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h00PosNeg.swap x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h00PosPos x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h01NegNeg x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h01NegNeg.swap x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h01PosNeg x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h01PosNeg.swap x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h10PosNeg x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h10PosNeg.swap x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h10PosPos x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h10PosPos.swap x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h11NegNeg x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h11PosNeg x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h11PosNeg.swap x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
    | exact h11PosPos x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond

end Bescovitch
