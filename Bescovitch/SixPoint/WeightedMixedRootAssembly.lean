/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedChart
public import Bescovitch.SixPoint.WeightedMixedRootCover

/-!
# Assembly of the mixed root boxes

A bound on each exact rational root box gives the mixed inequality on every lens chart.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- Bounds on all rational root boxes imply the mixed inequality on all lens charts. -/
theorem weightedLensChartBound_of_mixed_root_box_bounds
    (hroot : ∀ (capP capW : Bool) (sideP sideW : ℚ) (x : Fin 6 → ℝ),
      ((sideP : ℝ) ^ 2 = 1) → ((sideW : ℝ) ^ 2 = 1) →
      (∀ i, (weightedMixedRootBox capP capW i).Contains (x i)) →
      x 0 ^ 2 + x 1 ^ 2 ≤ 1 → (x 0 - cStar) ^ 2 + x 1 ^ 2 ≤ 1 →
      x 3 ^ 2 + x 4 ^ 2 ≤ 1 → (x 3 - cStar) ^ 2 + x 4 ^ 2 ≤ 1 →
      weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
        (chordChartFirst sideP (x 0) (x 1) (x 2))
        (chordChartSecond sideP cStar (x 0) (x 1) (x 2))
        (chordChartFirst sideW (x 3) (x 4) (x 5))
        (chordChartSecond sideW cStar (x 3) (x 4) (x 5)) ≤ 0) :
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

end Bescovitch
