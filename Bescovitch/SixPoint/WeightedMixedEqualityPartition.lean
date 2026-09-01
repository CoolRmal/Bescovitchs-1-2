/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedEquality
public import Bescovitch.SixPoint.WeightedMixedRootCover

/-!
# Exact face partition for the exceptional mixed chart

Four exact pairs of rational cuts divide the exceptional root box into `3 ^ 4` cells.  The
central cell is the analytic equality neighborhood; all other cells are delegated to the finite
complement certificate.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- One of the three closed bands determined by two ordered cuts. -/
inductive WeightedMixedEqualityBand
  | lower
  | middle
  | upper
  deriving DecidableEq, Fintype

/-- The four band choices for the two longitudinal and two stereographic coordinates. -/
structure WeightedMixedEqualityCell where
  /-- Band of the first chord's longitudinal coordinate. -/
  pLongitudinal : WeightedMixedEqualityBand
  /-- Band of the first chord's stereographic coordinate. -/
  pStereographic : WeightedMixedEqualityBand
  /-- Band of the second chord's longitudinal coordinate. -/
  wLongitudinal : WeightedMixedEqualityBand
  /-- Band of the second chord's stereographic coordinate. -/
  wStereographic : WeightedMixedEqualityBand
  deriving DecidableEq, Fintype

/-- Split an interval into the three closed bands determined by two interior cuts. -/
def threeBandInterval (I : RationalInterval) (lowerCut upperCut : ℚ)
    (hcuts : I.lower ≤ lowerCut ∧ lowerCut ≤ upperCut ∧ upperCut ≤ I.upper) :
    WeightedMixedEqualityBand → RationalInterval
  | .lower => ⟨I.lower, lowerCut, hcuts.1⟩
  | .middle => ⟨lowerCut, upperCut, hcuts.2.1⟩
  | .upper => ⟨upperCut, I.upper, hcuts.2.2⟩

/-- The exact rational box represented by one equality-partition cell. -/
def weightedMixedEqualityCellBox (cell : WeightedMixedEqualityCell) :
    Fin 6 → RationalInterval
  | 0 => threeBandInterval (weightedMixedRootBox true true 0) (85902 / 100000)
      (85984 / 100000) (by norm_num [weightedMixedRootBox]) cell.pLongitudinal
  | 1 => weightedMixedRootBox true true 1
  | 2 => threeBandInterval (weightedMixedRootBox true true 2) (649 / 1000)
      (655 / 1000) (by norm_num [weightedMixedRootBox]) cell.pStereographic
  | 3 => threeBandInterval (weightedMixedRootBox true true 3) (85902 / 100000)
      (85984 / 100000) (by norm_num [weightedMixedRootBox]) cell.wLongitudinal
  | 4 => weightedMixedRootBox true true 4
  | 5 => threeBandInterval (weightedMixedRootBox true true 5) (649 / 1000)
      (655 / 1000) (by norm_num [weightedMixedRootBox]) cell.wStereographic

/-- The unique cell in which all four cut coordinates lie between their two face cuts. -/
def weightedMixedEqualityLocalCell : WeightedMixedEqualityCell where
  pLongitudinal := .middle
  pStereographic := .middle
  wLongitudinal := .middle
  wStereographic := .middle

/-- The weighted mixed score in the exceptional chart with both orientations negative. -/
def weightedMixedEqualityScore (x : Fin 6 → ℝ) : ℝ :=
  weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
    (chordChartFirst (-1) (x 0) (x 1) (x 2))
    (chordChartSecond (-1) cStar (x 0) (x 1) (x 2))
    (chordChartFirst (-1) (x 3) (x 4) (x 5))
    (chordChartSecond (-1) cStar (x 3) (x 4) (x 5))

private theorem exists_band_of_mem {I : RationalInterval} {lowerCut upperCut : ℚ}
    (hcuts : I.lower ≤ lowerCut ∧ lowerCut ≤ upperCut ∧ upperCut ≤ I.upper)
    {x : ℝ} (hx : I.Contains x) :
    ∃ band, (threeBandInterval I lowerCut upperCut hcuts band).Contains x := by
  by_cases hlower : x < lowerCut
  · refine ⟨.lower, ?_⟩
    simpa [threeBandInterval, RationalInterval.Contains] using ⟨hx.1, hlower.le⟩
  · by_cases hupper : (upperCut : ℝ) < x
    · refine ⟨.upper, ?_⟩
      simpa [threeBandInterval, RationalInterval.Contains] using ⟨hupper.le, hx.2⟩
    · refine ⟨.middle, ?_⟩
      simpa [threeBandInterval, RationalInterval.Contains] using
        ⟨le_of_not_gt hlower, le_of_not_gt hupper⟩

/-- Every point of the exceptional root box lies in one of the `3 ^ 4` exact cells. -/
theorem exists_weighted_mixed_equality_cell (x : Fin 6 → ℝ)
    (hx : ∀ i, (weightedMixedRootBox true true i).Contains (x i)) :
    ∃ cell, ∀ i, (weightedMixedEqualityCellBox cell i).Contains (x i) := by
  obtain ⟨pLongitudinal, hpLongitudinal⟩ := exists_band_of_mem
    (I := weightedMixedRootBox true true 0) (lowerCut := 85902 / 100000)
    (upperCut := 85984 / 100000) (by norm_num [weightedMixedRootBox]) (hx 0)
  obtain ⟨pStereographic, hpStereographic⟩ := exists_band_of_mem
    (I := weightedMixedRootBox true true 2) (lowerCut := 649 / 1000)
    (upperCut := 655 / 1000) (by norm_num [weightedMixedRootBox]) (hx 2)
  obtain ⟨wLongitudinal, hwLongitudinal⟩ := exists_band_of_mem
    (I := weightedMixedRootBox true true 3) (lowerCut := 85902 / 100000)
    (upperCut := 85984 / 100000) (by norm_num [weightedMixedRootBox]) (hx 3)
  obtain ⟨wStereographic, hwStereographic⟩ := exists_band_of_mem
    (I := weightedMixedRootBox true true 5) (lowerCut := 649 / 1000)
    (upperCut := 655 / 1000) (by norm_num [weightedMixedRootBox]) (hx 5)
  let cell : WeightedMixedEqualityCell :=
    ⟨pLongitudinal, pStereographic, wLongitudinal, wStereographic⟩
  refine ⟨cell, fun i ↦ ?_⟩
  fin_cases i
  · simpa [cell, weightedMixedEqualityCellBox] using hpLongitudinal
  · simpa [weightedMixedEqualityCellBox] using hx 1
  · simpa [cell, weightedMixedEqualityCellBox] using hpStereographic
  · simpa [cell, weightedMixedEqualityCellBox] using hwLongitudinal
  · simpa [weightedMixedEqualityCellBox] using hx 4
  · simpa [cell, weightedMixedEqualityCellBox] using hwStereographic

/-- The analytic equality theorem bounds the score throughout the central partition cell. -/
theorem weighted_mixed_equality_score_nonpos_on_local_cell_of_self
    (selfNonpos : ∀ p₁ p₂ : EuclideanSpace ℝ (Fin 2),
      ‖p₁‖ ≤ 1 → ‖p₂‖ ≤ 1 → cStar ≤ ‖p₁ - p₂‖ →
      weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu p₁ p₂ p₁ p₂ ≤ 0)
    (x : Fin 6 → ℝ)
    (hx : ∀ i, (weightedMixedEqualityCellBox weightedMixedEqualityLocalCell i).Contains (x i))
    (hPFirst : x 0 ^ 2 + x 1 ^ 2 ≤ 1)
    (hWFirst : x 3 ^ 2 + x 4 ^ 2 ≤ 1) : weightedMixedEqualityScore x ≤ 0 := by
  have haP : 0.85902 ≤ x 0 ∧ x 0 ≤ 0.85984 := by
    have h := hx 0
    norm_num [weightedMixedEqualityCellBox, weightedMixedEqualityLocalCell,
      threeBandInterval, RationalInterval.Contains] at h ⊢
    exact h
  have hzP : 0.649 ≤ x 2 ∧ x 2 ≤ 0.655 := by
    have h := hx 2
    norm_num [weightedMixedEqualityCellBox, weightedMixedEqualityLocalCell,
      threeBandInterval, RationalInterval.Contains] at h ⊢
    exact h
  have haW : 0.85902 ≤ x 3 ∧ x 3 ≤ 0.85984 := by
    have h := hx 3
    norm_num [weightedMixedEqualityCellBox, weightedMixedEqualityLocalCell,
      threeBandInterval, RationalInterval.Contains] at h ⊢
    exact h
  have hzW : 0.649 ≤ x 5 ∧ x 5 ≤ 0.655 := by
    have h := hx 5
    norm_num [weightedMixedEqualityCellBox, weightedMixedEqualityLocalCell,
      threeBandInterval, RationalInterval.Contains] at h ⊢
    exact h
  simpa only [weightedMixedEqualityScore] using
    WeightedMixedEqualityLocal.weighted_pair_score_nonpos_in_equality_local_box_of_self
      selfNonpos (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) haP hzP haW hzW hPFirst hWFirst

/-- Cellwise complement bounds and the analytic local bound imply the root-box bound. -/
theorem weighted_mixed_equality_score_nonpos_of_cell_bounds
    (selfNonpos : ∀ p₁ p₂ : EuclideanSpace ℝ (Fin 2),
      ‖p₁‖ ≤ 1 → ‖p₂‖ ≤ 1 → cStar ≤ ‖p₁ - p₂‖ →
      weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu p₁ p₂ p₁ p₂ ≤ 0)
    (hcomplement : ∀ cell ≠ weightedMixedEqualityLocalCell, ∀ x : Fin 6 → ℝ,
      (∀ i, (weightedMixedEqualityCellBox cell i).Contains (x i)) →
      x 0 ^ 2 + x 1 ^ 2 ≤ 1 → (x 0 - cStar) ^ 2 + x 1 ^ 2 ≤ 1 →
      x 3 ^ 2 + x 4 ^ 2 ≤ 1 → (x 3 - cStar) ^ 2 + x 4 ^ 2 ≤ 1 →
      weightedMixedEqualityScore x ≤ 0)
    (x : Fin 6 → ℝ)
    (hx : ∀ i, (weightedMixedRootBox true true i).Contains (x i))
    (hPFirst : x 0 ^ 2 + x 1 ^ 2 ≤ 1)
    (hPSecond : (x 0 - cStar) ^ 2 + x 1 ^ 2 ≤ 1)
    (hWFirst : x 3 ^ 2 + x 4 ^ 2 ≤ 1)
    (hWSecond : (x 3 - cStar) ^ 2 + x 4 ^ 2 ≤ 1) :
    weightedMixedEqualityScore x ≤ 0 := by
  obtain ⟨cell, hcell⟩ := exists_weighted_mixed_equality_cell x hx
  by_cases hlocal : cell = weightedMixedEqualityLocalCell
  · subst cell
    exact weighted_mixed_equality_score_nonpos_on_local_cell_of_self
      selfNonpos x hcell hPFirst hWFirst
  · exact hcomplement cell hlocal x hcell hPFirst hPSecond hWFirst hWSecond

end Bescovitch
