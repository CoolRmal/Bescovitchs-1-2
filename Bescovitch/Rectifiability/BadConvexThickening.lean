/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Rectifiability.BadConvexPacking

/-!
# Enlarging bad convex sets

The seven-diameter enlargements of a disjoint family of bad convex sets still leave a point of
the compact core uncovered.  The number `15 = 2 * 7 + 1` is exactly the diameter expansion
factor.
-/

@[expose] public section

noncomputable section

open Bornology MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace Bescovitch

/-- Straightness bounds the mass of all diameter thickenings by their total expanded diameter. -/
theorem measure_iUnion_diameterThickening_le {mu : Measure Plane} [IsFiniteMeasure mu]
    (hmu : IsStraightMeasure mu) {alpha p : ℝ} (halpha : 0 < alpha) (hp : 0 ≤ p)
    {F : Set Plane} {chosen : Set (Set Plane)}
    (hchosen : chosen ⊆ badConvexSets mu F alpha) (hcountable : chosen.Countable) :
    mu (⋃ V : chosen, diameterThickening p (V : Set Plane)) ≤
      ENNReal.ofReal (2 * p + 1) * ∑' V : chosen, Metric.ediam (V : Set Plane) := by
  letI : Countable chosen := hcountable.to_subtype
  calc
    mu (⋃ V : chosen, diameterThickening p (V : Set Plane)) ≤
        ∑' V : chosen, mu (diameterThickening p (V : Set Plane)) := measure_iUnion_le _
    _ ≤ ∑' V : chosen, Metric.ediam (diameterThickening p (V : Set Plane)) :=
      ENNReal.tsum_le_tsum fun V ↦
        hmu _ (isOpen_diameterThickening p (V : Set Plane)).measurableSet
    _ ≤ ∑' V : chosen, ENNReal.ofReal (2 * p + 1) * Metric.ediam (V : Set Plane) :=
      ENNReal.tsum_le_tsum fun V ↦
        ediam_diameterThickening_le hp (isBounded_of_mem_badConvexSets halpha
          (hchosen V.property))
    _ = ENNReal.ofReal (2 * p + 1) * ∑' V : chosen, Metric.ediam (V : Set Plane) :=
      ENNReal.tsum_mul_left

/-- The seven-diameter enlargements have less mass than the retained core. -/
theorem measure_iUnion_sevenDiameterThickening_lt {mu : Measure Plane} [IsFiniteMeasure mu]
    (hmu : IsStraightMeasure mu) {F : Set Plane} (hF : MeasurableSet F)
    {alpha : ℝ} (halpha : 0 < alpha) {chosen : Set (Set Plane)}
    (hchosen : chosen ⊆ badConvexSets mu F alpha) (hcountable : chosen.Countable)
    (hdisjoint : chosen.PairwiseDisjoint id)
    (houtside : mu Fᶜ < ENNReal.ofReal (alpha / 15) * mu F) :
    mu (⋃ V : chosen, diameterThickening 7 (V : Set Plane)) < mu F := by
  have hsum := tsum_ediam_badConvexSets_lt hF halpha (by norm_num : (0 : ℝ) < 15)
    hchosen hcountable hdisjoint houtside
  calc
    mu (⋃ V : chosen, diameterThickening 7 (V : Set Plane)) ≤
        ENNReal.ofReal 15 * ∑' V : chosen, Metric.ediam (V : Set Plane) := by
      convert measure_iUnion_diameterThickening_le hmu halpha
        (by norm_num : (0 : ℝ) ≤ 7) hchosen hcountable using 1
      all_goals norm_num
    _ < ENNReal.ofReal 15 * (ENNReal.ofReal (1 / 15) * mu F) :=
      ENNReal.mul_lt_mul_right (by norm_num) ENNReal.ofReal_ne_top hsum
    _ = mu F := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 15)]
      norm_num

/-- Consequently, some point of the retained core lies outside every seven-diameter
enlargement. -/
theorem exists_mem_not_mem_sevenDiameterThickening {mu : Measure Plane} [IsFiniteMeasure mu]
    (hmu : IsStraightMeasure mu) {F : Set Plane} (hF : MeasurableSet F)
    {alpha : ℝ} (halpha : 0 < alpha) {chosen : Set (Set Plane)}
    (hchosen : chosen ⊆ badConvexSets mu F alpha) (hcountable : chosen.Countable)
    (hdisjoint : chosen.PairwiseDisjoint id)
    (houtside : mu Fᶜ < ENNReal.ofReal (alpha / 15) * mu F) :
    ∃ z ∈ F, ∀ V : chosen, z ∉ diameterThickening 7 (V : Set Plane) := by
  have hmeasure := measure_iUnion_sevenDiameterThickening_lt hmu hF halpha hchosen hcountable
    hdisjoint houtside
  have hnot_subset : ¬F ⊆ ⋃ V : chosen, diameterThickening 7 (V : Set Plane) := by
    intro hsubset
    exact (not_le_of_gt hmeasure) (measure_mono hsubset)
  obtain ⟨z, hzF, hz⟩ := Set.not_subset.mp hnot_subset
  exact ⟨z, hzF, fun V hzV ↦ hz (mem_iUnion_of_mem V hzV)⟩

end Bescovitch
