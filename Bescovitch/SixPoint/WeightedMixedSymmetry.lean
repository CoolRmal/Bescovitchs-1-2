/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.RationalChord
public import Bescovitch.SixPoint.WeightedChart
public import Bescovitch.SixPoint.WeightedMixedTree

/-!
# Symmetries of the mixed root boxes

Reflection in the root axis lets pair transposition preserve the asymmetric stereographic
ranges. Consequently a bound for one root box also bounds the box with its two pairs exchanged.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Bescovitch

/-- Reflection in the root axis negates the transverse chord coordinate and parameter. -/
theorem orientedCoordinates_reflect_chordChartFirst (side a h z : ℝ) :
    orientedCoordinates !₂[1, 0] (-1) (chordChartFirst side a h z) =
      chordChartFirst side a (-h) (-z) := by
  ext i
  fin_cases i <;>
    simp [orientedCoordinates, chordChartFirst, stereographicDirection, quarterTurn,
      PiLp.inner_apply, Fin.sum_univ_two] <;>
    ring

/-- Reflection in the root axis has the same action on the second chord endpoint. -/
theorem orientedCoordinates_reflect_chordChartSecond (side c a h z : ℝ) :
    orientedCoordinates !₂[1, 0] (-1) (chordChartSecond side c a h z) =
      chordChartSecond side c a (-h) (-z) := by
  ext i
  fin_cases i <;>
    simp [orientedCoordinates, chordChartSecond, stereographicDirection, quarterTurn,
      PiLp.inner_apply, Fin.sum_univ_two] <;>
    ring

/-- Simultaneously reflecting both chord charts in the root axis preserves the weighted score. -/
theorem weightedPairScore_reflect_chordCharts
    (c lambda mu sideP aP hP zP sideW aW hW zW : ℝ) :
    weightedPairScore !₂[1, 0] c lambda mu
        (chordChartFirst sideP aP hP zP) (chordChartSecond sideP c aP hP zP)
        (chordChartFirst sideW aW hW zW) (chordChartSecond sideW c aW hW zW) =
      weightedPairScore !₂[1, 0] c lambda mu
        (chordChartFirst sideP aP (-hP) (-zP))
        (chordChartSecond sideP c aP (-hP) (-zP))
        (chordChartFirst sideW aW (-hW) (-zW))
        (chordChartSecond sideW c aW (-hW) (-zW)) := by
  have hroot : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have horientation : (-1 : ℝ) ^ 2 = 1 := by norm_num
  let T := orientedCoordinateIsometry !₂[1, 0] (-1) hroot horientation
  have hTroot : T !₂[1, 0] = !₂[1, 0] := orientedCoordinates_self !₂[1, 0] (-1) hroot
  simpa [T, hTroot, orientedCoordinates_reflect_chordChartFirst,
    orientedCoordinates_reflect_chordChartSecond] using
      (weightedPairScore_linearIsometry T !₂[1, 0] c lambda mu
        (chordChartFirst sideP aP hP zP) (chordChartSecond sideP c aP hP zP)
        (chordChartFirst sideW aW hW zW) (chordChartSecond sideW c aW hW zW)).symm

/-- The mixed weighted inequality restricted to one rational root box. -/
def WeightedMixedRootBoxBound (capP capW : Bool) (sideP sideW : ℚ) : Prop :=
  ∀ x : Fin 6 → ℝ,
    ((sideP : ℝ) ^ 2 = 1) → ((sideW : ℝ) ^ 2 = 1) →
    (∀ i, (weightedMixedRootBox capP capW i).Contains (x i)) →
    x 0 ^ 2 + x 1 ^ 2 ≤ 1 → (x 0 - barC) ^ 2 + x 1 ^ 2 ≤ 1 →
    x 3 ^ 2 + x 4 ^ 2 ≤ 1 → (x 3 - barC) ^ 2 + x 4 ^ 2 ≤ 1 →
    weightedPairScore !₂[1, 0] barC endpointLambda endpointMu
      (chordChartFirst sideP (x 0) (x 1) (x 2))
      (chordChartSecond sideP barC (x 0) (x 1) (x 2))
      (chordChartFirst sideW (x 3) (x 4) (x 5))
      (chordChartSecond sideW barC (x 3) (x 4) (x 5)) ≤ 0

private theorem swapped_coordinates_mem_root_box_of_nonneg (capP capW : Bool)
    (x : Fin 6 → ℝ) (hx : ∀ i, (weightedMixedRootBox capP capW i).Contains (x i))
    (hzW : 0 ≤ x 5) : ∀ i, (weightedMixedRootBox capW capP i).Contains
      ((![x 3, x 4, x 5, x 0, x 1, x 2] : Fin 6 → ℝ) i) := by
  have hxPz : 0 ≤ x 2 ∧ x 2 ≤ 1 := by
    simpa [weightedMixedRootBox, RationalInterval.Contains] using hx 2
  have hxWz : -1 ≤ x 5 ∧ x 5 ≤ 1 := by
    simpa [weightedMixedRootBox, RationalInterval.Contains] using hx 5
  intro i
  fin_cases i
  · simpa [weightedMixedRootBox] using hx 3
  · simpa [weightedMixedRootBox] using hx 4
  · simpa [weightedMixedRootBox, RationalInterval.Contains] using ⟨hzW, hxWz.2⟩
  · simpa [weightedMixedRootBox] using hx 0
  · simpa [weightedMixedRootBox] using hx 1
  · simpa [weightedMixedRootBox, RationalInterval.Contains] using
      (show -1 ≤ x 2 ∧ x 2 ≤ 1 by constructor <;> linarith [hxPz.1, hxPz.2])

private theorem reflected_swapped_coordinates_mem_root_box_of_nonpos (capP capW : Bool)
    (x : Fin 6 → ℝ) (hx : ∀ i, (weightedMixedRootBox capP capW i).Contains (x i))
    (hzW : x 5 ≤ 0) : ∀ i, (weightedMixedRootBox capW capP i).Contains
      ((![x 3, -x 4, -x 5, x 0, -x 1, -x 2] : Fin 6 → ℝ) i) := by
  have hxPh : (-720643 / 10 ^ 6 : ℝ) ≤ x 1 ∧ x 1 ≤ 720643 / 10 ^ 6 := by
    simpa [weightedMixedRootBox, RationalInterval.Contains] using hx 1
  have hxPz : 0 ≤ x 2 ∧ x 2 ≤ 1 := by
    simpa [weightedMixedRootBox, RationalInterval.Contains] using hx 2
  have hxWh : (-720643 / 10 ^ 6 : ℝ) ≤ x 4 ∧ x 4 ≤ 720643 / 10 ^ 6 := by
    simpa [weightedMixedRootBox, RationalInterval.Contains] using hx 4
  have hxWz : -1 ≤ x 5 ∧ x 5 ≤ 1 := by
    simpa [weightedMixedRootBox, RationalInterval.Contains] using hx 5
  intro i
  fin_cases i
  · simpa [weightedMixedRootBox] using hx 3
  · simpa [weightedMixedRootBox, RationalInterval.Contains] using
      (show (-720643 / 10 ^ 6 : ℝ) ≤ -x 4 ∧ -x 4 ≤ 720643 / 10 ^ 6 by
        constructor <;> linarith [hxWh.1, hxWh.2])
  · simpa [weightedMixedRootBox, RationalInterval.Contains] using
      (show 0 ≤ -x 5 ∧ -x 5 ≤ 1 by constructor <;> linarith [hxWz.1, hxWz.2])
  · simpa [weightedMixedRootBox] using hx 0
  · simpa [weightedMixedRootBox, RationalInterval.Contains] using
      (show (-720643 / 10 ^ 6 : ℝ) ≤ -x 1 ∧ -x 1 ≤ 720643 / 10 ^ 6 by
        constructor <;> linarith [hxPh.1, hxPh.2])
  · simpa [weightedMixedRootBox, RationalInterval.Contains] using
      (show -1 ≤ -x 2 ∧ -x 2 ≤ 1 by constructor <;> linarith [hxPz.1, hxPz.2])

/-- Exchanging the two chord pairs turns a bound for the transposed root box into the source
bound. -/
theorem WeightedMixedRootBoxBound.swap {capP capW : Bool} {sideP sideW : ℚ}
    (hbound : WeightedMixedRootBoxBound capW capP sideW sideP) :
    WeightedMixedRootBoxBound capP capW sideP sideW := by
  intro x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
  by_cases hzW : 0 ≤ x 5
  · let y : Fin 6 → ℝ := ![x 3, x 4, x 5, x 0, x 1, x 2]
    have hy := swapped_coordinates_mem_root_box_of_nonneg capP capW x hx hzW
    have h := hbound y hsideW hsideP hy (by simpa [y] using hWFirst)
      (by simpa [y] using hWSecond) (by simpa [y] using hPFirst)
      (by simpa [y] using hPSecond)
    rw [weightedPairScore_swap]
    simpa [y] using h
  · let y : Fin 6 → ℝ := ![x 3, -x 4, -x 5, x 0, -x 1, -x 2]
    have hy := reflected_swapped_coordinates_mem_root_box_of_nonpos capP capW x hx
      (le_of_not_ge hzW)
    have h := hbound y hsideW hsideP hy (by simpa [y] using hWFirst)
      (by simpa [y] using hWSecond) (by simpa [y] using hPFirst)
      (by simpa [y] using hPSecond)
    rw [weightedPairScore_reflect_chordCharts]
    rw [weightedPairScore_swap]
    simpa [y] using h

end Bescovitch
