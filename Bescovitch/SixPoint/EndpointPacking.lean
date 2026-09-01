/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.BlueChildSwap
public import Bescovitch.SixPoint.EndpointFailureClosed
public import Bescovitch.SixPoint.FiniteProperty
public import Bescovitch.SixPoint.SiblingIncidenceClosed
public import Bescovitch.SixPoint.WeightedChart

/-!
# The endpoint packing theorem

This file assembles the finite failure tree.  Its sole analytic input is the weighted geometric
bound for two ordered chords in the unit disk.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- The weighted geometric inequality for two ordered sibling pairs in the unit disk. -/
def WeightedGeometricBound : Prop :=
  ∀ e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2)),
    ‖e‖ = 1 →
    ‖p₁‖ ≤ 1 → ‖p₂‖ ≤ 1 → ‖w₁‖ ≤ 1 → ‖w₂‖ ≤ 1 →
    cStar ≤ ‖p₁ - p₂‖ → cStar ≤ ‖w₁ - w₂‖ →
    weightedPairScore e cStar endpointLambda endpointMu p₁ p₂ w₁ w₂ ≤ 0

/-- The lens-chart inequality implies the coordinate-free weighted geometric bound. -/
theorem weightedGeometricBound_of_lensChartBound
    (hchart : WeightedLensChartBound) : WeightedGeometricBound := by
  intro e p₁ p₂ w₁ w₂ he hp₁ hp₂ hw₁ hw₂ hpChord hwChord
  exact weightedPairScore_nonpos_of_lensChartBound_of_separated hchart
    e p₁ p₂ w₁ w₂ he hp₁ hp₂ hw₁ hw₂ hpChord hwChord

private theorem weightedGeometricBound_configuration
    (hweighted : WeightedGeometricBound) {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt sStar) :
    weightedPairScore configuration.rootDisplacement cStar endpointLambda endpointMu
      (configuration.redDisplacement .left) (configuration.redDisplacement .right)
      (configuration.bluePullback .left) (configuration.bluePullback .right) ≤ 0 := by
  apply hweighted
  · exact configuration.norm_rootDisplacement h
  · exact configuration.norm_redDisplacement_le_one h (by simp)
  · exact configuration.norm_redDisplacement_le_one h (by simp)
  · exact configuration.norm_bluePullback_le_one h (by simp)
  · exact configuration.norm_bluePullback_le_one h (by simp)
  · have hchord := configuration.two_mul_le_dist_redDisplacement h
    rw [sStar, dist_eq_norm] at hchord
    convert hchord using 1
    ring
  · have hchord := configuration.two_mul_le_dist_bluePullback h
    rw [sStar, dist_eq_norm] at hchord
    convert hchord using 1
    ring

private theorem exists_nonnegative_score_of_selected_diagonal
    (hweighted : WeightedGeometricBound) (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt sStar)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ∃ packing : SixPointPacking configuration, 0 ≤ packing.score sStar := by
  rcases exists_nonnegative_score_or_matched_sibling_endpoint configuration h hmatching with
    hpacking | ⟨code, hcode, hred, hblue⟩
  · exact hpacking
  · rcases hcode with rfl | rfl
    · exact exists_nonnegative_score_of_matched_endpoint_zero configuration h hmatching hred hblue
        (weightedGeometricBound_configuration hweighted h)
    · exact exists_nonnegative_score_of_matched_endpoint_three configuration h hmatching hred hblue
        (weightedGeometricBound_configuration hweighted (IsAdmissibleAt.swapChildren h))

/-- The weighted geometric bound implies the finite six-point property at the exact endpoint. -/
theorem sixPointFiniteProperty_sStar_of_weightedGeometricBound
    (hweighted : WeightedGeometricBound) : SixPointFiniteProperty sStar := by
  intro configuration h
  rcases exists_nonnegative_score_or_matching_obstruction configuration h with
    hpacking | hdiagonal | hantiDiagonal
  · exact hpacking
  · exact exists_nonnegative_score_of_selected_diagonal hweighted configuration h hdiagonal
  · let swapped := swapBlueChildren configuration
    have hadmissible : swapped.IsAdmissibleAt sStar := IsAdmissibleAt.swapBlueChildren h
    have hmatching : SelectedDiagonalMatchingFails swapped :=
      (selectedDiagonalMatchingFails_swapBlueChildren configuration).2 hantiDiagonal
    obtain ⟨packing, hscore⟩ :=
      exists_nonnegative_score_of_selected_diagonal hweighted swapped hadmissible hmatching
    exact ⟨packing.unswapBlue, by simpa only [packing.unswapBlue_score] using hscore⟩

end Bescovitch
