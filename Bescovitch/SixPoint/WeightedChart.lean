/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.ChordChart
public import Bescovitch.SixPoint.EndpointWeights
public import Bescovitch.SixPoint.WeightedTangent

/-!
# Coordinate reduction for the mixed weighted score

The weighted score is unchanged by a linear isometry.  We choose the transverse orientation so
that the first chord lies in the upper stereographic half-chart.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Bescovitch

/-- A linear isometry preserves the weighted pair score. -/
theorem weightedPairScore_linearIsometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →ₗᵢ[ℝ] F) (e : E) (c lambda mu : ℝ) (p₁ p₂ w₁ w₂ : E) :
    weightedPairScore (T e) c lambda mu (T p₁) (T p₂) (T w₁) (T w₂) =
      weightedPairScore e c lambda mu p₁ p₂ w₁ w₂ := by
  simp only [weightedPairScore, ← T.map_sub, T.norm_map]

/-- One of the two transverse orientations puts a chosen vector in the upper half-plane. -/
theorem exists_orientedCoordinates_upper (e n : Plane) :
    ∃ orientation : ℝ, (orientation = 1 ∨ orientation = -1) ∧
      0 ≤ orientedCoordinates e orientation n 1 := by
  by_cases h : 0 ≤ ⟪quarterTurn e, n⟫_ℝ
  · refine ⟨1, Or.inl rfl, ?_⟩
    simpa [orientedCoordinates] using h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [orientedCoordinates_apply_one]
    have : ⟪quarterTurn e, n⟫_ℝ < 0 := lt_of_not_ge h
    nlinarith

/-- The oriented coordinate map sends the root vector to `(1,0)` and preserves the weighted
score. -/
theorem exists_oriented_weightedPairScore (e p₁ p₂ w₁ w₂ : Plane) (he : ‖e‖ = 1) :
    ∃ orientation : ℝ, (orientation = 1 ∨ orientation = -1) ∧
      0 ≤ orientedCoordinates e orientation (p₁ - p₂) 1 ∧
      orientedCoordinates e orientation e = !₂[1, 0] ∧
      weightedPairScore (orientedCoordinates e orientation e) cStar endpointLambda endpointMu
          (orientedCoordinates e orientation p₁) (orientedCoordinates e orientation p₂)
          (orientedCoordinates e orientation w₁) (orientedCoordinates e orientation w₂) =
        weightedPairScore e cStar endpointLambda endpointMu p₁ p₂ w₁ w₂ := by
  obtain ⟨orientation, horientation, hupper⟩ := exists_orientedCoordinates_upper e (p₁ - p₂)
  have horientationSq : orientation ^ 2 = 1 := by rcases horientation with rfl | rfl <;> norm_num
  let T := orientedCoordinateIsometry e orientation he horientationSq
  refine ⟨orientation, horientation, hupper, orientedCoordinates_self e orientation he, ?_⟩
  simpa [T] using
    weightedPairScore_linearIsometry T e cStar endpointLambda endpointMu p₁ p₂ w₁ w₂

/-- Every pair of endpoint-length chords in the unit disk belongs to one of the sixteen rational
lens charts.  The first stereographic parameter is made nonnegative by the common orientation. -/
theorem exists_weightedPairScore_lensChart (e p₁ p₂ w₁ w₂ : Plane)
    (he : ‖e‖ = 1) (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hpChord : ‖p₁ - p₂‖ = cStar) (hwChord : ‖w₁ - w₂‖ = cStar) :
    ∃ sideP zP aP hP sideW zW aW hW : ℝ,
      (sideP = 1 ∨ sideP = -1) ∧ (sideW = 1 ∨ sideW = -1) ∧
      0 ≤ zP ∧ zP ≤ 1 ∧ -1 ≤ zW ∧ zW ≤ 1 ∧
      aP ^ 2 + hP ^ 2 ≤ 1 ∧ (aP - cStar) ^ 2 + hP ^ 2 ≤ 1 ∧
      aW ^ 2 + hW ^ 2 ≤ 1 ∧ (aW - cStar) ^ 2 + hW ^ 2 ≤ 1 ∧
      weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
          (chordChartFirst sideP aP hP zP) (chordChartSecond sideP cStar aP hP zP)
          (chordChartFirst sideW aW hW zW) (chordChartSecond sideW cStar aW hW zW) =
        weightedPairScore e cStar endpointLambda endpointMu p₁ p₂ w₁ w₂ := by
  obtain ⟨orientation, horientation, hupper, hroot, hscore⟩ :=
    exists_oriented_weightedPairScore e p₁ p₂ w₁ w₂ he
  have horientationSq : orientation ^ 2 = 1 := by
    rcases horientation with rfl | rfl <;> norm_num
  let P₁ := orientedCoordinates e orientation p₁
  let P₂ := orientedCoordinates e orientation p₂
  let W₁ := orientedCoordinates e orientation w₁
  let W₂ := orientedCoordinates e orientation w₂
  have hPChord : ‖P₁ - P₂‖ = cStar := by
    dsimp only [P₁, P₂]
    rw [← orientedCoordinates_sub,
      norm_orientedCoordinates e (p₁ - p₂) he horientationSq]
    exact hpChord
  have hWChord : ‖W₁ - W₂‖ = cStar := by
    dsimp only [W₁, W₂]
    rw [← orientedCoordinates_sub,
      norm_orientedCoordinates e (w₁ - w₂) he horientationSq]
    exact hwChord
  have hPUpper : 0 ≤ (cStar⁻¹ • (P₁ - P₂) : Plane) 1 := by
    have hdiff : 0 ≤ (P₁ - P₂) 1 := by
      simpa [P₁, P₂, ← orientedCoordinates_sub] using hupper
    simp only [PiLp.smul_apply]
    exact mul_nonneg (inv_nonneg.mpr cStar_pos.le) hdiff
  obtain ⟨sideP, zP, aP, hP, hsideP, hzPZero, hzPOne, hP₁, hP₂⟩ :=
    exists_chordChart_nonnegative cStar_pos hPChord hPUpper
  obtain ⟨sideW, zW, aW, hW, hsideW, hzWNegOne, hzWOne, hW₁, hW₂⟩ :=
    exists_chordChart cStar_pos hWChord
  have hsidePSq : sideP ^ 2 = 1 := by rcases hsideP with rfl | rfl <;> norm_num
  have hsideWSq : sideW ^ 2 = 1 := by rcases hsideW with rfl | rfl <;> norm_num
  have hP₁Norm : ‖P₁‖ ≤ 1 := by
    dsimp only [P₁]
    rw [norm_orientedCoordinates e p₁ he horientationSq]
    exact hp₁
  have hP₂Norm : ‖P₂‖ ≤ 1 := by
    dsimp only [P₂]
    rw [norm_orientedCoordinates e p₂ he horientationSq]
    exact hp₂
  have hW₁Norm : ‖W₁‖ ≤ 1 := by
    dsimp only [W₁]
    rw [norm_orientedCoordinates e w₁ he horientationSq]
    exact hw₁
  have hW₂Norm : ‖W₂‖ ≤ 1 := by
    dsimp only [W₂]
    rw [norm_orientedCoordinates e w₂ he horientationSq]
    exact hw₂
  have hPFirst : aP ^ 2 + hP ^ 2 ≤ 1 := by
    have hsquare : ‖P₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg P₁]
    rw [hP₁, norm_chordChartFirst_sq aP hP zP hsidePSq] at hsquare
    exact hsquare
  have hPSecond : (aP - cStar) ^ 2 + hP ^ 2 ≤ 1 := by
    have hsquare : ‖P₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg P₂]
    rw [hP₂, norm_chordChartSecond_sq cStar aP hP zP hsidePSq] at hsquare
    exact hsquare
  have hWFirst : aW ^ 2 + hW ^ 2 ≤ 1 := by
    have hsquare : ‖W₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg W₁]
    rw [hW₁, norm_chordChartFirst_sq aW hW zW hsideWSq] at hsquare
    exact hsquare
  have hWSecond : (aW - cStar) ^ 2 + hW ^ 2 ≤ 1 := by
    have hsquare : ‖W₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg W₂]
    rw [hW₂, norm_chordChartSecond_sq cStar aW hW zW hsideWSq] at hsquare
    exact hsquare
  refine ⟨sideP, zP, aP, hP, sideW, zW, aW, hW, hsideP, hsideW,
    hzPZero, hzPOne, hzWNegOne, hzWOne, hPFirst, hPSecond, hWFirst, hWSecond, ?_⟩
  rw [← hscore, hroot, ← hP₁, ← hP₂, ← hW₁, ← hW₂]

/-- The mixed weighted inequality on all sixteen rational lens charts. -/
def WeightedLensChartBound : Prop :=
  ∀ sideP zP aP hP sideW zW aW hW : ℝ,
    (sideP = 1 ∨ sideP = -1) → (sideW = 1 ∨ sideW = -1) →
    0 ≤ zP → zP ≤ 1 → -1 ≤ zW → zW ≤ 1 →
    aP ^ 2 + hP ^ 2 ≤ 1 → (aP - cStar) ^ 2 + hP ^ 2 ≤ 1 →
    aW ^ 2 + hW ^ 2 ≤ 1 → (aW - cStar) ^ 2 + hW ^ 2 ≤ 1 →
    weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
      (chordChartFirst sideP aP hP zP) (chordChartSecond sideP cStar aP hP zP)
      (chordChartFirst sideW aW hW zW) (chordChartSecond sideW cStar aW hW zW) ≤ 0

/-- The chart inequality gives the coordinate-free mixed bound for endpoint-length chords. -/
theorem weightedPairScore_nonpos_of_lensChartBound (hchart : WeightedLensChartBound)
    (e p₁ p₂ w₁ w₂ : Plane) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hpChord : ‖p₁ - p₂‖ = cStar) (hwChord : ‖w₁ - w₂‖ = cStar) :
    weightedPairScore e cStar endpointLambda endpointMu p₁ p₂ w₁ w₂ ≤ 0 := by
  obtain ⟨sideP, zP, aP, hP, sideW, zW, aW, hW, hsideP, hsideW,
      hzPZero, hzPOne, hzWNegOne, hzWOne, hPFirst, hPSecond, hWFirst, hWSecond,
      hscore⟩ :=
    exists_weightedPairScore_lensChart e p₁ p₂ w₁ w₂ he hp₁ hp₂ hw₁ hw₂ hpChord hwChord
  rw [← hscore]
  exact hchart sideP zP aP hP sideW zW aW hW hsideP hsideW hzPZero hzPOne
    hzWNegOne hzWOne hPFirst hPSecond hWFirst hWSecond

/-- Radial chord reduction extends the lens-chart bound to sibling distances at least `cStar`. -/
theorem weightedPairScore_nonpos_of_lensChartBound_of_separated
    (hchart : WeightedLensChartBound) (e p₁ p₂ w₁ w₂ : Plane) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hpChord : cStar ≤ ‖p₁ - p₂‖) (hwChord : cStar ≤ ‖w₁ - w₂‖) :
    weightedPairScore e cStar endpointLambda endpointMu p₁ p₂ w₁ w₂ ≤ 0 := by
  obtain ⟨p₂', w₂', hpChord', hwChord', hp₂'Norm, hw₂'Norm, hscore⟩ :=
    exists_weightedPairScore_chord_reduction e one_lt_cStar_and_cStar_lt_two.1 hp₁ hw₁
      hpChord hwChord endpointMu_pos.le endpoint_weight_reduction_margin
  apply hscore.trans
  exact weightedPairScore_nonpos_of_lensChartBound hchart e p₁ p₂' w₁ w₂' he hp₁
    (hp₂'Norm.trans hp₂) hw₁ (hw₂'Norm.trans hw₂) hpChord' hwChord'

end Bescovitch
