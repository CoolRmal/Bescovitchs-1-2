/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedChart
public import Bescovitch.SixPoint.WeightedMajorant
public import Bescovitch.SixPoint.WeightedParameterStability

/-!
# Geometric interpretation of the mixed certificate

The exact polynomial uses a rational chord just below `cStar`.  Shortening the second endpoint
keeps it in the unit disk, and the stability theorem transfers the resulting rational majorant
back to the algebraic endpoint score.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- The pointwise rational majorant certified on a lens chart. -/
def weightedLensCertificateMajorant
    (sideP zP aP hP sideW zW aW hW : ℝ)
    (rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ : ℝ)
    (uP₁ uW₁ uP₂ uW₂ : (EuclideanSpace ℝ (Fin 2)))
    (etaP₁ etaP₂ etaW₁ etaW₂ : ℝ) : ℝ :=
  weightedPairScoreTangentMajorant !₂[1, 0]
    certificateChord certificateLambda certificateMu
    (chordChartFirst sideP aP hP zP)
    (chordChartSecond sideP certificateChord aP hP zP)
    (chordChartFirst sideW aW hW zW)
    (chordChartSecond sideW certificateChord aW hW zW)
    rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
    etaP₁ etaP₂ etaW₁ etaW₂ + 1 / 10 ^ 8

private theorem norm_le_one_of_sq_le_one {E : Type*} [NormedAddCommGroup E]
    (v : E) (h : ‖v‖ ^ 2 ≤ 1) : ‖v‖ ≤ 1 := by
  exact (sq_le_sq₀ (norm_nonneg v) (by norm_num)).1 (by simpa only [one_pow] using h)

private theorem planeRoot_norm_le_one :
    ‖(!₂[1, 0] : (EuclideanSpace ℝ (Fin 2)))‖ ≤ 1 := by
  apply norm_le_one_of_sq_le_one
  norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private theorem norm_chordChartSecond_certificate_le_one
    {side : ℝ} (a h z : ℝ) (hside : side ^ 2 = 1)
    (hfirst : a ^ 2 + h ^ 2 ≤ 1) (hsecond : (a - cStar) ^ 2 + h ^ 2 ≤ 1) :
    ‖chordChartSecond side certificateChord a h z‖ ≤ 1 := by
  have ha : a ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg h]
  have hc := cStar_certificateChord_distance.1
  have hcCertificate : 1 < certificateChord := by norm_num [certificateChord]
  have hlong : (a - certificateChord) ^ 2 ≤ (a - cStar) ^ 2 := by
    nlinarith [sq_nonneg (cStar - certificateChord)]
  apply norm_le_one_of_sq_le_one
  rw [norm_chordChartSecond_sq certificateChord a h z hside]
  linarith

private theorem norm_chordChartSecond_sub_certificate
    {side : ℝ} (a h z : ℝ) (hside : side ^ 2 = 1) :
    ‖chordChartSecond side cStar a h z -
        chordChartSecond side certificateChord a h z‖ ≤ 1 / 10 ^ 15 := by
  have hc := cStar_certificateChord_distance
  have hvector :
      chordChartSecond side cStar a h z -
          chordChartSecond side certificateChord a h z =
        (certificateChord - cStar) • stereographicDirection side z := by
    simp only [chordChartSecond]
    module
  rw [hvector, norm_smul, norm_stereographicDirection z hside, mul_one,
    Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith

/-- A nonpositive rational certificate majorant proves the exact score on the corresponding
lens chart. -/
theorem weightedPairScore_le_lensCertificateMajorant
    (sideP zP aP hP sideW zW aW hW : ℝ)
    (rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ : ℝ)
    (uP₁ uW₁ uP₂ uW₂ : (EuclideanSpace ℝ (Fin 2))) (etaP₁ etaP₂ etaW₁ etaW₂ : ℝ)
    (hsideP : sideP ^ 2 = 1) (hsideW : sideW ^ 2 = 1)
    (hPFirst : aP ^ 2 + hP ^ 2 ≤ 1) (hPSecond : (aP - cStar) ^ 2 + hP ^ 2 ≤ 1)
    (hWFirst : aW ^ 2 + hW ^ 2 ≤ 1) (hWSecond : (aW - cStar) ^ 2 + hW ^ 2 ≤ 1)
    (hrhoP : 0 < rhoP) (hrhoW : 0 < rhoW) (hrho₁₁ : 0 < rho₁₁)
    (hrho₂₂ : 0 < rho₂₂) (hrho₁₂ : 0 < rho₁₂) (hrho₂₁ : 0 < rho₂₁)
    (huP₁ : ‖uP₁‖ ≤ 1) (huW₁ : ‖uW₁‖ ≤ 1)
    (huP₂ : ‖uP₂‖ ≤ 1) (huW₂ : ‖uW₂‖ ≤ 1)
    (hetaP₁ : 0 ≤ etaP₁) (hetaP₂ : 0 ≤ etaP₂)
    (hetaW₁ : 0 ≤ etaW₁) (hetaW₂ : 0 ≤ etaW₂) :
    weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
        (chordChartFirst sideP aP hP zP) (chordChartSecond sideP cStar aP hP zP)
        (chordChartFirst sideW aW hW zW) (chordChartSecond sideW cStar aW hW zW) ≤
      weightedLensCertificateMajorant sideP zP aP hP sideW zW aW hW
        rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
        etaP₁ etaP₂ etaW₁ etaW₂ := by
  let p₁ := chordChartFirst sideP aP hP zP
  let p₂ := chordChartSecond sideP cStar aP hP zP
  let p₂' := chordChartSecond sideP certificateChord aP hP zP
  let w₁ := chordChartFirst sideW aW hW zW
  let w₂ := chordChartSecond sideW cStar aW hW zW
  let w₂' := chordChartSecond sideW certificateChord aW hW zW
  have hp₁ : ‖p₁‖ ≤ 1 := by
    apply norm_le_one_of_sq_le_one
    simpa [p₁, norm_chordChartFirst_sq aP hP zP hsideP] using hPFirst
  have hp₂ : ‖p₂‖ ≤ 1 := by
    apply norm_le_one_of_sq_le_one
    simpa [p₂, norm_chordChartSecond_sq cStar aP hP zP hsideP] using hPSecond
  have hp₂' : ‖p₂'‖ ≤ 1 := by
    exact norm_chordChartSecond_certificate_le_one aP hP zP hsideP hPFirst hPSecond
  have hw₁ : ‖w₁‖ ≤ 1 := by
    apply norm_le_one_of_sq_le_one
    simpa [w₁, norm_chordChartFirst_sq aW hW zW hsideW] using hWFirst
  have hw₂ : ‖w₂‖ ≤ 1 := by
    apply norm_le_one_of_sq_le_one
    simpa [w₂, norm_chordChartSecond_sq cStar aW hW zW hsideW] using hWSecond
  have hw₂' : ‖w₂'‖ ≤ 1 := by
    exact norm_chordChartSecond_certificate_le_one aW hW zW hsideW hWFirst hWSecond
  have hp₂dist : ‖p₂ - p₂'‖ ≤ 1 / 10 ^ 15 := by
    exact norm_chordChartSecond_sub_certificate aP hP zP hsideP
  have hw₂dist : ‖w₂ - w₂'‖ ≤ 1 / 10 ^ 15 := by
    exact norm_chordChartSecond_sub_certificate aW hW zW hsideW
  have hstability := weightedPairScore_le_certificateScore_add !₂[1, 0]
    p₁ p₂ p₂' w₁ w₂ w₂' planeRoot_norm_le_one
    hp₁ hp₂ hp₂' hw₁ hw₂ hw₂' hp₂dist hw₂dist
  have htangent := weightedPairScore_le_tangentMajorant !₂[1, 0]
    certificateChord certificateLambda certificateMu p₁ p₂' w₁ w₂'
    rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
    etaP₁ etaP₂ etaW₁ etaW₂ planeRoot_norm_le_one
    hp₁ hp₂' hw₁ hw₂' certificateMu_nonneg (by norm_num [certificateLambda])
    certificate_firstPenalty_nonneg certificate_secondPenalty_nonneg
    hrhoP hrhoW hrho₁₁ hrho₂₂ hrho₁₂ hrho₂₁ huP₁ huW₁ huP₂ huW₂
    hetaP₁ hetaP₂ hetaW₁ hetaW₂
  calc
    _ ≤ weightedPairScore !₂[1, 0] certificateChord certificateLambda certificateMu
          p₁ p₂' w₁ w₂' + 1 / 10 ^ 8 := hstability
    _ ≤ weightedPairScoreTangentMajorant !₂[1, 0]
          certificateChord certificateLambda certificateMu p₁ p₂' w₁ w₂'
          rhoP rhoW rho₁₁ rho₂₂ rho₁₂ rho₂₁ uP₁ uW₁ uP₂ uW₂
          etaP₁ etaP₂ etaW₁ etaW₂ + 1 / 10 ^ 8 := add_le_add_left htangent _
    _ = _ := by
      rfl

end Bescovitch
