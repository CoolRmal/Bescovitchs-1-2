/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedEqualityFace
public import Bescovitch.SixPoint.WeightedMixedEqualityTransverse

/-!
# The analytic equality neighborhood

Inside the one exceptional mixed-chart neighborhood, monotonicity moves both chords to the
upper disk face and antisymmetric concavity moves them to a common chord. The self inequality
then closes the estimate.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Bescovitch.WeightedMixedEqualityLocal

private def faceScore (c lambda mu tP zP tW zW : ℝ) : ℝ :=
  weightedPairScore !₂[1, 0] c lambda mu
    (chordChartFirst (-1) (topFaceLongitudinal tP) (topFaceHeight tP) zP)
    (chordChartSecond (-1) c (topFaceLongitudinal tP) (topFaceHeight tP) zP)
    (chordChartFirst (-1) (topFaceLongitudinal tW) (topFaceHeight tW) zW)
    (chordChartSecond (-1) c (topFaceLongitudinal tW) (topFaceHeight tW) zW)

private theorem face_circle (t : ℝ) :
    topFaceLongitudinal t ^ 2 + topFaceHeight t ^ 2 = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  simp only [topFaceLongitudinal, topFaceHeight]
  field_simp [hden]
  ring

private theorem two_top_face_longitudinal_ge_c_star (t : ℝ) (htLower : 0 ≤ t)
    (ht : t ≤ 0.2754) : cStar ≤ 2 * topFaceLongitudinal t := by
  have htSq : t ^ 2 ≤ (2754 / 10000 : ℝ) ^ 2 :=
    (sq_le_sq₀ htLower (by norm_num)).2 (by norm_num at ht ⊢; exact ht)
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hc := cStar_mem_isolation_box.2.le
  norm_num at hc
  rw [topFaceLongitudinal]
  apply hc.trans
  rw [show 2 * ((1 - t ^ 2) / (1 + t ^ 2)) =
    (2 * (1 - t ^ 2)) / (1 + t ^ 2) by ring, le_div_iff₀ hden]
  nlinarith

private theorem face_score_diagonal_nonpos
    (self_nonpos : ∀ p₁ p₂ : EuclideanSpace ℝ (Fin 2),
      ‖p₁‖ ≤ 1 → ‖p₂‖ ≤ 1 → cStar ≤ ‖p₁ - p₂‖ →
      weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu p₁ p₂ p₁ p₂ ≤ 0)
    (t z : ℝ) (ht : 0.2745 ≤ t ∧ t ≤ 0.2754) :
    faceScore cStar endpointLambda endpointMu t z t z ≤ 0 := by
  let p₁ := chordChartFirst (-1) (topFaceLongitudinal t) (topFaceHeight t) z
  let p₂ := chordChartSecond (-1) cStar (topFaceLongitudinal t) (topFaceHeight t) z
  have hp₁sq : ‖p₁‖ ^ 2 = 1 := by
    rw [show ‖p₁‖ ^ 2 = topFaceLongitudinal t ^ 2 + topFaceHeight t ^ 2 by
      simpa [p₁] using norm_chordChartFirst_sq (topFaceLongitudinal t) (topFaceHeight t) z
        (show (-1 : ℝ) ^ 2 = 1 by norm_num)]
    exact face_circle t
  have hp₁ : ‖p₁‖ ≤ 1 := by nlinarith [norm_nonneg p₁]
  have hp₂sq : ‖p₂‖ ^ 2 =
      (topFaceLongitudinal t - cStar) ^ 2 + topFaceHeight t ^ 2 := by
    simpa [p₂] using
      norm_chordChartSecond_sq cStar (topFaceLongitudinal t) (topFaceHeight t) z
      (show (-1 : ℝ) ^ 2 = 1 by norm_num)
  have hp₂ : ‖p₂‖ ≤ 1 := by
    have hc : cStar ≤ 2 * topFaceLongitudinal t :=
      two_top_face_longitudinal_ge_c_star t (by linarith [ht.1]) ht.2
    have hsq : ‖p₂‖ ^ 2 ≤ 1 := by
      rw [hp₂sq, ← face_circle t]
      nlinarith [cStar_pos.le]
    nlinarith [norm_nonneg p₂]
  have hchord : ‖p₁ - p₂‖ = cStar := by
    exact norm_chordChartFirst_sub_second (topFaceLongitudinal t) (topFaceHeight t) z
      (show (-1 : ℝ) ^ 2 = 1 by norm_num) cStar_pos.le
  have hscore := self_nonpos p₁ p₂ hp₁ hp₂ hchord.ge
  simpa [faceScore, p₁, p₂] using hscore

private theorem top_face_transport (a h : ℝ)
    (ha : (85902 : ℝ) / 100000 ≤ a ∧ a ≤ 85984 / 100000)
    (hdisk : a ^ 2 + h ^ 2 ≤ 1) :
    let H := Real.sqrt (1 - a ^ 2)
    let t := H / (1 + a)
    h ≤ H ∧ (2745 : ℝ) / 10000 ≤ t ∧ t ≤ 2754 / 10000 ∧
      topFaceLongitudinal t = a ∧ topFaceHeight t = H := by
  let H := Real.sqrt (1 - a ^ 2)
  let t := H / (1 + a)
  change h ≤ H ∧ (2745 : ℝ) / 10000 ≤ t ∧ t ≤ 2754 / 10000 ∧
    topFaceLongitudinal t = a ∧ topFaceHeight t = H
  have haZero : 0 ≤ a := by linarith [ha.1]
  have haOne : a < 1 := by linarith [ha.2]
  have hradicand : 0 ≤ 1 - a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haOne.le) (by linarith : 0 ≤ 1 + a)]
  have hHZero : 0 ≤ H := Real.sqrt_nonneg _
  have hHSq : H ^ 2 = 1 - a ^ 2 := Real.sq_sqrt hradicand
  have hOneA : 0 < 1 + a := by linarith
  have htZero : 0 ≤ t := div_nonneg hHZero hOneA.le
  have hhSq : h ^ 2 ≤ H ^ 2 := by nlinarith
  have hhUpper : h ≤ H := by
    by_cases hhZero : 0 ≤ h
    · exact (sq_le_sq₀ hhZero hHZero).mp hhSq
    · exact (le_of_not_ge hhZero).trans hHZero
  have haSqUpper : a ^ 2 ≤ ((85984 : ℝ) / 100000) ^ 2 :=
    (sq_le_sq₀ haZero (by norm_num)).2 ha.2
  have hOneASqUpper : (1 + a) ^ 2 ≤ (1 + (85984 : ℝ) / 100000) ^ 2 := by
    apply (sq_le_sq₀ hOneA.le (by norm_num)).2
    linarith
  have hLowerEndpoint :
      (((2745 : ℝ) / 10000) * (1 + 85984 / 100000)) ^ 2 ≤
        1 - ((85984 : ℝ) / 100000) ^ 2 := by norm_num
  have hLowerSquare : (((2745 : ℝ) / 10000) * (1 + a)) ^ 2 ≤ H ^ 2 := by
    calc
      _ = ((2745 : ℝ) / 10000) ^ 2 * (1 + a) ^ 2 := by ring
      _ ≤ ((2745 : ℝ) / 10000) ^ 2 * (1 + 85984 / 100000) ^ 2 :=
        mul_le_mul_of_nonneg_left hOneASqUpper (sq_nonneg _)
      _ = (((2745 : ℝ) / 10000) * (1 + 85984 / 100000)) ^ 2 := by ring
      _ ≤ 1 - ((85984 : ℝ) / 100000) ^ 2 := hLowerEndpoint
      _ ≤ 1 - a ^ 2 := by linarith
      _ = H ^ 2 := hHSq.symm
  have hLowerNumerator : (2745 : ℝ) / 10000 * (1 + a) ≤ H :=
    (sq_le_sq₀ (mul_nonneg (by norm_num) hOneA.le) hHZero).mp hLowerSquare
  have htLower : (2745 : ℝ) / 10000 ≤ t := by
    dsimp [t]
    exact (le_div_iff₀ hOneA).2 hLowerNumerator
  have haSqLower : ((85902 : ℝ) / 100000) ^ 2 ≤ a ^ 2 :=
    (sq_le_sq₀ (by norm_num) haZero).2 ha.1
  have hOneASqLower : (1 + (85902 : ℝ) / 100000) ^ 2 ≤ (1 + a) ^ 2 := by
    apply (sq_le_sq₀ (by norm_num) hOneA.le).2
    linarith
  have hUpperEndpoint :
      1 - ((85902 : ℝ) / 100000) ^ 2 ≤
        (((2754 : ℝ) / 10000) * (1 + 85902 / 100000)) ^ 2 := by norm_num
  have hUpperSquare : H ^ 2 ≤ (((2754 : ℝ) / 10000) * (1 + a)) ^ 2 := by
    calc
      H ^ 2 = 1 - a ^ 2 := hHSq
      _ ≤ 1 - ((85902 : ℝ) / 100000) ^ 2 := by linarith
      _ ≤ (((2754 : ℝ) / 10000) * (1 + 85902 / 100000)) ^ 2 := hUpperEndpoint
      _ = ((2754 : ℝ) / 10000) ^ 2 * (1 + 85902 / 100000) ^ 2 := by ring
      _ ≤ ((2754 : ℝ) / 10000) ^ 2 * (1 + a) ^ 2 :=
        mul_le_mul_of_nonneg_left hOneASqLower (sq_nonneg _)
      _ = (((2754 : ℝ) / 10000) * (1 + a)) ^ 2 := by ring
  have hUpperNumerator : H ≤ (2754 : ℝ) / 10000 * (1 + a) :=
    (sq_le_sq₀ hHZero (mul_nonneg (by norm_num) hOneA.le)).mp hUpperSquare
  have htUpper : t ≤ (2754 : ℝ) / 10000 := by
    dsimp [t]
    exact (div_le_iff₀ hOneA).2 hUpperNumerator
  have htDenominator : 0 < 1 + t ^ 2 := by positivity
  have htRelation : t ^ 2 * (1 + a) = 1 - a := by
    dsimp [t]
    field_simp [hOneA.ne']
    nlinarith
  have hfirstIdentity : topFaceLongitudinal t = a := by
    rw [topFaceLongitudinal]
    apply (div_eq_iff (ne_of_gt htDenominator)).2
    nlinarith
  have hsecondIdentity : topFaceHeight t = H := by
    rw [topFaceHeight]
    apply (div_eq_iff (ne_of_gt htDenominator)).2
    dsimp [t]
    field_simp [hOneA.ne']
    nlinarith
  exact ⟨hhUpper, htLower, htUpper, hfirstIdentity, hsecondIdentity⟩

private theorem top_face_height_bounds (a h : ℝ)
    (ha : (85902 : ℝ) / 100000 ≤ a ∧ a ≤ 85984 / 100000)
    (hdisk : a ^ 2 + h ^ 2 ≤ 1) :
    let H := Real.sqrt (1 - a ^ 2)
    (-513 : ℝ) / 1000 ≤ h ∧ h ≤ H ∧ H ≤ 513 / 1000 := by
  let H := Real.sqrt (1 - a ^ 2)
  change (-513 : ℝ) / 1000 ≤ h ∧ h ≤ H ∧ H ≤ 513 / 1000
  have haZero : 0 ≤ a := by linarith [ha.1]
  have haOne : a < 1 := by linarith [ha.2]
  have hradicand : 0 ≤ 1 - a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haOne.le) (by linarith : 0 ≤ 1 + a)]
  have hHZero : 0 ≤ H := Real.sqrt_nonneg _
  have hHSq : H ^ 2 = 1 - a ^ 2 := Real.sq_sqrt hradicand
  have haSqLower : ((85902 : ℝ) / 100000) ^ 2 ≤ a ^ 2 :=
    (sq_le_sq₀ (by norm_num) haZero).2 ha.1
  have hEndpoint : 1 - ((85902 : ℝ) / 100000) ^ 2 ≤ ((513 : ℝ) / 1000) ^ 2 := by
    norm_num
  have hHUpperSquare : H ^ 2 ≤ ((513 : ℝ) / 1000) ^ 2 := by
    rw [hHSq]
    linarith
  have hHUpper : H ≤ (513 : ℝ) / 1000 :=
    (sq_le_sq₀ hHZero (by norm_num)).mp hHUpperSquare
  have hhSq : h ^ 2 ≤ H ^ 2 := by nlinarith
  have hhUpper : h ≤ H := by
    by_cases hhZero : 0 ≤ h
    · exact (sq_le_sq₀ hhZero hHZero).mp hhSq
    · exact (le_of_not_ge hhZero).trans hHZero
  have hhLowerH : -H ≤ h := by
    by_cases hhZero : 0 ≤ h
    · exact (neg_nonpos.mpr hHZero).trans hhZero
    · have hnegZero : 0 ≤ -h := neg_nonneg.mpr (le_of_not_ge hhZero)
      have hnegLe : -h ≤ H := by
        apply (sq_le_sq₀ hnegZero hHZero).mp
        simpa only [neg_sq] using hhSq
      linarith
  refine ⟨?_, hhUpper, hHUpper⟩
  simpa only [neg_div] using (neg_le_neg hHUpper).trans hhLowerH

private theorem transverse_score_monotoneOn_second (aP hP zP aW zW : ℝ)
    (haP : 0.85902 ≤ aP ∧ aP ≤ 0.85984)
    (hhP : -0.513 ≤ hP ∧ hP ≤ 0.513)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (haW : 0.85902 ≤ aW ∧ aW ≤ 0.85984)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655) :
    MonotoneOn
      (fun h ↦ weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
        (chordChartFirst (-1) aP hP zP) (chordChartSecond (-1) cStar aP hP zP)
        (chordChartFirst (-1) aW h zW) (chordChartSecond (-1) cStar aW h zW))
      (Set.Icc (-0.513) 0.513) := by
  have hmono := (transverse_score_strict_mono_on aW zW aP hP zP
    haW hzW haP hhP hzP).monotoneOn
  intro x hx y hy hxy
  have h := hmono hx hy hxy
  simpa only [weightedPairScore_swap] using h

/-- The mixed score is nonpositive on the certified equality neighborhood, assuming the
coordinate-free self inequality. -/
theorem weighted_pair_score_nonpos_in_equality_local_box_of_self
    (self_nonpos : ∀ p₁ p₂ : EuclideanSpace ℝ (Fin 2),
      ‖p₁‖ ≤ 1 → ‖p₂‖ ≤ 1 → cStar ≤ ‖p₁ - p₂‖ →
      weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu p₁ p₂ p₁ p₂ ≤ 0)
    (aP hP zP aW hW zW : ℝ)
    (haP : 0.85902 ≤ aP ∧ aP ≤ 0.85984)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (haW : 0.85902 ≤ aW ∧ aW ≤ 0.85984)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655)
    (hPdisk : aP ^ 2 + hP ^ 2 ≤ 1)
    (hWdisk : aW ^ 2 + hW ^ 2 ≤ 1) :
    weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
      (chordChartFirst (-1) aP hP zP) (chordChartSecond (-1) cStar aP hP zP)
      (chordChartFirst (-1) aW hW zW) (chordChartSecond (-1) cStar aW hW zW) ≤ 0 := by
  let HP := Real.sqrt (1 - aP ^ 2)
  let HW := Real.sqrt (1 - aW ^ 2)
  let tP := HP / (1 + aP)
  let tW := HW / (1 + aW)
  have haP' : (85902 : ℝ) / 100000 ≤ aP ∧ aP ≤ 85984 / 100000 := by
    norm_num at haP ⊢
    exact haP
  have haW' : (85902 : ℝ) / 100000 ≤ aW ∧ aW ≤ 85984 / 100000 := by
    norm_num at haW ⊢
    exact haW
  have hPtop : hP ≤ HP ∧ (2745 : ℝ) / 10000 ≤ tP ∧ tP ≤ 2754 / 10000 ∧
      topFaceLongitudinal tP = aP ∧ topFaceHeight tP = HP := by
    simpa only [HP, tP] using top_face_transport aP hP haP' hPdisk
  have hWtop : hW ≤ HW ∧ (2745 : ℝ) / 10000 ≤ tW ∧ tW ≤ 2754 / 10000 ∧
      topFaceLongitudinal tW = aW ∧ topFaceHeight tW = HW := by
    simpa only [HW, tW] using top_face_transport aW hW haW' hWdisk
  have hPheight : (-513 : ℝ) / 1000 ≤ hP ∧ hP ≤ HP ∧ HP ≤ 513 / 1000 := by
    simpa only [HP] using top_face_height_bounds aP hP haP' hPdisk
  have hWheight : (-513 : ℝ) / 1000 ≤ hW ∧ hW ≤ HW ∧ HW ≤ 513 / 1000 := by
    simpa only [HW] using top_face_height_bounds aW hW haW' hWdisk
  have hPt : 0.2745 ≤ tP ∧ tP ≤ 0.2754 := by
    norm_num at hPtop ⊢
    exact ⟨hPtop.2.1, hPtop.2.2.1⟩
  have hWt : 0.2745 ≤ tW ∧ tW ≤ 0.2754 := by
    norm_num at hWtop ⊢
    exact ⟨hWtop.2.1, hWtop.2.2.1⟩
  have hhP : -0.513 ≤ hP ∧ hP ≤ 0.513 := by
    norm_num at hPheight ⊢
    exact ⟨hPheight.1, hPtop.1.trans hPheight.2.2⟩
  have hhW : -0.513 ≤ hW ∧ hW ≤ 0.513 := by
    norm_num at hWheight ⊢
    exact ⟨hWheight.1, hWtop.1.trans hWheight.2.2⟩
  have hHP : -0.513 ≤ HP ∧ HP ≤ 0.513 := by
    norm_num at hPheight ⊢
    exact ⟨hPheight.1.trans hPtop.1, hPheight.2.2⟩
  have hHW : -0.513 ≤ HW ∧ HW ≤ 0.513 := by
    norm_num at hWheight ⊢
    exact ⟨hWheight.1.trans hWtop.1, hWheight.2.2⟩
  let score := fun q k ↦ weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
    (chordChartFirst (-1) aP q zP) (chordChartSecond (-1) cStar aP q zP)
    (chordChartFirst (-1) aW k zW) (chordChartSecond (-1) cStar aW k zW)
  have hraiseP : score hP hW ≤ score HP hW := by
    exact (transverse_score_strict_mono_on aP zP aW hW zW haP hzP haW
      hhW hzW).monotoneOn hhP hHP hPtop.1
  have hraiseW : score HP hW ≤ score HP HW := by
    exact transverse_score_monotoneOn_second aP HP zP aW zW haP
      hHP hzP haW hzW hhW hHW hWtop.1
  have htop : score HP HW = faceScore cStar endpointLambda endpointMu tP zP tW zW := by
    simp only [score, faceScore]
    rw [hPtop.2.2.2.1, hPtop.2.2.2.2, hWtop.2.2.2.1, hWtop.2.2.2.2]
  have hface : faceScore cStar endpointLambda endpointMu tP zP tW zW ≤
      faceScore cStar endpointLambda endpointMu
        ((tP + tW) / 2) ((zP + zW) / 2) ((tP + tW) / 2) ((zP + zW) / 2) := by
    simpa only [faceScore] using
      weighted_pair_score_top_face_le_diagonal tP zP tW zW hPt hzP hWt hzW
  have hdiag := face_score_diagonal_nonpos self_nonpos ((tP + tW) / 2) ((zP + zW) / 2)
    ⟨by linarith [hPt.1, hWt.1], by linarith [hPt.2, hWt.2]⟩
  change score hP hW ≤ 0
  rw [htop] at hraiseW
  exact hraiseP.trans (hraiseW.trans (hface.trans hdiag))

end Bescovitch.WeightedMixedEqualityLocal
