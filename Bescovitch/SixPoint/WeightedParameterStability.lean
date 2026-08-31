/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.EndpointTightBounds
public import Bescovitch.SixPoint.WeightedReduction

/-!
# Stability of the weighted score

The mixed certificate uses rational centres for the three algebraic endpoint parameters.  Their
proved enclosures are so narrow that replacing the parameters, and shortening each second chord
endpoint by the same amount, changes the score by less than `10⁻⁸`.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- The rational chord value used in the mixed certificate. -/
def certificateChord : ℝ := 13866128436518096 / 10 ^ 16

/-- The rational centre used for the first endpoint weight. -/
def certificateLambda : ℝ := 8947642540885 / 10 ^ 14

/-- The rational centre used for the second endpoint weight. -/
def certificateMu : ℝ := 92883833887540 / 10 ^ 14

theorem cStar_certificateChord_distance :
    0 ≤ cStar - certificateChord ∧ cStar - certificateChord ≤ 1 / 10 ^ 15 := by
  have hcLower := cStar_mem_isolation_box.1
  have hcUpper := cStar_mem_isolation_box.2
  rw [certificateChord]
  constructor
  · linarith
  · norm_num at hcUpper ⊢
    linarith

theorem endpointLambda_certificate_distance :
    |endpointLambda - certificateLambda| ≤ 1 / 10 ^ 12 := by
  have hlower := endpointLambda_tight_bounds.1
  have hupper := endpointLambda_tight_bounds.2
  rw [abs_le, certificateLambda]
  norm_num at hlower hupper ⊢
  constructor <;> linarith

theorem endpointMu_certificate_distance :
    |endpointMu - certificateMu| ≤ 1 / 10 ^ 12 := by
  have hlower := endpointMu_tight_bounds.1
  have hupper := endpointMu_tight_bounds.2
  rw [abs_le, certificateMu]
  norm_num at hlower hupper ⊢
  constructor <;> linarith

private theorem firstPenalty_certificate_distance :
    |weightedFirstPenalty cStar endpointLambda endpointMu -
      weightedFirstPenalty certificateChord certificateLambda certificateMu| ≤ 1 / 10 ^ 10 := by
  have hcLower := cStar_mem_isolation_box.1.le
  have hcUpper := cStar_mem_isolation_box.2.le
  have hlower := endpointLambda_tight_bounds.1
  have hupper := endpointLambda_tight_bounds.2
  have hmuLower := endpointMu_tight_bounds.1
  have hmuUpper := endpointMu_tight_bounds.2
  rw [abs_le]
  simp only [weightedFirstPenalty, certificateChord, certificateLambda, certificateMu]
  norm_num at hcLower hcUpper hlower hupper hmuLower hmuUpper ⊢
  constructor <;> nlinarith

private theorem secondPenalty_certificate_distance :
    |weightedSecondPenalty cStar endpointLambda endpointMu -
      weightedSecondPenalty certificateChord certificateLambda certificateMu| ≤ 1 / 10 ^ 10 := by
  have hcLower := cStar_mem_isolation_box.1.le
  have hcUpper := cStar_mem_isolation_box.2.le
  have hlower := endpointLambda_tight_bounds.1
  have hupper := endpointLambda_tight_bounds.2
  have hmuLower := endpointMu_tight_bounds.1
  have hmuUpper := endpointMu_tight_bounds.2
  rw [abs_le]
  simp only [weightedSecondPenalty, certificateChord, certificateLambda, certificateMu]
  norm_num at hcLower hcUpper hlower hupper hmuLower hmuUpper ⊢
  constructor <;> nlinarith

private theorem constantTerm_certificate_distance :
    |weightedConstantTerm cStar endpointLambda endpointMu -
      weightedConstantTerm certificateChord certificateLambda certificateMu| ≤ 1 / 10 ^ 10 := by
  have hcLower := cStar_mem_isolation_box.1.le
  have hcUpper := cStar_mem_isolation_box.2.le
  have hlower := endpointLambda_tight_bounds.1
  have hupper := endpointLambda_tight_bounds.2
  have hmuLower := endpointMu_tight_bounds.1
  have hmuUpper := endpointMu_tight_bounds.2
  rw [abs_le]
  simp only [weightedConstantTerm, certificateChord, certificateLambda, certificateMu]
  norm_num at hcLower hcUpper hlower hupper hmuLower hmuUpper ⊢
  constructor <;> nlinarith

theorem certificateLambda_nonneg : 0 ≤ certificateLambda := by
  norm_num [certificateLambda]

theorem certificateMu_nonneg : 0 ≤ certificateMu := by
  norm_num [certificateMu]

theorem certificate_firstPenalty_nonneg :
    0 ≤ weightedFirstPenalty certificateChord certificateLambda certificateMu := by
  norm_num [weightedFirstPenalty, certificateChord, certificateLambda, certificateMu]

theorem certificate_secondPenalty_nonneg :
    0 ≤ weightedSecondPenalty certificateChord certificateLambda certificateMu := by
  norm_num [weightedSecondPenalty, certificateChord, certificateLambda, certificateMu]

private theorem certificate_secondPenalty_le_five :
    weightedSecondPenalty certificateChord certificateLambda certificateMu ≤ 5 := by
  norm_num [weightedSecondPenalty, certificateChord, certificateLambda, certificateMu]

private theorem norm_pair_perturbation
    {E : Type*} [NormedAddCommGroup E] (e p q p' q' : E)
    {delta : ℝ} (hp : ‖p - p'‖ ≤ delta) (hq : ‖q - q'‖ ≤ delta) :
    |‖e - p - q‖ - ‖e - p' - q'‖| ≤ 2 * delta := by
  calc
    |‖e - p - q‖ - ‖e - p' - q'‖| ≤ ‖(e - p - q) - (e - p' - q')‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖-(p - p') - (q - q')‖ := by congr 1; abel
    _ ≤ ‖-(p - p')‖ + ‖q - q'‖ := norm_sub_le _ _
    _ ≤ 2 * delta := by rw [norm_neg]; linarith

private theorem norm_single_perturbation
    {E : Type*} [NormedAddCommGroup E] (e p p' : E)
    {delta : ℝ} (hp : ‖p - p'‖ ≤ delta) :
    |‖e - p‖ - ‖e - p'‖| ≤ delta := by
  calc
    |‖e - p‖ - ‖e - p'‖| ≤ ‖(e - p) - (e - p')‖ := abs_norm_sub_norm_le _ _
    _ = ‖-(p - p')‖ := by congr 1; abel
    _ = ‖p - p'‖ := norm_neg _
    _ ≤ delta := hp

/-- Replacing the algebraic endpoint data by the rational certificate data changes the mixed
score by at most `10⁻⁸`. -/
theorem weightedPairScore_le_certificateScore_add
    {E : Type*} [NormedAddCommGroup E] (e p₁ p₂ p₂' w₁ w₂ w₂' : E)
    (he : ‖e‖ ≤ 1) (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hp₂' : ‖p₂'‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1) (hw₂' : ‖w₂'‖ ≤ 1)
    (hp₂dist : ‖p₂ - p₂'‖ ≤ 1 / 10 ^ 15)
    (hw₂dist : ‖w₂ - w₂'‖ ≤ 1 / 10 ^ 15) :
    weightedPairScore e cStar endpointLambda endpointMu p₁ p₂ w₁ w₂ ≤
      weightedPairScore e certificateChord certificateLambda certificateMu p₁ p₂' w₁ w₂' +
        1 / 10 ^ 8 := by
  have hlambda := endpointLambda_certificate_distance
  have hmu := endpointMu_certificate_distance
  have hfirst := firstPenalty_certificate_distance
  have hsecond := secondPenalty_certificate_distance
  have hconstant := constantTerm_certificate_distance
  have h11 : ‖e - p₁ - w₁‖ ≤ 3 :=
    (norm_sub_le (e - p₁) w₁).trans (by linarith [norm_sub_le e p₁])
  have h22 := norm_pair_perturbation e p₂ w₂ p₂' w₂' hp₂dist hw₂dist
  have h12 := norm_single_perturbation (e - p₁) w₂ w₂' hw₂dist
  have h21 := norm_single_perturbation (e - w₁) p₂ p₂' hp₂dist
  have hpositiveActual :
      ‖e - p₁‖ + ‖e - w₁‖ + ‖e - p₁ - w₂‖ + ‖e - w₁ - p₂‖ ≤ 12 := by
    have hP : ‖e - p₁‖ ≤ 2 := (norm_sub_le e p₁).trans (by linarith)
    have hW : ‖e - w₁‖ ≤ 2 := (norm_sub_le e w₁).trans (by linarith)
    have hPW : ‖e - p₁ - w₂‖ ≤ 3 :=
      (norm_sub_le (e - p₁) w₂).trans (by linarith [norm_sub_le e p₁])
    have hWP : ‖e - w₁ - p₂‖ ≤ 3 :=
      (norm_sub_le (e - w₁) p₂).trans (by linarith [norm_sub_le e w₁])
    linarith
  have hfirstRadii : ‖p₁‖ + ‖w₁‖ ≤ 2 := by linarith
  have hsecondRadii : ‖p₂‖ + ‖w₂‖ ≤ 2 := by linarith
  have hsecondRadiiPerturbation :
      |(‖p₂‖ + ‖w₂‖) - (‖p₂'‖ + ‖w₂'‖)| ≤ 2 / 10 ^ 15 := by
    have hp := abs_norm_sub_norm_le p₂ p₂'
    have hw := abs_norm_sub_norm_le w₂ w₂'
    have hpAbs : |‖p₂‖ - ‖p₂'‖| ≤ 1 / 10 ^ 15 := hp.trans hp₂dist
    have hwAbs : |‖w₂‖ - ‖w₂'‖| ≤ 1 / 10 ^ 15 := hw.trans hw₂dist
    calc
      |(‖p₂‖ + ‖w₂‖) - (‖p₂'‖ + ‖w₂'‖)| =
          |(‖p₂‖ - ‖p₂'‖) + (‖w₂‖ - ‖w₂'‖)| := by ring_nf
      _ ≤ |‖p₂‖ - ‖p₂'‖| + |‖w₂‖ - ‖w₂'‖| := abs_add_le _ _
      _ ≤ 2 / 10 ^ 15 := by norm_num at hpAbs hwAbs ⊢; linarith
  have hpositiveCertificate :
      ‖e - p₁‖ + ‖e - w₁‖ + ‖e - p₁ - w₂'‖ + ‖e - w₁ - p₂'‖ ≤ 12 := by
    have hP : ‖e - p₁‖ ≤ 2 := (norm_sub_le e p₁).trans (by linarith)
    have hW : ‖e - w₁‖ ≤ 2 := (norm_sub_le e w₁).trans (by linarith)
    have hPW : ‖e - p₁ - w₂'‖ ≤ 3 :=
      (norm_sub_le (e - p₁) w₂').trans (by linarith [norm_sub_le e p₁])
    have hWP : ‖e - w₁ - p₂'‖ ≤ 3 :=
      (norm_sub_le (e - w₁) p₂').trans (by linarith [norm_sub_le e w₁])
    linarith
  have hprimary :
      (1 + endpointLambda) * ‖e - p₁ - w₁‖ ≤
        (1 + certificateLambda) * ‖e - p₁ - w₁‖ + 3 / 10 ^ 12 := by
    have hdiff := (abs_le.mp hlambda).2
    have hmul := mul_le_mul_of_nonneg_right hdiff (norm_nonneg (e - p₁ - w₁))
    nlinarith
  have hsecondNorm :
      ‖e - p₂ - w₂‖ ≤ ‖e - p₂' - w₂'‖ + 2 / 10 ^ 15 := by
    have := (abs_le.mp h22).2
    norm_num at this ⊢
    linarith
  have hpositiveTerms :
      endpointMu / 2 *
          (‖e - p₁‖ + ‖e - w₁‖ + ‖e - p₁ - w₂‖ + ‖e - w₁ - p₂‖) ≤
        certificateMu / 2 *
          (‖e - p₁‖ + ‖e - w₁‖ + ‖e - p₁ - w₂'‖ + ‖e - w₁ - p₂'‖) +
          6 / 10 ^ 12 + 1 / 10 ^ 15 := by
    have hsum :
        ‖e - p₁‖ + ‖e - w₁‖ + ‖e - p₁ - w₂‖ + ‖e - w₁ - p₂‖ ≤
          ‖e - p₁‖ + ‖e - w₁‖ + ‖e - p₁ - w₂'‖ + ‖e - w₁ - p₂'‖ +
            2 / 10 ^ 15 := by
      have h12Upper := (abs_le.mp h12).2
      have h21Upper := (abs_le.mp h21).2
      linarith
    have hmuUpper := (abs_le.mp hmu).2
    have hmuActual : 0 ≤ endpointMu := endpointMu_pos.le
    have hmuCertificate : certificateMu ≤ 1 := by norm_num [certificateMu]
    have hparameter := mul_le_mul_of_nonneg_right hmuUpper
      (by positivity : 0 ≤ (‖e - p₁‖ + ‖e - w₁‖ + ‖e - p₁ - w₂‖ +
        ‖e - w₁ - p₂‖) / 2)
    have hhalfMu : 0 ≤ certificateMu / 2 :=
      div_nonneg certificateMu_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    have hgeometry := mul_le_mul_of_nonneg_left hsum hhalfMu
    norm_num at hparameter hgeometry ⊢
    nlinarith
  have hfirstPenaltyTerm :
      -(weightedFirstPenalty cStar endpointLambda endpointMu / 2 * (‖p₁‖ + ‖w₁‖)) ≤
        -(weightedFirstPenalty certificateChord certificateLambda certificateMu / 2 *
          (‖p₁‖ + ‖w₁‖)) + 1 / 10 ^ 10 := by
    have hdiff := (abs_le.mp hfirst).1
    have hhalfRadii : 0 ≤ (‖p₁‖ + ‖w₁‖) / 2 :=
      div_nonneg (add_nonneg (norm_nonneg p₁) (norm_nonneg w₁))
        (by norm_num : (0 : ℝ) ≤ 2)
    have hmul := mul_le_mul_of_nonneg_right
      (show weightedFirstPenalty certificateChord certificateLambda certificateMu -
          weightedFirstPenalty cStar endpointLambda endpointMu ≤ 1 / 10 ^ 10 by linarith)
      hhalfRadii
    nlinarith
  have hsecondPenaltyTerm :
      -(weightedSecondPenalty cStar endpointLambda endpointMu / 2 * (‖p₂‖ + ‖w₂‖)) ≤
        -(weightedSecondPenalty certificateChord certificateLambda certificateMu / 2 *
          (‖p₂'‖ + ‖w₂'‖)) + 1 / 10 ^ 10 + 5 / 10 ^ 15 := by
    have hparameterDifference :
        weightedSecondPenalty certificateChord certificateLambda certificateMu -
          weightedSecondPenalty cStar endpointLambda endpointMu ≤ 1 / 10 ^ 10 := by
      linarith [(abs_le.mp hsecond).1]
    have hhalfRadii : 0 ≤ (‖p₂‖ + ‖w₂‖) / 2 :=
      div_nonneg (add_nonneg (norm_nonneg p₂) (norm_nonneg w₂))
        (by norm_num : (0 : ℝ) ≤ 2)
    have hparameter := mul_le_mul_of_nonneg_right hparameterDifference hhalfRadii
    have hradii := (abs_le.mp hsecondRadiiPerturbation).1
    have hhalfPenalty : 0 ≤
        weightedSecondPenalty certificateChord certificateLambda certificateMu / 2 :=
      div_nonneg certificate_secondPenalty_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    have hgeometry := mul_le_mul_of_nonneg_left
      (show (‖p₂'‖ + ‖w₂'‖) - (‖p₂‖ + ‖w₂‖) ≤ 2 / 10 ^ 15 by linarith)
      hhalfPenalty
    nlinarith only [hparameter, hgeometry, hsecondRadii,
      certificate_secondPenalty_le_five]
  have hconstantTerm :
      -weightedConstantTerm cStar endpointLambda endpointMu ≤
        -weightedConstantTerm certificateChord certificateLambda certificateMu + 1 / 10 ^ 10 := by
    linarith [(abs_le.mp hconstant).1]
  rw [weightedPairScore, weightedPairScore]
  norm_num at hprimary hsecondNorm hpositiveTerms hfirstPenaltyTerm hsecondPenaltyTerm hconstantTerm ⊢
  linarith only [hprimary, hsecondNorm, hpositiveTerms, hfirstPenaltyTerm,
    hsecondPenaltyTerm, hconstantTerm]

end Bescovitch
