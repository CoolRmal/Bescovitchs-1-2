/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedSymmetry
import Bescovitch.SixPoint.WeightedMixedRootCover

/-!
# Geometric soundness of a mixed-certificate tree

A successful exact tree check bounds the original mixed weighted score on its root box.  This
module is the bridge between the rational Bernstein computation and the geometric inequality.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

open WeightedMixedPolynomial

namespace WeightedMixedLeaf

/-- The rational quadratic majorant represented by one certified leaf. -/
def quadraticMajorant (data : WeightedMixedLeaf)
    (sideP zP aP hP sideW zW aW hW : ℝ) : ℝ :=
  weightedLensQuadraticCertificateMajorant sideP zP aP hP sideW zW aW hW
    (data.rho 0) (data.rho 1) (data.rho 2) (data.rho 3) (data.rho 4) (data.rho 5)
    (stereographicDirection 1 (data.supportSlope 0))
    (stereographicDirection 1 (data.supportSlope 1))
    (stereographicDirection 1 (data.supportSlope 2))
    (stereographicDirection 1 (data.supportSlope 3))
    (data.slack 0) (data.slack 1) (data.slack 2) (data.slack 3)

end WeightedMixedLeaf

private theorem leaf_parameter_pos (data : WeightedMixedLeaf)
    (hdata : ∀ i, 0 < data.rhoNumerator i) (i : Fin 6) :
    0 < (data.rho i : ℝ) := by
  rw [WeightedMixedLeaf.rho]
  norm_num only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, div_pos_iff]
  exact Or.inl ⟨by exact_mod_cast hdata i, by norm_num⟩

private theorem leaf_support_norm_le_one (data : WeightedMixedLeaf) (i : Fin 4) :
    ‖stereographicDirection 1 (data.supportSlope i)‖ ≤ 1 := by
  rw [norm_stereographicDirection (side := (1 : ℝ)) _ (by norm_num)]

private theorem leaf_slack_nonneg (data : WeightedMixedLeaf) (i : Fin 4) :
    0 ≤ (data.slack i : ℝ) := by
  rw [WeightedMixedLeaf.slack]
  positivity

private theorem leaf_quadratic_majorant_nonpos
    (sideP sideW : ℚ) (leafBox : Fin 6 → RationalInterval)
    (data : WeightedMixedLeaf) (x : Fin 6 → ℝ)
    (hrho : ∀ i, 0 < data.rhoNumerator i)
    (hx : ∀ i, (leafBox i).Contains (x i))
    (hpolynomial : MultivariateDensePolynomial.eval
      (polynomialOfLeaf sideP sideW (fun i ↦ (leafBox i).lower)
        (fun i ↦ (leafBox i).upper) data)
      (fun i ↦ (leafBox i).centeredCoordinate (x i)) ≤ 0)
    (hsideP : (sideP : ℝ) ^ 2 = 1) (hsideW : (sideW : ℝ) ^ 2 = 1) :
    data.quadraticMajorant sideP (x 2) (x 0) (x 1) sideW (x 5) (x 3) (x 4) ≤ 0 := by
  let y : Fin 6 → ℝ := fun i ↦ (leafBox i).centeredCoordinate (x i)
  have hcoordinate (i : Fin 6) :
      MultivariateDensePolynomial.eval
          (affineCoordinate i (leafBox i).lower (leafBox i).upper) y = x i :=
    eval_affine_coordinate_centered_coordinate leafBox x hx i
  have hproduct : 0 < (1 + x 2 ^ 2) * (1 + x 5 ^ 2) :=
    mul_pos (by positivity) (by positivity)
  have hfactor : 0 < ((1 + x 2 ^ 2) * (1 + x 5 ^ 2)) ^ 2 := sq_pos_of_pos hproduct
  have hidentity := eval_polynomial_of_leaf_eq_cleared_majorant
    sideP sideW (fun i ↦ (leafBox i).lower) (fun i ↦ (leafBox i).upper)
    data y x hcoordinate hsideP hsideW (fun i ↦ (leaf_parameter_pos data hrho i).ne')
  rw [hidentity] at hpolynomial
  simpa only [WeightedMixedLeaf.quadraticMajorant] using
    nonpos_of_mul_nonpos_right hpolynomial hfactor

private theorem weighted_pair_score_le_leaf_quadratic_majorant
    (sideP sideW : ℚ) (data : WeightedMixedLeaf) (x : Fin 6 → ℝ)
    (hrho : ∀ i, 0 < data.rhoNumerator i)
    (hsideP : (sideP : ℝ) ^ 2 = 1) (hsideW : (sideW : ℝ) ^ 2 = 1)
    (hPFirst : x 0 ^ 2 + x 1 ^ 2 ≤ 1)
    (hPSecond : (x 0 - cStar) ^ 2 + x 1 ^ 2 ≤ 1)
    (hWFirst : x 3 ^ 2 + x 4 ^ 2 ≤ 1)
    (hWSecond : (x 3 - cStar) ^ 2 + x 4 ^ 2 ≤ 1) :
    weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
      (chordChartFirst sideP (x 0) (x 1) (x 2))
      (chordChartSecond sideP cStar (x 0) (x 1) (x 2))
      (chordChartFirst sideW (x 3) (x 4) (x 5))
      (chordChartSecond sideW cStar (x 3) (x 4) (x 5)) ≤
        data.quadraticMajorant sideP (x 2) (x 0) (x 1) sideW (x 5) (x 3) (x 4) := by
  simpa only [WeightedMixedLeaf.quadraticMajorant] using
    weightedPairScore_le_lensQuadraticCertificateMajorant
      sideP (x 2) (x 0) (x 1) sideW (x 5) (x 3) (x 4)
      (data.rho 0) (data.rho 1) (data.rho 2) (data.rho 3) (data.rho 4) (data.rho 5)
      (stereographicDirection 1 (data.supportSlope 0))
      (stereographicDirection 1 (data.supportSlope 1))
      (stereographicDirection 1 (data.supportSlope 2))
      (stereographicDirection 1 (data.supportSlope 3))
      (data.slack 0) (data.slack 1) (data.slack 2) (data.slack 3)
      hsideP hsideW hPFirst hPSecond hWFirst hWSecond
      (leaf_parameter_pos data hrho 0) (leaf_parameter_pos data hrho 1)
      (leaf_parameter_pos data hrho 2) (leaf_parameter_pos data hrho 3)
      (leaf_parameter_pos data hrho 4) (leaf_parameter_pos data hrho 5)
      (leaf_support_norm_le_one data 0) (leaf_support_norm_le_one data 1)
      (leaf_support_norm_le_one data 2) (leaf_support_norm_le_one data 3)
      (leaf_slack_nonneg data 0) (leaf_slack_nonneg data 1)
      (leaf_slack_nonneg data 2) (leaf_slack_nonneg data 3)

/-- A successful exact leaf check bounds the mixed score at every feasible point of its box. -/
theorem weighted_pair_score_nonpos_of_weighted_mixed_leaf_check
    (sideP sideW : ℚ) (leafBox : Fin 6 → RationalInterval)
    (data : WeightedMixedLeaf) (x : Fin 6 → ℝ)
    (hcheck : weightedMixedLeafCheck sideP sideW leafBox data = true)
    (hx : ∀ i, (leafBox i).Contains (x i))
    (hsideP : (sideP : ℝ) ^ 2 = 1) (hsideW : (sideW : ℝ) ^ 2 = 1)
    (hPFirst : x 0 ^ 2 + x 1 ^ 2 ≤ 1)
    (hPSecond : (x 0 - cStar) ^ 2 + x 1 ^ 2 ≤ 1)
    (hWFirst : x 3 ^ 2 + x 4 ^ 2 ≤ 1)
    (hWSecond : (x 3 - cStar) ^ 2 + x 4 ^ 2 ≤ 1) :
    weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
      (chordChartFirst sideP (x 0) (x 1) (x 2))
      (chordChartSecond sideP cStar (x 0) (x 1) (x 2))
      (chordChartFirst sideW (x 3) (x 4) (x 5))
      (chordChartSecond sideW cStar (x 3) (x 4) (x 5)) ≤ 0 := by
  rw [weightedMixedLeafCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hpolynomial :=
    MultivariateDensePolynomial.eval_nonpos_of_centeredBernstein_check_of_degree_bound
      degreeProfile _ (polynomial_of_leaf_degree_bound sideP sideW _ _ data) hcheck.2 _
      (fun i ↦ (leafBox i).abs_centered_coordinate_le_one (hx i))
  exact (weighted_pair_score_le_leaf_quadratic_majorant sideP sideW data x hcheck.1
    hsideP hsideW hPFirst hPSecond hWFirst hWSecond).trans
      (leaf_quadratic_majorant_nonpos sideP sideW leafBox data x hcheck.1 hx
        hpolynomial hsideP hsideW)

/-- A successful exact tree check proves the mixed score throughout every feasible point of its
root box. -/
theorem weighted_pair_score_nonpos_of_weighted_mixed_tree_check
    (sideP sideW : ℚ) (tree : WeightedMixedTree) (box : Fin 6 → RationalInterval)
    (x : Fin 6 → ℝ)
    (hcheck : weightedMixedTreeCheck sideP sideW 0 box tree = true)
    (hx : ∀ i, (box i).Contains (x i))
    (hsideP : (sideP : ℝ) ^ 2 = 1) (hsideW : (sideW : ℝ) ^ 2 = 1)
    (hPFirst : x 0 ^ 2 + x 1 ^ 2 ≤ 1)
    (hPSecond : (x 0 - cStar) ^ 2 + x 1 ^ 2 ≤ 1)
    (hWFirst : x 3 ^ 2 + x 4 ^ 2 ≤ 1)
    (hWSecond : (x 3 - cStar) ^ 2 + x 4 ^ 2 ≤ 1) :
    weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
      (chordChartFirst sideP (x 0) (x 1) (x 2))
      (chordChartSecond sideP cStar (x 0) (x 1) (x 2))
      (chordChartFirst sideW (x 3) (x 4) (x 5))
      (chordChartSecond sideW cStar (x 3) (x 4) (x 5)) ≤ 0 := by
  have hPSecondCertificate := second_disk_constraint_at_certificate_chord hPFirst hPSecond
  have hWSecondCertificate := second_disk_constraint_at_certificate_chord hWFirst hWSecond
  have hdisk : WeightedMixedDiskConstraints x := by
    refine ⟨hPFirst, ?_, hWFirst, ?_⟩
    · norm_num [certificateChord] at hPSecondCertificate ⊢
      exact hPSecondCertificate
    · norm_num [certificateChord] at hWSecondCertificate ⊢
      exact hWSecondCertificate
  obtain ⟨leafBox, data, hrho, hxLeaf, hpolynomial⟩ :=
    exists_certified_leaf_of_weighted_mixed_tree_check
      sideP sideW tree 0 box x hcheck hx hdisk
  exact (weighted_pair_score_le_leaf_quadratic_majorant sideP sideW data x hrho
    hsideP hsideW hPFirst hPSecond hWFirst hWSecond).trans
      (leaf_quadratic_majorant_nonpos sideP sideW leafBox data x hrho hxLeaf
        hpolynomial hsideP hsideW)

/-- A successful exact tree check proves the corresponding rational root-box bound. -/
theorem weightedMixedRootBoxBound_of_tree_check
    (capP capW : Bool) (sideP sideW : ℚ) (tree : WeightedMixedTree)
    (hcheck : weightedMixedTreeCheck sideP sideW 0
      (weightedMixedRootBox capP capW) tree = true) :
    WeightedMixedRootBoxBound capP capW sideP sideW := by
  intro x hsideP hsideW hx hPFirst hPSecond hWFirst hWSecond
  exact weighted_pair_score_nonpos_of_weighted_mixed_tree_check
    sideP sideW tree (weightedMixedRootBox capP capW) x hcheck hx hsideP hsideW
    hPFirst hPSecond hWFirst hWSecond

end Bescovitch
