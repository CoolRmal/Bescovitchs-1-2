/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.EndpointWeights

/-!
# The sharp endpoint configuration

This file realizes the algebraic endpoint as two vectors in the unit disk and records the exact
distances at which the weighted inequality is sharp.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- The unit root direction used to display the endpoint configuration. -/
def endpointRootVector : (EuclideanSpace ℝ (Fin 2)) := !₂[1, 0]

/-- The unit-radius point in the endpoint configuration. -/
def endpointUnitVector (B : ℝ) : (EuclideanSpace ℝ (Fin 2)) :=
  !₂[endpointUnitAbscissa B, endpointUnitOrdinate B]

/-- The second point in the endpoint configuration. -/
def endpointOuterVector (c B : ℝ) : (EuclideanSpace ℝ (Fin 2)) :=
  !₂[endpointOuterAbscissa c B, endpointOuterOrdinate c B]

private theorem endpointUnitRadicand_pos {c B : ℝ} (h : IsEndpointPair c B) :
    0 < 1 - endpointUnitAbscissa B ^ 2 := by
  have hB_lower := h.second_mem_isolation_box.1
  have hB_upper := h.second_mem_isolation_box.2
  rw [endpointUnitAbscissa]
  have hB_pos : 0 < B := by norm_num at hB_lower ⊢; linarith
  have hB_one : 1 < B := by norm_num at hB_lower ⊢; linarith
  have hB_three : B < 3 := by norm_num at hB_upper ⊢; linarith
  have hB_sq_lower : 1 < B ^ 2 := by nlinarith
  have hB_sq_upper : B ^ 2 < 9 := by nlinarith
  rw [sub_pos]
  have habs : |(5 - B ^ 2) / 4| < (1 : ℝ) := by
    rw [abs_lt]
    exact ⟨by nlinarith, by nlinarith⟩
  have hsq := (sq_lt_sq.mpr (by simpa using habs) :
    ((5 - B ^ 2) / 4) ^ 2 < (1 : ℝ) ^ 2)
  norm_num at hsq ⊢
  exact hsq

private theorem endpointOuterRadicand_pos {c B : ℝ} (h : IsEndpointPair c B) :
    0 < endpointOuterRadius c B ^ 2 - endpointOuterAbscissa c B ^ 2 := by
  let b := endpointOuterRadius c B
  let x := endpointUnitAbscissa B
  let z := endpointOuterAbscissa c B
  let k := endpointChordAbscissa c B
  have hx : 0 < 1 - x ^ 2 := by
    simpa [x] using endpointUnitRadicand_pos h
  have hgram : (k - x * z) ^ 2 = (1 - x ^ 2) * (b ^ 2 - z ^ 2) := by
    simpa only [IsEndpointPair, endpointOuterRadius, endpointSecondDistance,
      endpointUnitAbscissa, endpointOuterAbscissa, endpointChordAbscissa, b, x, z, k]
      using h.2.2.2.2.2.1
  have hk : k - x * z < 0 := by
    simpa only [IsEndpointPair, endpointOuterRadius, endpointSecondDistance,
      endpointUnitAbscissa, endpointOuterAbscissa, endpointChordAbscissa, b, x, z, k]
      using h.2.2.2.2.2.2.2.2
  nlinarith [sq_pos_of_neg hk]

private theorem endpoint_inner_product_identity {c B : ℝ} (h : IsEndpointPair c B) :
    endpointUnitAbscissa B * endpointOuterAbscissa c B +
        endpointUnitOrdinate B * endpointOuterOrdinate c B =
      endpointChordAbscissa c B := by
  let b := endpointOuterRadius c B
  let x := endpointUnitAbscissa B
  let y := endpointUnitOrdinate B
  let z := endpointOuterAbscissa c B
  let w := endpointOuterOrdinate c B
  let k := endpointChordAbscissa c B
  have hx : 0 < 1 - x ^ 2 := by
    simpa [x] using endpointUnitRadicand_pos h
  have hb : 0 < b ^ 2 - z ^ 2 := by
    simpa [b, z] using endpointOuterRadicand_pos h
  have hy_sq : y ^ 2 = 1 - x ^ 2 := by
    simpa [y, endpointUnitOrdinate] using Real.sq_sqrt hx.le
  have hw_sq : w ^ 2 = b ^ 2 - z ^ 2 := by
    change (-Real.sqrt (b ^ 2 - z ^ 2)) ^ 2 = b ^ 2 - z ^ 2
    rw [neg_sq]
    exact Real.sq_sqrt hb.le
  have hy : 0 < y := by
    simpa [y, endpointUnitOrdinate] using Real.sqrt_pos.2 hx
  have hw : w < 0 := by
    simpa [w, endpointOuterOrdinate] using neg_lt_zero.mpr (Real.sqrt_pos.2 hb)
  have hgram : (k - x * z) ^ 2 = (1 - x ^ 2) * (b ^ 2 - z ^ 2) := by
    simpa only [IsEndpointPair, endpointOuterRadius, endpointSecondDistance,
      endpointUnitAbscissa, endpointOuterAbscissa, endpointChordAbscissa, b, x, z, k]
      using h.2.2.2.2.2.1
  have hk : k - x * z < 0 := by
    simpa only [IsEndpointPair, endpointOuterRadius, endpointSecondDistance,
      endpointUnitAbscissa, endpointOuterAbscissa, endpointChordAbscissa, b, x, z, k]
      using h.2.2.2.2.2.2.2.2
  have hsq : (k - x * z) ^ 2 = (y * w) ^ 2 := by
    calc
      (k - x * z) ^ 2 = (1 - x ^ 2) * (b ^ 2 - z ^ 2) := hgram
      _ = (y * w) ^ 2 := by rw [← hy_sq, ← hw_sq]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
  · change x * z + y * w = k
    linarith
  · exfalso
    have hyw : y * w < 0 := mul_neg_of_pos_of_neg hy hw
    linarith

/-- The displayed root direction has unit norm. -/
@[simp]
theorem norm_endpointRootVector : ‖endpointRootVector‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  simp [endpointRootVector, EuclideanSpace.real_norm_sq_eq]

/-- The first endpoint vector lies on the unit circle. -/
theorem norm_endpointUnitVector {c B : ℝ} (h : IsEndpointPair c B) :
    ‖endpointUnitVector B‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [EuclideanSpace.real_norm_sq_eq, endpointUnitVector, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hy := Real.sq_sqrt (endpointUnitRadicand_pos h).le
  change endpointUnitOrdinate B ^ 2 = 1 - endpointUnitAbscissa B ^ 2 at hy
  nlinarith

/-- The norm of the second endpoint vector is its prescribed outer radius. -/
theorem norm_endpointOuterVector {c B : ℝ} (h : IsEndpointPair c B) :
    ‖endpointOuterVector c B‖ = endpointOuterRadius c B := by
  have hb_lower := h.second_mem_isolation_box.1
  have hc_lower := h.c_mem_isolation_box.1
  have hc_upper := h.c_mem_isolation_box.2
  have hb_pos : 0 < endpointOuterRadius c B := by
    rw [endpointOuterRadius]
    have hc0 : 0 < c := by norm_num at hc_lower ⊢; linarith
    have hc1 : 0 < c + 1 := by linarith
    have hcsq : c ^ 2 < (13866128436518100 / 10 ^ 16 : ℝ) ^ 2 := by
      nlinarith
    apply div_pos
    · norm_num at hb_lower hc_lower hc_upper hcsq ⊢
      nlinarith
    · exact hc1
  rw [← sq_eq_sq₀ (norm_nonneg _) hb_pos.le]
  simp only [EuclideanSpace.real_norm_sq_eq, endpointOuterVector, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hw : endpointOuterOrdinate c B ^ 2 =
      endpointOuterRadius c B ^ 2 - endpointOuterAbscissa c B ^ 2 := by
    simpa [endpointOuterOrdinate] using Real.sq_sqrt (endpointOuterRadicand_pos h).le
  nlinarith

/-- The two displayed endpoint vectors have chord length `c`. -/
theorem norm_endpointUnitVector_sub_endpointOuterVector {c B : ℝ}
    (h : IsEndpointPair c B) :
    ‖endpointUnitVector B - endpointOuterVector c B‖ = c := by
  have hc : 0 < c := by
    have := h.c_mem_isolation_box.1
    norm_num at this ⊢
    linarith
  rw [← sq_eq_sq₀ (norm_nonneg _) hc.le]
  simp only [EuclideanSpace.real_norm_sq_eq, endpointUnitVector, endpointOuterVector,
    Fin.sum_univ_two, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hip := endpoint_inner_product_identity h
  have hu_sq : endpointUnitAbscissa B ^ 2 + endpointUnitOrdinate B ^ 2 = 1 := by
    have hy := Real.sq_sqrt (endpointUnitRadicand_pos h).le
    change endpointUnitOrdinate B ^ 2 = 1 - endpointUnitAbscissa B ^ 2 at hy
    linarith
  have hv_sq : endpointOuterAbscissa c B ^ 2 + endpointOuterOrdinate c B ^ 2 =
      endpointOuterRadius c B ^ 2 := by
    have hw : endpointOuterOrdinate c B ^ 2 =
        endpointOuterRadius c B ^ 2 - endpointOuterAbscissa c B ^ 2 := by
      simpa [endpointOuterOrdinate] using Real.sq_sqrt (endpointOuterRadicand_pos h).le
    linarith
  rw [endpointChordAbscissa] at hip
  nlinarith

/-- Doubling the unit endpoint vector produces the first endpoint distance. -/
theorem norm_endpointRootVector_sub_unit_sub_unit {c B : ℝ} (h : IsEndpointPair c B) :
    ‖endpointRootVector - endpointUnitVector B - endpointUnitVector B‖ = B := by
  have hB : 0 < B := by
    have := h.second_mem_isolation_box.1
    norm_num at this ⊢
    linarith
  rw [← sq_eq_sq₀ (norm_nonneg _) hB.le]
  simp only [EuclideanSpace.real_norm_sq_eq, endpointRootVector, endpointUnitVector,
    Fin.sum_univ_two, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hy := Real.sq_sqrt (endpointUnitRadicand_pos h).le
  change endpointUnitOrdinate B ^ 2 = 1 - endpointUnitAbscissa B ^ 2 at hy
  rw [endpointUnitAbscissa] at hy ⊢
  nlinarith

/-- Doubling the outer endpoint vector produces the second endpoint distance. -/
theorem norm_endpointRootVector_sub_outer_sub_outer {c B : ℝ} (h : IsEndpointPair c B) :
    ‖endpointRootVector - endpointOuterVector c B - endpointOuterVector c B‖ =
      endpointSecondDistance c B := by
  have hc_lower := h.c_mem_isolation_box.1
  have hc_upper := h.c_mem_isolation_box.2
  have hB_upper := h.second_mem_isolation_box.2
  have hc0 : 0 < c := by norm_num at hc_lower ⊢; linarith
  have hcsq : (13866128436518096 / 10 ^ 16 : ℝ) ^ 2 < c ^ 2 := by
    nlinarith
  have hD : 0 < endpointSecondDistance c B := by
    rw [endpointSecondDistance]
    norm_num at hc_lower hc_upper hB_upper hcsq ⊢
    nlinarith
  rw [← sq_eq_sq₀ (norm_nonneg _) hD.le]
  simp only [EuclideanSpace.real_norm_sq_eq, endpointRootVector, endpointOuterVector,
    Fin.sum_univ_two, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hw : endpointOuterOrdinate c B ^ 2 =
      endpointOuterRadius c B ^ 2 - endpointOuterAbscissa c B ^ 2 := by
    simpa [endpointOuterOrdinate] using Real.sq_sqrt (endpointOuterRadicand_pos h).le
  rw [endpointOuterAbscissa] at hw ⊢
  nlinarith

/-- The root-to-unit-vector distance is the first auxiliary endpoint distance. -/
theorem norm_endpointRootVector_sub_unit {c B : ℝ} (h : IsEndpointPair c B) :
    ‖endpointRootVector - endpointUnitVector B‖ = endpointFirstAuxiliaryDistance B := by
  have hA_nonneg : 0 ≤ endpointFirstAuxiliaryDistance B := by
    exact Real.sqrt_nonneg _
  rw [← sq_eq_sq₀ (norm_nonneg _) hA_nonneg]
  simp only [EuclideanSpace.real_norm_sq_eq, endpointRootVector, endpointUnitVector,
    Fin.sum_univ_two, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hy := Real.sq_sqrt (endpointUnitRadicand_pos h).le
  change endpointUnitOrdinate B ^ 2 = 1 - endpointUnitAbscissa B ^ 2 at hy
  have hA : endpointFirstAuxiliaryDistance B ^ 2 = (B ^ 2 - 1) / 2 := by
    simpa [endpointFirstAuxiliaryDistance] using Real.sq_sqrt h.radicands_pos.1.le
  rw [endpointUnitAbscissa] at hy ⊢
  nlinarith

/-- The distance from the root to the sum of both endpoint vectors is the mixed auxiliary
distance. -/
theorem norm_endpointRootVector_sub_unit_sub_outer {c B : ℝ} (h : IsEndpointPair c B) :
    ‖endpointRootVector - endpointUnitVector B - endpointOuterVector c B‖ =
      endpointMixedAuxiliaryDistance c B := by
  have hC_nonneg : 0 ≤ endpointMixedAuxiliaryDistance c B := Real.sqrt_nonneg _
  rw [← sq_eq_sq₀ (norm_nonneg _) hC_nonneg]
  simp only [EuclideanSpace.real_norm_sq_eq, endpointRootVector, endpointUnitVector,
    endpointOuterVector, Fin.sum_univ_two, PiLp.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have hu_sq : endpointUnitAbscissa B ^ 2 + endpointUnitOrdinate B ^ 2 = 1 := by
    have hy := Real.sq_sqrt (endpointUnitRadicand_pos h).le
    change endpointUnitOrdinate B ^ 2 = 1 - endpointUnitAbscissa B ^ 2 at hy
    linarith
  have hv_sq : endpointOuterAbscissa c B ^ 2 + endpointOuterOrdinate c B ^ 2 =
      endpointOuterRadius c B ^ 2 := by
    have hw : endpointOuterOrdinate c B ^ 2 =
        endpointOuterRadius c B ^ 2 - endpointOuterAbscissa c B ^ 2 := by
      simpa [endpointOuterOrdinate] using Real.sq_sqrt (endpointOuterRadicand_pos h).le
    linarith
  have hip := endpoint_inner_product_identity h
  have hC : endpointMixedAuxiliaryDistance c B ^ 2 =
      (B ^ 2 + endpointSecondDistance c B ^ 2) / 2 - c ^ 2 := by
    simpa [endpointMixedAuxiliaryDistance, endpointSecondDistance] using
      Real.sq_sqrt h.radicands_pos.2.le
  rw [endpointUnitAbscissa] at hu_sq
  rw [endpointOuterAbscissa] at hv_sq
  rw [endpointUnitAbscissa, endpointOuterAbscissa, endpointChordAbscissa] at hip
  rw [endpointUnitAbscissa, endpointOuterAbscissa]
  nlinarith

/-- The weighted self-pair inequality is an equality at every natural endpoint pair. -/
theorem weightedPairScore_endpoint_self_eq_zero {c B lambda mu : ℝ}
    (h : IsEndpointPair c B) :
    weightedPairScore endpointRootVector c lambda mu
      (endpointUnitVector B) (endpointOuterVector c B)
      (endpointUnitVector B) (endpointOuterVector c B) = 0 := by
  have hbalance :
      endpointFirstAuxiliaryDistance B + endpointMixedAuxiliaryDistance c B =
        3 * c * endpointOuterRadius c B + c ^ 2 - 1 := by
    simpa only [IsEndpointPair, endpointOuterRadius, endpointSecondDistance,
      endpointFirstAuxiliaryDistance, endpointMixedAuxiliaryDistance] using
      h.2.2.2.2.1
  simp only [weightedPairScore]
  rw [norm_endpointRootVector_sub_unit_sub_unit h,
    norm_endpointRootVector_sub_outer_sub_outer h,
    norm_endpointRootVector_sub_unit h,
    norm_endpointRootVector_sub_unit_sub_outer h,
    norm_endpointUnitVector h, norm_endpointOuterVector h]
  rw [weightedFirstPenalty, weightedSecondPenalty, weightedConstantTerm]
  have hc_ne : c + 1 ≠ 0 := by
    have hc := h.c_mem_isolation_box.1
    norm_num at hc ⊢
    linarith
  have hb :
      (c + 1) * endpointOuterRadius c B = 2 * B - 3 * c ^ 2 + 2 * c - 1 := by
    rw [endpointOuterRadius]
    field_simp [hc_ne]
  rw [endpointSecondDistance]
  linear_combination mu * hbalance - lambda / 2 * hb

/-- The certified endpoint realizes equality in the sharp weighted self-pair inequality. -/
theorem weightedPairScore_certified_endpoint_self_eq_zero :
    weightedPairScore endpointRootVector cStar endpointLambda endpointMu
      (endpointUnitVector certifiedEndpointPair.2)
      (endpointOuterVector cStar certifiedEndpointPair.2)
      (endpointUnitVector certifiedEndpointPair.2)
      (endpointOuterVector cStar certifiedEndpointPair.2) = 0 := by
  exact weightedPairScore_endpoint_self_eq_zero
    (cStar_eq_certifiedEndpointPair_fst.symm ▸ certifiedEndpointPair_isEndpointPair)

end Bescovitch
