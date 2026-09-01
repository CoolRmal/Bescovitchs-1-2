/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.EndpointPacking
public import Bescovitch.SixPoint.WeightedMixedEqualityPartition
public import Bescovitch.SixPoint.WeightedMixedRootAssembly
public import Bescovitch.SixPoint.WeightedSelfCertificate

/-!
# Assembly of the exact weighted certificate

The seven radial certificates prove the self inequality. Together with the nine strict mixed
root boxes, that self inequality closes the exceptional equality box and hence proves the
coordinate-free weighted geometric bound.
-/

@[expose] public section

namespace Bescovitch

/-- The self bins, strict mixed boxes, and equality complement imply the weighted bound. -/
theorem weightedGeometricBound_of_certificate_bounds
    (hself₀ : WeightedSelfRadiusBinBound (1933 / 5000) (2 / 5))
    (hself₁ : WeightedSelfRadiusBinBound (2 / 5) (1 / 2))
    (hself₂ : WeightedSelfRadiusBinBound (1 / 2) (3 / 5))
    (hself₃ : WeightedSelfRadiusBinBound (3 / 5) (7 / 10))
    (hself₄ : WeightedSelfRadiusBinBound (7 / 10) (4 / 5))
    (hself₅ : WeightedSelfRadiusBinBound (4 / 5) (9 / 10))
    (hself₆ : WeightedSelfRadiusBinBound (9 / 10) 1)
    (h00NegNeg : WeightedMixedRootBoxBound false false (-1) (-1))
    (h00PosNeg : WeightedMixedRootBoxBound false false 1 (-1))
    (h00PosPos : WeightedMixedRootBoxBound false false 1 1)
    (h01NegNeg : WeightedMixedRootBoxBound false true (-1) (-1))
    (h01PosNeg : WeightedMixedRootBoxBound false true 1 (-1))
    (h10PosNeg : WeightedMixedRootBoxBound true false 1 (-1))
    (h10PosPos : WeightedMixedRootBoxBound true false 1 1)
    (h11PosNeg : WeightedMixedRootBoxBound true true 1 (-1))
    (h11PosPos : WeightedMixedRootBoxBound true true 1 1)
    (hequality : WeightedMixedEqualityComplementBound) : WeightedGeometricBound := by
  apply weightedGeometricBound_of_lensChartBound
  apply weightedLensChartBound_of_canonical_mixed_root_box_bounds
  · exact h00NegNeg
  · exact h00PosNeg
  · exact h00PosPos
  · exact h01NegNeg
  · exact h01PosNeg
  · exact h10PosNeg
  · exact h10PosPos
  · apply weighted_mixed_equality_root_box_bound_of_cell_bounds
    · intro p₁ p₂ hp₁ hp₂ hsep
      exact weightedSelf_nonpos_of_certificate_radius_bins hself₀ hself₁ hself₂ hself₃
        hself₄ hself₅ hself₆ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) p₁ p₂
        (by
          have hsq : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 := by
            simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
          nlinarith [norm_nonneg (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))]) hp₁ hp₂ hsep
    · simpa only [WeightedMixedEqualityComplementBound] using hequality
  · exact h11PosNeg
  · exact h11PosPos

end Bescovitch
