/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.RationalEndpointData
public import Bescovitch.SixPoint.WeightedSelf

/-!
# Exact certificate for the weighted self inequality

This module assembles the seven exact scalar radius-bin certificates. The first rational bin
starts just below the physical radius range; the isolation interval for `barC` supplies the
small restriction needed by the analytic theorem.
-/

@[expose] public section

namespace Bescovitch

/-- Bounds on the seven rational certificate bins imply the weighted self inequality. -/
theorem weightedSelf_nonpos_of_certificate_radius_bins
    (h₀ : WeightedSelfRadiusBinBound (1933 / 5000) (2 / 5))
    (h₁ : WeightedSelfRadiusBinBound (2 / 5) (1 / 2))
    (h₂ : WeightedSelfRadiusBinBound (1 / 2) (3 / 5))
    (h₃ : WeightedSelfRadiusBinBound (3 / 5) (7 / 10))
    (h₄ : WeightedSelfRadiusBinBound (7 / 10) (4 / 5))
    (h₅ : WeightedSelfRadiusBinBound (4 / 5) (9 / 10))
    (h₆ : WeightedSelfRadiusBinBound (9 / 10) 1)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e p₁ p₂ : E) (he : ‖e‖ = 1) (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1)
    (hsep : barC ≤ ‖p₁ - p₂‖) :
    weightedPairScore e barC endpointLambda endpointMu p₁ p₂ p₁ p₂ ≤ 0 := by
  have h₀' : WeightedSelfRadiusBinBound (barC - 1) (2 / 5) := by
    intro r b t hbLower hbUpper hrLower hrUpper htLower htUpper
    apply h₀
    · nlinarith [barC_mem_isolation_box.1]
    · exact hbUpper
    · exact hrLower
    · exact hrUpper
    · exact htLower
    · exact htUpper
  exact weightedSelf_nonpos_of_radius_bin_bounds h₀' h₁ h₂ h₃ h₄ h₅ h₆
    e p₁ p₂ he hp₁ hp₂ hsep

end Bescovitch
