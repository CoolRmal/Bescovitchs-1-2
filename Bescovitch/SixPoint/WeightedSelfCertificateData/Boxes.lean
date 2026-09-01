/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfDirectInterval

/-!
# Rational boxes for the weighted-self bins

The two nonconstant curvature coefficients depend on the upper radius of each bin. These exact
rational intervals enclose their values throughout the isolated endpoint box.
-/

@[expose] public section

namespace Bescovitch

/-- Lower endpoints of the seven rational certificate bins. -/
def weightedSelfBinLower : Fin 7 → ℚ :=
  ![1933 / 5000, 2 / 5, 1 / 2, 3 / 5, 7 / 10, 4 / 5, 9 / 10]

/-- Upper endpoints of the seven rational certificate bins. -/
def weightedSelfBinUpper : Fin 7 → ℚ :=
  ![2 / 5, 1 / 2, 3 / 5, 7 / 10, 4 / 5, 9 / 10, 1]

/-- Enclosures for the second-distance curvature coefficient on the seven bins. -/
def weightedSelfKappaDBox : Fin 7 → RationalInterval := ![
  ⟨16529483415 / 10 ^ 12, 16529483418 / 10 ^ 12, by norm_num⟩,
  ⟨14935530200 / 10 ^ 12, 14935530203 / 10 ^ 12, by norm_num⟩,
  ⟨13561492695 / 10 ^ 12, 13561492698 / 10 ^ 12, by norm_num⟩,
  ⟨12368700498 / 10 ^ 12, 12368700501 / 10 ^ 12, by norm_num⟩,
  ⟨11326623936 / 10 ^ 12, 11326623939 / 10 ^ 12, by norm_num⟩,
  ⟨10410900917 / 10 ^ 12, 10410900920 / 10 ^ 12, by norm_num⟩,
  ⟨9601900006 / 10 ^ 12, 9601900009 / 10 ^ 12, by norm_num⟩]

/-- Enclosures for the mixed-distance curvature coefficient on the seven bins. -/
def weightedSelfKappaCBox : Fin 7 → RationalInterval := ![
  ⟨11195483647 / 10 ^ 12, 11195483650 / 10 ^ 12, by norm_num⟩,
  ⟨10711221288 / 10 ^ 12, 10711221291 / 10 ^ 12, by norm_num⟩,
  ⟨10257712887 / 10 ^ 12, 10257712890 / 10 ^ 12, by norm_num⟩,
  ⟨9832408404 / 10 ^ 12, 9832408407 / 10 ^ 12, by norm_num⟩,
  ⟨9433016726 / 10 ^ 12, 9433016729 / 10 ^ 12, by norm_num⟩,
  ⟨9057474748 / 10 ^ 12, 9057474751 / 10 ^ 12, by norm_num⟩,
  ⟨8703920674 / 10 ^ 12, 8703920677 / 10 ^ 12, by norm_num⟩]

private theorem coefficientExpression_ten (upper : ℚ) :
    weightedSelfCoefficientExpression upper 10 =
      RadicalExpression.div
        (RadicalExpression.div (.constant 1) (.mul (.constant 2) (.var 2)))
        (RadicalExpression.pow
          (.add (.add (.constant 1) (.constant (2 * upper))) (.var 2)) 2) := by
  simp [weightedSelfCoefficientExpression]

private theorem coefficientExpression_fourteen (upper : ℚ) :
    weightedSelfCoefficientExpression upper 14 =
      RadicalExpression.div
        (RadicalExpression.div (.var 6) (.mul (.constant 2) (.var 4)))
        (RadicalExpression.pow
          (.add (.add (.constant 2) (.constant upper)) (.var 4)) 2) := by
  simp [weightedSelfCoefficientExpression]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
/-- Each bin-dependent curvature expression is enclosed by its displayed rational box. -/
theorem weightedSelfKappaBoxes_certify (i : Fin 7) :
    (weightedSelfCoefficientExpression (weightedSelfBinUpper i) 10).certifiesWithin
        weightedSelfEndpointBox (weightedSelfKappaDBox i) = true ∧
      (weightedSelfCoefficientExpression (weightedSelfBinUpper i) 14).certifiesWithin
        weightedSelfEndpointBox (weightedSelfKappaCBox i) = true := by
  fin_cases i
  all_goals
    rw [coefficientExpression_ten, coefficientExpression_fourteen]
    norm_num [weightedSelfBinUpper, weightedSelfKappaDBox, weightedSelfKappaCBox,
      weightedSelfEndpointBox, RadicalExpression.certifiesWithin,
      RadicalExpression.enclosure, RadicalExpression.div, RadicalExpression.pow,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.mul,
      RationalInterval.inv]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
/-- Direct interval evaluation certifies `Q ≥ 0` on each complete parameter cube. -/
theorem weightedSelfDirectQCertificates (i : Fin 7) :
    weightedSelfDirectQCertifiesNonnegative
      (weightedSelfBinLower i) (weightedSelfBinUpper i)
      (weightedSelfCoefficientBox (weightedSelfKappaDBox i) (weightedSelfKappaCBox i))
      .unit .unit .unit = true := by
  fin_cases i <;> with_unfolding_all rfl

/-- The reduced linear coefficient `Q` is nonnegative on every certified radius bin. -/
theorem weightedSelfPolynomialQ_nonneg_on_certificate_bin
    (i : Fin 7) (x y z : Set.Icc (0 : ℝ) 1) :
    0 ≤ weightedSelfPolynomialQ
      (weightedSelfRealChart (weightedSelfBinLower i) (weightedSelfBinUpper i) x y z).r
      (weightedSelfRealChart (weightedSelfBinLower i) (weightedSelfBinUpper i) x y z).b
      (weightedSelfRealChart (weightedSelfBinLower i) (weightedSelfBinUpper i) x y z).t
      (weightedSelfBinUpper i) := by
  obtain ⟨hD, hC⟩ := weightedSelfKappaBoxes_certify i
  have hinput := weightedSelfCoefficientInput_mem
    (weightedSelfBinUpper i) (weightedSelfKappaDBox i) (weightedSelfKappaCBox i) hD hC
  have hunit (u : Set.Icc (0 : ℝ) 1) : RationalInterval.unit.Contains (u : ℝ) := by
    simpa only [RationalInterval.unit, RationalInterval.Contains, Rat.cast_zero,
      Rat.cast_one, Set.mem_Icc] using u.property
  apply weightedSelfPolynomialQ_nonneg_of_direct_interval_certificate
    (weightedSelfBinLower i) (weightedSelfBinUpper i)
    (weightedSelfCoefficientBox (weightedSelfKappaDBox i) (weightedSelfKappaCBox i))
    hinput (weightedSelfDirectQCertificates i) (hunit x) (hunit y) (hunit z)
  apply ne_of_gt
  apply weightedSelfRealChart_first_pos
  · fin_cases i <;> norm_num [weightedSelfBinLower, weightedSelfBinUpper]
  · fin_cases i <;> norm_num [weightedSelfBinUpper]
  · exact x.property
  · exact y.property

end Bescovitch
