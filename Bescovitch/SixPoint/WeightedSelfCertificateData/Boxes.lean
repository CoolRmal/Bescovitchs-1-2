/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateCore

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
  ⟨16557900989 / 10 ^ 12, 16557900990 / 10 ^ 12, by norm_num⟩,
  ⟨14960552474 / 10 ^ 12, 14960552475 / 10 ^ 12, by norm_num⟩,
  ⟨13583674326 / 10 ^ 12, 13583674327 / 10 ^ 12, by norm_num⟩,
  ⟨12388484118 / 10 ^ 12, 12388484119 / 10 ^ 12, by norm_num⟩,
  ⟨11344366656 / 10 ^ 12, 11344366657 / 10 ^ 12, by norm_num⟩,
  ⟨10426893730 / 10 ^ 12, 10426893731 / 10 ^ 12, by norm_num⟩,
  ⟨9616382194 / 10 ^ 12, 9616382195 / 10 ^ 12, by norm_num⟩]

/-- Enclosures for the mixed-distance curvature coefficient on the seven bins. -/
def weightedSelfKappaCBox : Fin 7 → RationalInterval := ![
  ⟨11202918890 / 10 ^ 12, 11202918891 / 10 ^ 12, by norm_num⟩,
  ⟨10718260066 / 10 ^ 12, 10718260067 / 10 ^ 12, by norm_num⟩,
  ⟨10264385030 / 10 ^ 12, 10264385031 / 10 ^ 12, by norm_num⟩,
  ⟨9838740893 / 10 ^ 12, 9838740894 / 10 ^ 12, by norm_num⟩,
  ⟨9439034017 / 10 ^ 12, 9439034018 / 10 ^ 12, by norm_num⟩,
  ⟨9063199057 / 10 ^ 12, 9063199058 / 10 ^ 12, by norm_num⟩,
  ⟨8709372221 / 10 ^ 12, 8709372222 / 10 ^ 12, by norm_num⟩]

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

end Bescovitch
