/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.RationalEndpointData
public import Bescovitch.SixPoint.WeightedSelfCertificateData.Boxes

/-!
# Interval certificates for the nonexceptional weighted-self bins

Four of the seven radius bins carry no equality configuration, so a plain interval-Horner
certificate for `-P` and a Bernstein certificate for the discriminant already close them. The
sign of `Q` is supplied once and for all by the direct interval evaluation on the same bin.
-/

@[expose] public section

open scoped unitInterval

namespace Bescovitch

/-- The interval enclosure of `-P` on one of the seven rational radius bins. -/
def weightedSelfBinNegativePPolynomial (i : Fin 7) : IntervalTrivariate :=
  weightedSelfNegativePIntervalPolynomial (weightedSelfBinLower i) (weightedSelfBinUpper i)
    (weightedSelfCoefficientBox (weightedSelfKappaDBox i) (weightedSelfKappaCBox i))

/-- The interval enclosure of the discriminant on one of the seven rational radius bins. -/
def weightedSelfBinDiscriminantPolynomial (i : Fin 7) : IntervalTrivariate :=
  weightedSelfDiscriminantIntervalPolynomial (weightedSelfBinLower i) (weightedSelfBinUpper i)
    (weightedSelfCoefficientBox (weightedSelfKappaDBox i) (weightedSelfKappaCBox i))

/-- Interval-Horner and Bernstein trees certify the weighted-self estimate on one radius bin. -/
theorem weightedSelfRadiusBinBound_of_bin_trees (i : Fin 7)
    (negativePTree discriminantTree : TensorSubdivision)
    (hnegativeP : intervalPolynomialSubdivisionCertifiesNonnegative negativePTree
      (weightedSelfBinNegativePPolynomial i) .unit .unit .unit = true)
    (hdiscriminant : intervalTensorSubdivisionCertifiesNonnegative discriminantTree
      (weightedSelfBinDiscriminantPolynomial i).bernsteinCoefficients = true) :
    WeightedSelfRadiusBinBound (weightedSelfBinLower i) (weightedSelfBinUpper i) := by
  obtain ⟨hD, hC⟩ := weightedSelfKappaBoxes_certify i
  refine weightedSelfRadiusBinBound_of_horner_bernstein_and_q_sign
    (weightedSelfBinLower i) (weightedSelfBinUpper i) ?_ ?_
    (weightedSelfKappaDBox i) (weightedSelfKappaCBox i) hD hC
    negativePTree discriminantTree hnegativeP
    (weightedSelfPolynomialQ_nonneg_on_certificate_bin i) hdiscriminant
  · fin_cases i <;> norm_num [weightedSelfBinLower, weightedSelfBinUpper]
  · fin_cases i <;> norm_num [weightedSelfBinUpper]

end Bescovitch
