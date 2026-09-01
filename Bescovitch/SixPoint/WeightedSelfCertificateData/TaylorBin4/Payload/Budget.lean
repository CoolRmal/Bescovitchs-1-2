/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.CenterValue
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.CenterSlope
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.LowerCurvature
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.BudgetRows00_07
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.BudgetRows08_15
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Payload.BudgetRows16_24

/-!
# Completed-square budget payload
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

/-- Exact power coefficients for the completed-square budget. -/
def budgetFactorPayload : IntBivariate :=
  budgetFactorRows00_07 ++ budgetFactorRows08_15 ++ budgetFactorRows16_24

/-- Stored center value with the common payload denominator. -/
def storedCenterValue : ScaledPolynomial :=
  ⟨584, IntBivariate.scaleInt ((2 : ℤ) ^ 24) centerValuePowerPayload⟩

/-- Stored center slope with the common payload denominator. -/
def storedCenterSlope : ScaledPolynomial :=
  ⟨579, IntBivariate.scaleInt ((2 : ℤ) ^ 63) centerSlopePowerPayload⟩

/-- Stored lower curvature with the common payload denominator. -/
def storedLowerCurvature : ScaledPolynomial :=
  ⟨574, IntBivariate.scaleInt ((2 : ℤ) ^ 98) lowerCurvaturePowerPayload⟩

/-- The completed-square budget assembled from its stored factors. -/
def storedBudget : ScaledPolynomial :=
  ScaledPolynomial.dyadic 40 0 *
    (ScaledPolynomial.dyadic 4 0 * storedLowerCurvature * storedCenterValue +
      -(storedCenterSlope ^ 2)) + -ScaledPolynomial.dyadic 1 0

end

end WeightedSelfTaylorBin4
end Bescovitch
