/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateCore
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.NegativePError
import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.NominalSigns

/-!
# Exact sign of P on `[1933/5000, 2/5]`
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

noncomputable section

open DyadicTrivariatePolynomial
open scoped unitInterval

/-- The exact polynomial `P` is nonpositive throughout this affine cube. -/
theorem exact_negative_p (x y z : I) :
    weightedSelfPolynomialP
      (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
      (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
      (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t (2 / 5) ≤ 0 := by
  let exactP := (weightedSelfRealFormula
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t (2 / 5)).p
  let nominalP := formula.p.eval x y z
  have herror : |exactP - nominalP| < (7 / 10 ^ 10 : ℝ) := by
    simpa only [exactP, nominalP] using exact_p_error x y z
  have hnominal : nominalP ≤ -(9 / 100 : ℝ) := by
    dsimp only [nominalP]
    linarith [nominal_negative_p_lower x y z]
  have hexact : exactP ≤ 0 := by
    have hupper := (le_abs_self (exactP - nominalP)).trans_lt herror
    norm_num at hupper
    linarith
  have hrPos := weightedSelfRealChart_first_pos
    (lower := (1933 / 5000 : ℝ)) (upper := (2 / 5 : ℝ))
    (z := (z : ℝ)) (by norm_num) (by norm_num) x.property y.property
  have hformula := weightedSelfRealFormula_eq_weightedSelf
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t (2 / 5) hrPos.ne'
  dsimp only [exactP] at hexact
  rwa [hformula.1] at hexact

end

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
