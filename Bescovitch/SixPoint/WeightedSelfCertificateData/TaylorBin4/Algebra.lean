/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebra for the weighted-self Taylor certificate
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

/-- A quadratic lower model with a positive completed-square remainder gives a quantitative
lower bound. -/
theorem lower_bound_of_quadratic_model
    {value centerValue centerSlope remainder lowerBound epsilon u : ℝ}
    (hvalue : value = centerValue + centerSlope * u + remainder * u ^ 2)
    (hlower : 0 < lowerBound)
    (hremainder : lowerBound ≤ remainder)
    (hbudget : 4 * lowerBound * epsilon ≤
      4 * lowerBound * centerValue - centerSlope ^ 2) :
    epsilon ≤ value := by
  have hu : 0 ≤ u ^ 2 := sq_nonneg u
  have hsquare : 0 ≤ (2 * lowerBound * u + centerSlope) ^ 2 := sq_nonneg _
  have hquadratic :
      epsilon ≤ centerValue + centerSlope * u + lowerBound * u ^ 2 := by
    nlinarith
  have herror : 0 ≤ (remainder - lowerBound) * u ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hremainder) hu
  rw [hvalue]
  nlinarith

/-- The Taylor remainder of a quartic around an arbitrary center. -/
theorem quartic_taylor_identity
    (d0 d1 d2 d3 d4 a z : ℝ) :
    d0 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4 =
      (d0 + d1 * a + d2 * a ^ 2 + d3 * a ^ 3 + d4 * a ^ 4) +
      (d1 + 2 * d2 * a + 3 * d3 * a ^ 2 + 4 * d4 * a ^ 3) * (z - a) +
      (d2 + d3 * (z + 2 * a) + d4 * (z ^ 2 + 2 * a * z + 3 * a ^ 2)) *
        (z - a) ^ 2 := by
  ring

/-- A coefficient-only lower bound for the varying Taylor remainder on the unit interval. -/
theorem quartic_remainder_lower_bound
    {d2 d3 d4 a z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hd4 : 0 ≤ d4) (hlinear : -(3 / 16 : ℝ) ≤ d3 + 2 * a * d4) :
    d2 + 2 * a * d3 + 3 * a ^ 2 * d4 - 3 / 16 ≤
      d2 + d3 * (z + 2 * a) + d4 * (z ^ 2 + 2 * a * z + 3 * a ^ 2) := by
  have hzsq : 0 ≤ z ^ 2 := sq_nonneg z
  nlinarith

/-- The hard-bin nominal margin absorbs the certified endpoint-box perturbation. -/
theorem nonnegative_of_close_to_hard_bin_nominal
    {exact nominal : ℝ} (hnominal : (1 / 2400 : ℝ) ≤ nominal)
    (hclose : |exact - nominal| < (1 / 2 ^ 24 : ℝ)) : 0 ≤ exact := by
  have hleft : -(1 / 2 ^ 24 : ℝ) < exact - nominal := (abs_lt.mp hclose).1
  norm_num at hleft hnominal ⊢
  linarith

/-- Evaluate the real weighted-self formula at `t = -1 + 2z`. -/
def realFormulaAtZ (atom : Fin 18 → ℝ) (r b z : ℝ) : WeightedSelfFormula ℝ :=
  weightedSelfFormula weightedSelfRealFormulaOperations atom r b (-1 + 2 * z)

/-- Interpolate the `P` component as a quadratic in `z`. -/
theorem real_formula_p_interpolation (atom : Fin 18 → ℝ) (r b z : ℝ) :
    let f0 := (realFormulaAtZ atom r b 0).p
    let fm := (realFormulaAtZ atom r b (1 / 2)).p
    let f1 := (realFormulaAtZ atom r b 1).p
    let c := 2 * (f0 + f1 - 2 * fm)
    let a := f0
    let slope := f1 - a - c
    (realFormulaAtZ atom r b z).p = a + slope * z + c * z ^ 2 := by
  simp only [realFormulaAtZ, weightedSelfFormula, weightedSelfRealFormulaOperations]
  ring

/-- Interpolate the `Q` component as an affine function of `z`. -/
theorem real_formula_q_interpolation (atom : Fin 18 → ℝ) (r b z : ℝ) :
    let f0 := (realFormulaAtZ atom r b 0).q
    let f1 := (realFormulaAtZ atom r b 1).q
    (realFormulaAtZ atom r b z).q = f0 + (f1 - f0) * z := by
  simp only [realFormulaAtZ, weightedSelfFormula, weightedSelfRealFormulaOperations]
  ring

/-- Express the radicand through its midpoint value and the endpoint factors. -/
theorem real_formula_radicand_interpolation (atom : Fin 18 → ℝ) (r b z : ℝ) :
    let fm := (realFormulaAtZ atom r b (1 / 2)).radicand
    (realFormulaAtZ atom r b z).radicand = 4 * fm * z * (1 - z) := by
  simp only [realFormulaAtZ, weightedSelfFormula, weightedSelfRealFormulaOperations]
  ring

end

end WeightedSelfTaylorBin4
end Bescovitch
