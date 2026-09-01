/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Algebra
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Certificate
import Mathlib.Data.Rat.Cast.Order

/-!
# The nominal quartic on the hard weighted-self bin
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

/-- The rational values represented by the bin-four dyadic coefficient data. -/
def bin4NominalAtoms : Fin 18 → ℚ := ![
  1524596944819 / 2 ^ 40,
  3159715121154 / 2 ^ 40,
  2247193809520 / 2 ^ 40,
  2094620947479 / 2 ^ 40,
  2278693482689 / 2 ^ 40,
  98380370149 / 2 ^ 40,
  1021268553918 / 2 ^ 40,
  208420083779 / 2 ^ 40,
  6041009426 / 2 ^ 40,
  268985659914 / 2 ^ 40,
  13621282339 / 2 ^ 40,
  268042924775 / 2 ^ 40,
  17577289049 / 2 ^ 40,
  246390455462 / 2 ^ 40,
  10817810015 / 2 ^ 40,
  413853097094 / 2 ^ 40,
  4365710208548 / 2 ^ 40,
  6131883299131 / 2 ^ 40]

open scoped unitInterval

/-- The dyadic midpoint data used for the hard ordinary bin. -/
def bin4NominalChart (x y z : ℝ) : WeightedSelfChart ℝ :=
  let lower := (659706976666 : ℝ) / 2 ^ 40
  let upper := (769658139443 : ℝ) / 2 ^ 40
  let b := lower + (upper - lower) * y
  let r := (bin4NominalAtoms 0 : ℝ) - b +
    (1 - (bin4NominalAtoms 0 : ℝ) + b) * x
  ⟨r, b, -1 + 2 * z⟩

/-- The reduced real formula at the dyadic midpoint data. -/
def bin4NominalFormula (x y z : ℝ) : WeightedSelfFormula ℝ :=
  let chart := bin4NominalChart x y z
  realFormulaAtZ (fun i ↦ (bin4NominalAtoms i : ℝ)) chart.r chart.b z

/-- The discriminant of the dyadic midpoint formula. -/
def bin4NominalDiscriminant (x y z : ℝ) : ℝ :=
  let data := bin4NominalFormula x y z
  data.p ^ 2 - data.q ^ 2 * data.radicand

private theorem bin4_atom_eval (i : Fin 18) (x y : ℝ) :
    ScaledPolynomial.eval (bin4Atoms i) x y = (bin4NominalAtoms i : ℝ) := by
  fin_cases i <;>
    norm_num [bin4Atoms, bin4NominalAtoms, ScaledPolynomial.eval_dyadic]

@[simp] private theorem eval_scaled_first (x y : ℝ) :
    ScaledPolynomial.eval ScaledPolynomial.first x y = x := by
  simp [ScaledPolynomial.eval, ScaledPolynomial.first, IntBivariate.first,
    IntBivariate.eval, IntPolynomial.eval]

@[simp] private theorem eval_scaled_second (x y : ℝ) :
    ScaledPolynomial.eval ScaledPolynomial.second x y = y := by
  simp [ScaledPolynomial.eval, ScaledPolynomial.second, IntBivariate.second,
    IntBivariate.eval, IntPolynomial.eval]

private theorem eval_bin4FormulaAt_eq_nominal (w : ScaledPolynomial) (x y : ℝ) :
    let z := ScaledPolynomial.eval w x y
    ScaledPolynomial.eval (bin4FormulaAt w).p x y =
        (bin4NominalFormula x y z).p ∧
      ScaledPolynomial.eval (bin4FormulaAt w).q x y =
        (bin4NominalFormula x y z).q ∧
      ScaledPolynomial.eval (bin4FormulaAt w).radicand x y =
        (bin4NominalFormula x y z).radicand := by
  have h := eval_bin4FormulaAt w x y
  simpa only [bin4NominalFormula, bin4NominalChart, realFormulaAtZ, bin4_atom_eval,
    ScaledPolynomial.eval_add_notation, ScaledPolynomial.eval_neg_notation,
    ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_dyadic,
    eval_scaled_first, eval_scaled_second, pow_zero, div_one, Int.cast_one,
    Int.cast_ofNat, Int.cast_neg, neg_one_mul, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, sub_eq_add_neg] using h

private theorem eval_bin4A (x y : ℝ) :
    ScaledPolynomial.eval bin4A x y = (bin4NominalFormula x y 0).p := by
  simpa [bin4A, ScaledPolynomial.eval_dyadic] using
    (eval_bin4FormulaAt_eq_nominal (ScaledPolynomial.dyadic 0 0) x y).1

private theorem eval_bin4Mid_p (x y : ℝ) :
    ScaledPolynomial.eval bin4Mid.p x y =
      (bin4NominalFormula x y (1 / 2)).p := by
  simpa [bin4Mid, ScaledPolynomial.eval_dyadic] using
    (eval_bin4FormulaAt_eq_nominal (ScaledPolynomial.dyadic 1 1) x y).1

private theorem eval_bin4AtOne_p (x y : ℝ) :
    ScaledPolynomial.eval bin4AtOne.p x y = (bin4NominalFormula x y 1).p := by
  simpa [bin4AtOne, ScaledPolynomial.eval_dyadic] using
    (eval_bin4FormulaAt_eq_nominal (ScaledPolynomial.dyadic 1 0) x y).1

private theorem eval_bin4U (x y : ℝ) :
    ScaledPolynomial.eval bin4U x y = (bin4NominalFormula x y 0).q := by
  simpa [bin4U, ScaledPolynomial.eval_dyadic] using
    (eval_bin4FormulaAt_eq_nominal (ScaledPolynomial.dyadic 0 0) x y).2.1

private theorem eval_bin4AtOne_q (x y : ℝ) :
    ScaledPolynomial.eval bin4AtOne.q x y = (bin4NominalFormula x y 1).q := by
  simpa [bin4AtOne, ScaledPolynomial.eval_dyadic] using
    (eval_bin4FormulaAt_eq_nominal (ScaledPolynomial.dyadic 1 0) x y).2.1

private theorem eval_bin4Mid_radicand (x y : ℝ) :
    ScaledPolynomial.eval bin4Mid.radicand x y =
      (bin4NominalFormula x y (1 / 2)).radicand := by
  simpa [bin4Mid, ScaledPolynomial.eval_dyadic] using
    (eval_bin4FormulaAt_eq_nominal (ScaledPolynomial.dyadic 1 1) x y).2.2

/-- The nominal `P` component is the quadratic with coefficients `A`, `B`, and `C`. -/
theorem bin4_nominal_p_eq (x y z : ℝ) :
    (bin4NominalFormula x y z).p =
      ScaledPolynomial.eval bin4A x y +
        ScaledPolynomial.eval bin4B x y * z +
        ScaledPolynomial.eval bin4C x y * z ^ 2 := by
  have h := real_formula_p_interpolation
    (fun i ↦ (bin4NominalAtoms i : ℝ))
    (bin4NominalChart x y z).r (bin4NominalChart x y z).b z
  dsimp only at h
  have hp : (bin4NominalFormula x y z).p =
      (bin4NominalFormula x y 0).p +
        ((bin4NominalFormula x y 1).p - (bin4NominalFormula x y 0).p -
          2 * ((bin4NominalFormula x y 0).p + (bin4NominalFormula x y 1).p -
            2 * (bin4NominalFormula x y (1 / 2)).p)) * z +
        2 * ((bin4NominalFormula x y 0).p + (bin4NominalFormula x y 1).p -
          2 * (bin4NominalFormula x y (1 / 2)).p) * z ^ 2 := by
    simpa only [bin4NominalFormula, bin4NominalChart] using h
  rw [hp]
  simp only [bin4B, bin4C, ScaledPolynomial.eval_add_notation,
    ScaledPolynomial.eval_neg_notation, ScaledPolynomial.eval_mul_notation,
    ScaledPolynomial.eval_dyadic]
  rw [eval_bin4A, eval_bin4Mid_p, eval_bin4AtOne_p]
  norm_num
  ring

private theorem bin4_nominal_q_eq (x y z : ℝ) :
    (bin4NominalFormula x y z).q =
      ScaledPolynomial.eval bin4U x y +
        ScaledPolynomial.eval bin4V x y * z := by
  have h := real_formula_q_interpolation
    (fun i ↦ (bin4NominalAtoms i : ℝ))
    (bin4NominalChart x y z).r (bin4NominalChart x y z).b z
  dsimp only at h
  have hq : (bin4NominalFormula x y z).q =
      (bin4NominalFormula x y 0).q +
        ((bin4NominalFormula x y 1).q - (bin4NominalFormula x y 0).q) * z := by
    simpa only [bin4NominalFormula, bin4NominalChart] using h
  rw [hq]
  simp only [bin4V, ScaledPolynomial.eval_add_notation,
    ScaledPolynomial.eval_neg_notation]
  rw [eval_bin4U, eval_bin4AtOne_q]
  ring

private theorem bin4_nominal_radicand_eq (x y z : ℝ) :
    (bin4NominalFormula x y z).radicand =
      ScaledPolynomial.eval bin4H x y * z * (1 - z) := by
  have h := real_formula_radicand_interpolation
    (fun i ↦ (bin4NominalAtoms i : ℝ))
    (bin4NominalChart x y z).r (bin4NominalChart x y z).b z
  dsimp only at h
  have hrad : (bin4NominalFormula x y z).radicand =
      4 * (bin4NominalFormula x y (1 / 2)).radicand * z * (1 - z) := by
    simpa only [bin4NominalFormula, bin4NominalChart] using h
  rw [hrad]
  simp only [bin4H, ScaledPolynomial.eval_mul_notation,
    ScaledPolynomial.eval_dyadic]
  rw [eval_bin4Mid_radicand]
  norm_num

private theorem bin4_nominal_discriminant_eq_quartic (x y z : ℝ) :
    bin4NominalDiscriminant x y z =
      ScaledPolynomial.eval bin4A x y ^ 2 +
        ScaledPolynomial.eval bin4D1 x y * z +
        ScaledPolynomial.eval bin4D2 x y * z ^ 2 +
        ScaledPolynomial.eval bin4D3 x y * z ^ 3 +
        ScaledPolynomial.eval bin4D4 x y * z ^ 4 := by
  rw [bin4NominalDiscriminant, bin4_nominal_p_eq, bin4_nominal_q_eq,
    bin4_nominal_radicand_eq]
  simp only [bin4D1, bin4D2, bin4D3, bin4D4,
    ScaledPolynomial.eval_add_notation, ScaledPolynomial.eval_neg_notation,
    ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_pow_notation,
    ScaledPolynomial.eval_dyadic]
  norm_num
  ring

private theorem bin4_curvature_bounds (x y : I) :
    0 ≤ ScaledPolynomial.eval bin4D4 x y ∧
      0 ≤ ScaledPolynomial.eval bin4LowerCurvature x y ∧
      ScaledPolynomial.eval bin4LowerCurvature x y ≤ 15 ∧
      -(3 / 16 : ℝ) ≤ ScaledPolynomial.eval bin4D3 x y +
        2 * (3 / 32 : ℝ) * ScaledPolynomial.eval bin4D4 x y := by
  have hd4 : 0 ≤ ScaledPolynomial.eval bin4D4 x y := by
    rw [d4_eval]
    exact div_nonneg (d4_power_nonnegative x y) (by positivity)
  have hlower : 0 ≤ ScaledPolynomial.eval bin4LowerCurvature x y := by
    rw [lower_curvature_eval]
    exact div_nonneg (lower_curvature_power_nonnegative x y) (by positivity)
  have hupperPayload : 0 ≤ ScaledPolynomial.eval bin4UpperCurvature x y := by
    rw [upper_curvature_eval]
    exact div_nonneg (upper_curvature_power_nonnegative x y) (by positivity)
  have hlowerUpper : ScaledPolynomial.eval bin4LowerCurvature x y ≤ 15 := by
    have heq : ScaledPolynomial.eval bin4UpperCurvature x y =
        15 - ScaledPolynomial.eval bin4LowerCurvature x y := by
      simp only [bin4UpperCurvature, ScaledPolynomial.eval_add_notation,
        ScaledPolynomial.eval_neg_notation, ScaledPolynomial.eval_dyadic]
      norm_num
      ring
    linarith
  have hlinearPayload : 0 ≤ ScaledPolynomial.eval bin4RemainderLinearSlack x y := by
    rw [remainder_linear_slack_eval]
    exact div_nonneg (remainder_linear_slack_power_nonnegative x y) (by positivity)
  have hlinear : -(3 / 16 : ℝ) ≤ ScaledPolynomial.eval bin4D3 x y +
      2 * (3 / 32 : ℝ) * ScaledPolynomial.eval bin4D4 x y := by
    have heq : ScaledPolynomial.eval bin4RemainderLinearSlack x y =
        ScaledPolynomial.eval bin4D3 x y +
          2 * (3 / 32 : ℝ) * ScaledPolynomial.eval bin4D4 x y + 3 / 16 := by
      simp only [bin4RemainderLinearSlack, ScaledPolynomial.eval_add_notation,
        ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_dyadic]
      norm_num
    rw [heq] at hlinearPayload
    linarith
  exact ⟨hd4, hlower, hlowerUpper, hlinear⟩

private theorem bin4_taylor_remainder_lower_bound (x y z : I) :
    ScaledPolynomial.eval bin4LowerCurvature x y ≤
      ScaledPolynomial.eval bin4D2 x y +
        ScaledPolynomial.eval bin4D3 x y * ((z : ℝ) + 2 * (3 / 32 : ℝ)) +
        ScaledPolynomial.eval bin4D4 x y *
          ((z : ℝ) ^ 2 + 2 * (3 / 32 : ℝ) * z + 3 * (3 / 32 : ℝ) ^ 2) := by
  obtain ⟨hd4, _, _, hlinear⟩ := bin4_curvature_bounds x y
  have hcurvatureFormula : ScaledPolynomial.eval bin4LowerCurvature x y =
      ScaledPolynomial.eval bin4D2 x y +
        2 * (3 / 32 : ℝ) * ScaledPolynomial.eval bin4D3 x y +
        3 * (3 / 32 : ℝ) ^ 2 * ScaledPolynomial.eval bin4D4 x y - 3 / 16 := by
    simp only [bin4LowerCurvature, bin4Center,
      ScaledPolynomial.eval_add_notation, ScaledPolynomial.eval_neg_notation,
      ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_pow_notation,
      ScaledPolynomial.eval_dyadic]
    norm_num
    ring
  rw [hcurvatureFormula]
  exact quartic_remainder_lower_bound z.property.1 z.property.2 hd4 hlinear

private theorem bin4_center_identities (x y : I) :
    ScaledPolynomial.eval bin4CenterValue x y =
        ScaledPolynomial.eval bin4A x y ^ 2 +
          ScaledPolynomial.eval bin4D1 x y * (3 / 32 : ℝ) +
          ScaledPolynomial.eval bin4D2 x y * (3 / 32 : ℝ) ^ 2 +
          ScaledPolynomial.eval bin4D3 x y * (3 / 32 : ℝ) ^ 3 +
          ScaledPolynomial.eval bin4D4 x y * (3 / 32 : ℝ) ^ 4 ∧
      ScaledPolynomial.eval bin4CenterSlope x y =
        ScaledPolynomial.eval bin4D1 x y +
          2 * ScaledPolynomial.eval bin4D2 x y * (3 / 32 : ℝ) +
          3 * ScaledPolynomial.eval bin4D3 x y * (3 / 32 : ℝ) ^ 2 +
          4 * ScaledPolynomial.eval bin4D4 x y * (3 / 32 : ℝ) ^ 3 := by
  constructor
  · simp only [bin4CenterValue, bin4Center,
      ScaledPolynomial.eval_add_notation, ScaledPolynomial.eval_mul_notation,
      ScaledPolynomial.eval_pow_notation, ScaledPolynomial.eval_dyadic]
    norm_num
  · simp only [bin4CenterSlope, bin4Center,
      ScaledPolynomial.eval_add_notation, ScaledPolynomial.eval_mul_notation,
      ScaledPolynomial.eval_pow_notation, ScaledPolynomial.eval_dyadic]
    norm_num

private theorem bin4_completed_square_budget (x y : I)
    (hlower : 0 ≤ ScaledPolynomial.eval bin4LowerCurvature x y)
    (hlowerUpper : ScaledPolynomial.eval bin4LowerCurvature x y ≤ 15) :
    0 < ScaledPolynomial.eval bin4LowerCurvature x y ∧
      4 * ScaledPolynomial.eval bin4LowerCurvature x y * (1 / 2400 : ℝ) ≤
        4 * ScaledPolynomial.eval bin4LowerCurvature x y *
          ScaledPolynomial.eval bin4CenterValue x y -
          ScaledPolynomial.eval bin4CenterSlope x y ^ 2 := by
  have hstoredBudget : 0 ≤ ScaledPolynomial.eval storedBudget x y := by
    rw [budget_eval]
    exact div_nonneg (budget_power_nonnegative x y) (by positivity)
  have hbudgetPolynomial : 0 ≤ ScaledPolynomial.eval bin4Budget x y := by
    rwa [stored_budget_eval_eq_bin4_budget] at hstoredBudget
  have hbudget : 0 ≤
      40 * (4 * ScaledPolynomial.eval bin4LowerCurvature x y *
        ScaledPolynomial.eval bin4CenterValue x y -
        ScaledPolynomial.eval bin4CenterSlope x y ^ 2) - 1 := by
    have heq : ScaledPolynomial.eval bin4Budget x y =
        40 * (4 * ScaledPolynomial.eval bin4LowerCurvature x y *
          ScaledPolynomial.eval bin4CenterValue x y -
          ScaledPolynomial.eval bin4CenterSlope x y ^ 2) - 1 := by
      simp only [bin4Budget, ScaledPolynomial.eval_add_notation,
        ScaledPolynomial.eval_neg_notation, ScaledPolynomial.eval_mul_notation,
        ScaledPolynomial.eval_pow_notation, ScaledPolynomial.eval_dyadic]
      norm_num
      ring
    rwa [heq] at hbudgetPolynomial
  have hlowerPositive : 0 < ScaledPolynomial.eval bin4LowerCurvature x y := by
    have hne : ScaledPolynomial.eval bin4LowerCurvature x y ≠ 0 := by
      intro hzero
      rw [hzero] at hbudget
      nlinarith [sq_nonneg (ScaledPolynomial.eval bin4CenterSlope x y)]
    exact lt_of_le_of_ne hlower (Ne.symm hne)
  have hcompletedSquare :
      4 * ScaledPolynomial.eval bin4LowerCurvature x y * (1 / 2400 : ℝ) ≤
        4 * ScaledPolynomial.eval bin4LowerCurvature x y *
          ScaledPolynomial.eval bin4CenterValue x y -
          ScaledPolynomial.eval bin4CenterSlope x y ^ 2 := by
    nlinarith [hlowerUpper]
  exact ⟨hlowerPositive, hcompletedSquare⟩

/-- The dyadic midpoint discriminant has a uniform positive margin on the unit cube. -/
theorem bin4_nominal_discriminant_lower_bound (x y z : I) :
    (1 / 2400 : ℝ) ≤ bin4NominalDiscriminant x y z := by
  let d0 := ScaledPolynomial.eval bin4A x y ^ 2
  let d1 := ScaledPolynomial.eval bin4D1 x y
  let d2 := ScaledPolynomial.eval bin4D2 x y
  let d3 := ScaledPolynomial.eval bin4D3 x y
  let d4 := ScaledPolynomial.eval bin4D4 x y
  let a : ℝ := 3 / 32
  let centerValue := ScaledPolynomial.eval bin4CenterValue x y
  let centerSlope := ScaledPolynomial.eval bin4CenterSlope x y
  let lowerCurvature := ScaledPolynomial.eval bin4LowerCurvature x y
  let remainder := d2 + d3 * ((z : ℝ) + 2 * a) +
    d4 * ((z : ℝ) ^ 2 + 2 * a * z + 3 * a ^ 2)
  have hbounds := bin4_curvature_bounds x y
  change 0 ≤ d4 ∧ 0 ≤ lowerCurvature ∧ lowerCurvature ≤ 15 ∧
    -(3 / 16 : ℝ) ≤ d3 + 2 * a * d4 at hbounds
  obtain ⟨_, hlower, hlowerUpper, _⟩ := hbounds
  have hremainder := bin4_taylor_remainder_lower_bound x y z
  change lowerCurvature ≤ remainder at hremainder
  have hcenters := bin4_center_identities x y
  change centerValue = d0 + d1 * a + d2 * a ^ 2 + d3 * a ^ 3 + d4 * a ^ 4 ∧
    centerSlope = d1 + 2 * d2 * a + 3 * d3 * a ^ 2 + 4 * d4 * a ^ 3 at hcenters
  obtain ⟨hcenterValue, hcenterSlope⟩ := hcenters
  have hcompleted := bin4_completed_square_budget x y hlower hlowerUpper
  change 0 < lowerCurvature ∧
    4 * lowerCurvature * (1 / 2400 : ℝ) ≤
      4 * lowerCurvature * centerValue - centerSlope ^ 2 at hcompleted
  obtain ⟨hlowerPositive, hcompletedSquare⟩ := hcompleted
  have hquartic := bin4_nominal_discriminant_eq_quartic x y z
  have hvalue : bin4NominalDiscriminant x y z =
      centerValue + centerSlope * ((z : ℝ) - a) +
        remainder * ((z : ℝ) - a) ^ 2 := by
    rw [hquartic]
    rw [hcenterValue, hcenterSlope]
    exact quartic_taylor_identity d0 d1 d2 d3 d4 a z
  exact lower_bound_of_quadratic_model hvalue hlowerPositive hremainder hcompletedSquare

end

end WeightedSelfTaylorBin4
end Bescovitch
