/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfApproximation
public import Bescovitch.SixPoint.WeightedSelfCertificateData.Bin1933To2000.Formula
import Bescovitch.SixPoint.WeightedSelfCertificateData.Boxes
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases

/-!
# Approximation error for Q on `[1933/5000, 2/5]`
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

noncomputable section

open DyadicTrivariatePolynomial WeightedSelfApproximation Approximation
open scoped unitInterval

private def nominalAtom (i : Fin 18) : ℚ :=
  nominalNumerators i / 2 ^ 40

private def approxAtoms : Fin 18 → Approximation := fun i ↦
  around
    (weightedSelfCoefficientBox (weightedSelfKappaDBox 0) (weightedSelfKappaCBox 0) i)
    (nominalAtom i)

private def approxChart : WeightedSelfChart Approximation :=
  let lower := around (RationalInterval.singleton (1933 / 5000))
    (425071195298 / 2 ^ 40)
  let upper := around (RationalInterval.singleton (2 / 5))
    (439804651110 / 2 ^ 40)
  let x := same RationalInterval.unit
  let y := same RationalInterval.unit
  let z := same RationalInterval.unit
  let b := add lower (mul (add upper (neg lower)) y)
  let r := add (add (approxAtoms 0) (neg b))
    (mul (add (add (rational 1) (neg (approxAtoms 0))) b) x)
  let t := add (rational (-1)) (mul (rational 2) z)
  ⟨r, b, t⟩

private def approxFormula : Bescovitch.WeightedSelfFormula Approximation :=
  Bescovitch.weightedSelfFormula operations approxAtoms approxChart.r
    approxChart.b approxChart.t

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem q_error_lt : approxFormula.q.error < 7 / 10 ^ 11 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem q_exact_abs_bound :
    absBound approxFormula.q.exact ≤ 227 / 100 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem q_nominal_abs_bound :
    absBound approxFormula.q.nominal ≤ 227 / 100 := by
  with_unfolding_all rfl

set_option maxHeartbeats 5000000 in
private theorem approx_atoms_rel : ∀ i,
    (approxAtoms i).Rel
      (weightedSelfCoefficientInput ((2 / 5 : ℚ) : ℝ) i)
      ((nominalAtom i : ℚ) : ℝ) := by
  obtain ⟨hD, hC⟩ := weightedSelfKappaBoxes_certify (0 : Fin 7)
  have hinput := weightedSelfCoefficientInput_mem (2 / 5)
    (weightedSelfKappaDBox 0) (weightedSelfKappaCBox 0) (by
      simpa [weightedSelfBinUpper] using hD) (by
      simpa [weightedSelfBinUpper] using hC)
  intro i
  change (around
    (weightedSelfCoefficientBox (weightedSelfKappaDBox 0)
      (weightedSelfKappaCBox 0) i) (nominalAtom i)).Rel
    (weightedSelfCoefficientInput ((2 / 5 : ℚ) : ℝ) i)
    ((nominalAtom i : ℚ) : ℝ)
  exact around_rel (hinput i)

private theorem nominal_atom_eval (i : Fin 18) (x y z : ℝ) :
    (atoms i).eval x y z = (nominalAtom i : ℝ) := by
  fin_cases i <;>
    norm_num [atoms, nominalAtom, ScaledPolynomial.eval_dyadic]

private theorem approx_chart_rel (x y z : I) :
    (approxChart.r).Rel
        (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
        (chart.r.eval x y z) ∧
      (approxChart.b).Rel
        (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
        (chart.b.eval x y z) ∧
      (approxChart.t).Rel
        (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t
        (chart.t.eval x y z) := by
  have hlower :
      (around (RationalInterval.singleton (1933 / 5000))
        (425071195298 / 2 ^ 40)).Rel ((1933 / 5000 : ℚ) : ℝ)
          ((425071195298 / 2 ^ 40 : ℚ) : ℝ) :=
    around_rel (RationalInterval.singleton_contains (1933 / 5000))
  have hupper :
      (around (RationalInterval.singleton (2 / 5))
        (439804651110 / 2 ^ 40)).Rel ((2 / 5 : ℚ) : ℝ)
          ((439804651110 / 2 ^ 40 : ℚ) : ℝ) :=
    around_rel (RationalInterval.singleton_contains (2 / 5))
  have hx := unit_rel x
  have hy := unit_rel y
  have hz := unit_rel z
  have hb := add_rel hlower (mul_rel (add_rel hupper (neg_rel hlower)) hy)
  have hr := add_rel (add_rel (approx_atoms_rel 0) (neg_rel hb))
    (mul_rel (add_rel (add_rel (rational_rel 1)
      (neg_rel (approx_atoms_rel 0))) hb) hx)
  have ht := add_rel (rational_rel (-1)) (mul_rel (rational_rel 2) hz)
  simp only [approxChart, chart, weightedSelfRealChart, sub_eq_add_neg,
    ScaledPolynomial.eval_add_notation, ScaledPolynomial.eval_neg_notation,
    ScaledPolynomial.eval_mul_notation, ScaledPolynomial.eval_dyadic,
    ScaledPolynomial.eval_first, ScaledPolynomial.eval_second,
    ScaledPolynomial.eval_third]
  constructor
  · convert hr using 1
    all_goals norm_num [weightedSelfCoefficientInput, nominal_atom_eval]
  constructor
  · convert hb using 1 <;> norm_num
  · norm_num at ht ⊢
    exact ht

private theorem approx_formula_rel (x y z : I) :
    (approxFormula.p).Rel
        (weightedSelfRealFormula
          (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
          (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
          (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t (2 / 5)).p
        (formula.p.eval x y z) ∧
      (approxFormula.q).Rel
        (weightedSelfRealFormula
          (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
          (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
          (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t (2 / 5)).q
        (formula.q.eval x y z) ∧
      (approxFormula.radicand).Rel
        (weightedSelfRealFormula
          (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
          (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
          (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t (2 / 5)).radicand
        (formula.radicand.eval x y z) := by
  obtain ⟨hr, hb, ht⟩ := approx_chart_rel x y z
  have h := formula_rel_real approx_atoms_rel hr hb ht
  have hatom : (fun i ↦ ((nominalAtom i : ℚ) : ℝ)) =
      fun i ↦ (atoms i).eval x y z := by
    funext i
    exact (nominal_atom_eval i x y z).symm
  rw [hatom] at h
  let exactData := Bescovitch.weightedSelfFormula weightedSelfRealFormulaOperations
    (weightedSelfCoefficientInput ((2 / 5 : ℚ) : ℝ))
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
    (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t
  let nominalData := Bescovitch.weightedSelfFormula weightedSelfRealFormulaOperations
    (fun i ↦ (atoms i).eval x y z) (chart.r.eval x y z)
    (chart.b.eval x y z) (chart.t.eval x y z)
  change (approxFormula.p).Rel exactData.p nominalData.p ∧
    (approxFormula.q).Rel exactData.q nominalData.q ∧
    (approxFormula.radicand).Rel exactData.radicand nominalData.radicand at h
  have heval := WeightedSelfDyadicPolynomial.eval_formula atoms chart.r chart.b chart.t x y z
  change formula.p.eval x y z = nominalData.p ∧
    formula.q.eval x y z = nominalData.q ∧
    formula.radicand.eval x y z = nominalData.radicand at heval
  rw [← heval.1, ← heval.2.1, ← heval.2.2] at h
  dsimp only [exactData] at h
  have hupper : ((2 / 5 : ℚ) : ℝ) = (2 / 5 : ℝ) := by norm_num
  rw [hupper] at h
  simpa only [approxFormula, weightedSelfRealFormula] using h

/-- The exact and nominal `Q` values obey the stated error and magnitude bounds. -/
theorem q_error_and_magnitude_bounds (x y z : I) :
    let exactQ := (weightedSelfRealFormula
        (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).r
        (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).b
        (weightedSelfRealChart (1933 / 5000) (2 / 5) x y z).t (2 / 5)).q
    |exactQ - formula.q.eval x y z| < (7 / 10 ^ 11 : ℝ) ∧
      |exactQ| ≤ (227 / 100 : ℝ) ∧
      |formula.q.eval x y z| ≤ (227 / 100 : ℝ) := by
  have hq := (approx_formula_rel x y z).2.1
  have herror := hq.2.2
  have hstrict : (approxFormula.q.error : ℝ) < (7 / 10 ^ 11 : ℝ) := by
    have hconstant : ((7 / 10 ^ 11 : ℚ) : ℝ) = (7 / 10 ^ 11 : ℝ) := by
      norm_num
    rw [← hconstant]
    exact (Rat.cast_lt (K := ℝ)).2 q_error_lt
  have hqExact := abs_le_abs_bound hq.1
  have hqNominal := abs_le_abs_bound hq.2.1
  dsimp only
  refine ⟨herror.trans_lt hstrict, ?_, ?_⟩
  · calc
      _ ≤ ((absBound approxFormula.q.exact : ℚ) : ℝ) := hqExact
      _ ≤ ((227 / 100 : ℚ) : ℝ) :=
        (Rat.cast_le (K := ℝ)).2 q_exact_abs_bound
      _ = 227 / 100 := by norm_num
  · calc
      _ ≤ ((absBound approxFormula.q.nominal : ℚ) : ℝ) := hqNominal
      _ ≤ ((227 / 100 : ℚ) : ℝ) :=
        (Rat.cast_le (K := ℝ)).2 q_nominal_abs_bound
      _ = 227 / 100 := by norm_num

end

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch
