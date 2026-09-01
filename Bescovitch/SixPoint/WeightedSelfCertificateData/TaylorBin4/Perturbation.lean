/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.Approximation
public import Bescovitch.SixPoint.WeightedSelfCertificateData.TaylorBin4.NegativeP
public import Bescovitch.SixPoint.WeightedSelfCertificateData.Boxes
import Mathlib.Data.Rat.Cast.Order

/-!
# Perturbation from dyadic data to the exact weighted-self formula
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfTaylorBin4

noncomputable section

open Approximation

private def around (I : RationalInterval) (q : ℚ) : Approximation :=
  ⟨I, RationalInterval.singleton q,
    absBound (I.add (RationalInterval.singleton q).neg)⟩

private def same (I : RationalInterval) : Approximation := ⟨I, I, 0⟩

private theorem around_rel {I : RationalInterval} {q : ℚ} {x : ℝ} (hx : I.Contains x) :
    (around I q).Rel x q := by
  refine ⟨hx, RationalInterval.singleton_contains q, ?_⟩
  have hq : (RationalInterval.singleton q).Contains (q : ℝ) :=
    RationalInterval.singleton_contains q
  have hdiff := RationalInterval.add_contains hx
    (RationalInterval.neg_contains hq)
  simpa only [around, Rat.cast_sub, sub_eq_add_neg] using abs_le_absBound hdiff

private theorem same_rel {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    (same I).Rel x x := by
  refine ⟨hx, hx, ?_⟩
  change |x - x| ≤ ((0 : ℚ) : ℝ)
  simp

private def bin4ApproxAtoms : Fin 18 → Approximation := fun i ↦
  around
    (weightedSelfCoefficientBox (weightedSelfKappaDBox 3) (weightedSelfKappaCBox 3) i)
    (bin4NominalAtoms i)

private def bin4ApproxChart : WeightedSelfChart Approximation :=
  let lower := around (RationalInterval.singleton (3 / 5)) (659706976666 / 2 ^ 40)
  let upper := around (RationalInterval.singleton (7 / 10)) (769658139443 / 2 ^ 40)
  let x := same RationalInterval.unit
  let y := same RationalInterval.unit
  let z := same RationalInterval.unit
  let b := add lower (mul (add upper (neg lower)) y)
  let r := add (add (bin4ApproxAtoms 0) (neg b))
    (mul (add (add (rational 1) (neg (bin4ApproxAtoms 0))) b) x)
  let t := add (rational (-1)) (mul (rational 2) z)
  ⟨r, b, t⟩

private def bin4ApproxFormula : WeightedSelfFormula Approximation :=
  weightedSelfFormula operations bin4ApproxAtoms bin4ApproxChart.r
    bin4ApproxChart.b bin4ApproxChart.t

private def bin4ApproxDiscriminant : Approximation :=
  add (mul bin4ApproxFormula.p bin4ApproxFormula.p)
    (neg (mul (mul bin4ApproxFormula.q bin4ApproxFormula.q)
      bin4ApproxFormula.radicand))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bin4_error_lt : bin4ApproxDiscriminant.error < 1 / 2 ^ 24 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bin4_p_error_lt : bin4ApproxFormula.p.error < 1 / 2 ^ 30 := by
  with_unfolding_all rfl

set_option maxHeartbeats 5000000 in
/-- The exact coefficient vector lies in the dyadic approximation datum. -/
private theorem bin4_approx_atoms_rel : ∀ i,
    (bin4ApproxAtoms i).Rel
      (weightedSelfCoefficientInput ((7 / 10 : ℚ) : ℝ) i)
      (bin4NominalAtoms i : ℝ) := by
  obtain ⟨hD, hC⟩ := weightedSelfKappaBoxes_certify (3 : Fin 7)
  have hinput := weightedSelfCoefficientInput_mem (7 / 10)
    (weightedSelfKappaDBox 3) (weightedSelfKappaCBox 3) (by
      simpa [weightedSelfBinUpper] using hD) (by
      simpa [weightedSelfBinUpper] using hC)
  intro i
  change (around
    (weightedSelfCoefficientBox (weightedSelfKappaDBox 3)
      (weightedSelfKappaCBox 3) i) (bin4NominalAtoms i)).Rel
    (weightedSelfCoefficientInput ((7 / 10 : ℚ) : ℝ) i)
    (bin4NominalAtoms i : ℝ)
  exact around_rel (hinput i)

open scoped unitInterval

private theorem unit_rel (u : I) : (same RationalInterval.unit).Rel u u := by
  apply same_rel
  simpa only [RationalInterval.unit, RationalInterval.Contains, Rat.cast_zero,
    Rat.cast_one, Set.mem_Icc] using u.property

private theorem bin4_approx_chart_rel (x y z : I) :
    (bin4ApproxChart.r).Rel
        (weightedSelfRealChart (3 / 5) (7 / 10) x y z).r
        (bin4NominalChart x y z).r ∧
      (bin4ApproxChart.b).Rel
        (weightedSelfRealChart (3 / 5) (7 / 10) x y z).b
        (bin4NominalChart x y z).b ∧
      (bin4ApproxChart.t).Rel
        (weightedSelfRealChart (3 / 5) (7 / 10) x y z).t
        (bin4NominalChart x y z).t := by
  have hlower :
      (around (RationalInterval.singleton (3 / 5))
        (659706976666 / 2 ^ 40)).Rel (((3 / 5 : ℚ) : ℝ))
          (((659706976666 / 2 ^ 40 : ℚ) : ℝ)) :=
    around_rel (RationalInterval.singleton_contains (3 / 5))
  have hupper :
      (around (RationalInterval.singleton (7 / 10))
        (769658139443 / 2 ^ 40)).Rel (((7 / 10 : ℚ) : ℝ))
          (((769658139443 / 2 ^ 40 : ℚ) : ℝ)) :=
    around_rel (RationalInterval.singleton_contains (7 / 10))
  have hlowerExact : (((3 / 5 : ℚ) : ℝ)) = (3 / 5 : ℝ) := by norm_num
  have hupperExact : (((7 / 10 : ℚ) : ℝ)) = (7 / 10 : ℝ) := by norm_num
  have hlowerNominal : (((659706976666 / 2 ^ 40 : ℚ) : ℝ)) =
      (659706976666 : ℝ) / 2 ^ 40 := by norm_num
  have hupperNominal : (((769658139443 / 2 ^ 40 : ℚ) : ℝ)) =
      (769658139443 : ℝ) / 2 ^ 40 := by norm_num
  rw [hlowerExact, hlowerNominal] at hlower
  rw [hupperExact, hupperNominal] at hupper
  have hx := unit_rel x
  have hy := unit_rel y
  have hz := unit_rel z
  have hb := add_rel hlower (mul_rel (add_rel hupper (neg_rel hlower)) hy)
  have hr := add_rel (add_rel (bin4_approx_atoms_rel 0) (neg_rel hb))
    (mul_rel (add_rel (add_rel (rational_rel 1)
      (neg_rel (bin4_approx_atoms_rel 0))) hb) hx)
  have ht := add_rel (rational_rel (-1)) (mul_rel (rational_rel 2) hz)
  simp only [bin4ApproxChart, bin4NominalChart, weightedSelfRealChart, sub_eq_add_neg]
  constructor
  · convert hr using 1 <;> norm_num [weightedSelfCoefficientInput]
  constructor
  · exact hb
  · norm_num at ht
    exact ht

private theorem bin4_approx_formula_rel (x y z : I) :
    (bin4ApproxFormula.p).Rel
        (weightedSelfRealFormula
          (weightedSelfRealChart (3 / 5) (7 / 10) x y z).r
          (weightedSelfRealChart (3 / 5) (7 / 10) x y z).b
          (weightedSelfRealChart (3 / 5) (7 / 10) x y z).t
          (7 / 10)).p
        (bin4NominalFormula x y z).p ∧
      (bin4ApproxFormula.q).Rel
        (weightedSelfRealFormula
          (weightedSelfRealChart (3 / 5) (7 / 10) x y z).r
          (weightedSelfRealChart (3 / 5) (7 / 10) x y z).b
          (weightedSelfRealChart (3 / 5) (7 / 10) x y z).t
          (7 / 10)).q
        (bin4NominalFormula x y z).q ∧
      (bin4ApproxFormula.radicand).Rel
        (weightedSelfRealFormula
          (weightedSelfRealChart (3 / 5) (7 / 10) x y z).r
          (weightedSelfRealChart (3 / 5) (7 / 10) x y z).b
          (weightedSelfRealChart (3 / 5) (7 / 10) x y z).t
          (7 / 10)).radicand
        (bin4NominalFormula x y z).radicand := by
  obtain ⟨hr, hb, ht⟩ := bin4_approx_chart_rel x y z
  have h := formula_rel_real bin4_approx_atoms_rel hr hb ht
  have hupperExact : (((7 / 10 : ℚ) : ℝ)) = (7 / 10 : ℝ) := by norm_num
  rw [hupperExact] at h
  simpa only [bin4ApproxFormula, weightedSelfRealFormula, bin4NominalFormula,
    bin4NominalChart, realFormulaAtZ] using h

private theorem bin4_discriminant_error (x y z : I) :
    |weightedSelfDiscriminant
        (weightedSelfRealChart (3 / 5) (7 / 10) x y z).r
        (weightedSelfRealChart (3 / 5) (7 / 10) x y z).b
        (weightedSelfRealChart (3 / 5) (7 / 10) x y z).t (7 / 10) -
      bin4NominalDiscriminant x y z| < (1 / 2 ^ 24 : ℝ) := by
  obtain ⟨hp, hq, hrad⟩ := bin4_approx_formula_rel x y z
  have h := discriminant_rel hp hq hrad
  have hrPos := weightedSelfRealChart_first_pos
    (lower := (3 / 5 : ℝ)) (upper := (7 / 10 : ℝ))
    (z := (z : ℝ)) (by norm_num) (by norm_num) x.property y.property
  have hformula := weightedSelfRealFormula_eq_weightedSelf
    (weightedSelfRealChart (3 / 5) (7 / 10) x y z).r
    (weightedSelfRealChart (3 / 5) (7 / 10) x y z).b
    (weightedSelfRealChart (3 / 5) (7 / 10) x y z).t (7 / 10) hrPos.ne'
  rw [hformula.1, hformula.2.1, hformula.2.2] at h
  have herror : |weightedSelfDiscriminant
        (weightedSelfRealChart (3 / 5) (7 / 10) x y z).r
        (weightedSelfRealChart (3 / 5) (7 / 10) x y z).b
        (weightedSelfRealChart (3 / 5) (7 / 10) x y z).t (7 / 10) -
      bin4NominalDiscriminant x y z| ≤ (bin4ApproxDiscriminant.error : ℝ) := by
    simpa only [bin4ApproxDiscriminant, Approximation.discriminant,
      bin4NominalDiscriminant, weightedSelfDiscriminant] using h.2.2
  have hstrict : (bin4ApproxDiscriminant.error : ℝ) < (1 / 2 ^ 24 : ℝ) := by
    have hconstant : (((1 / 2 ^ 24 : ℚ) : ℝ)) = (1 / 2 ^ 24 : ℝ) := by
      norm_num
    rw [← hconstant]
    exact (Rat.cast_lt (K := ℝ)).2 bin4_error_lt
  exact herror.trans_lt hstrict

/-- The exact hard-bin discriminant is nonnegative on the affine cube. -/
theorem bin4_exact_discriminant_nonnegative (x y z : I) :
    0 ≤ weightedSelfDiscriminant
      (weightedSelfRealChart (3 / 5) (7 / 10) x y z).r
      (weightedSelfRealChart (3 / 5) (7 / 10) x y z).b
      (weightedSelfRealChart (3 / 5) (7 / 10) x y z).t (7 / 10) :=
  nonnegative_of_close_to_hard_bin_nominal
    (bin4_nominal_discriminant_lower_bound x y z)
    (bin4_discriminant_error x y z)

/-- The exact polynomial `P` is nonpositive throughout the hard affine cube. -/
theorem bin4_exact_negative_p (x y z : I) :
    weightedSelfPolynomialP
      (weightedSelfRealChart (3 / 5) (7 / 10) x y z).r
      (weightedSelfRealChart (3 / 5) (7 / 10) x y z).b
      (weightedSelfRealChart (3 / 5) (7 / 10) x y z).t (7 / 10) ≤ 0 := by
  let exactP :=
    (weightedSelfRealFormula
      (weightedSelfRealChart (3 / 5) (7 / 10) x y z).r
      (weightedSelfRealChart (3 / 5) (7 / 10) x y z).b
      (weightedSelfRealChart (3 / 5) (7 / 10) x y z).t (7 / 10)).p
  let nominalP := (bin4NominalFormula x y z).p
  have hrel := (bin4_approx_formula_rel x y z).1
  have herror : |exactP - nominalP| ≤ (bin4ApproxFormula.p.error : ℝ) := by
    exact hrel.2.2
  have herrorStrict : (bin4ApproxFormula.p.error : ℝ) < (1 / 2 ^ 30 : ℝ) := by
    have hconstant : (((1 / 2 ^ 30 : ℚ) : ℝ)) = (1 / 2 ^ 30 : ℝ) := by
      norm_num
    rw [← hconstant]
    exact (Rat.cast_lt (K := ℝ)).2 bin4_p_error_lt
  have hnominal : nominalP ≤ -(29 / 100 : ℝ) := by
    dsimp only [nominalP]
    linarith [bin4_nominal_negative_p_lower_bound x y z]
  have hexact : exactP ≤ 0 := by
    have hupper := (le_abs_self (exactP - nominalP)).trans herror
    norm_num at herrorStrict
    linarith
  have hrPos := weightedSelfRealChart_first_pos
    (lower := (3 / 5 : ℝ)) (upper := (7 / 10 : ℝ))
    (z := (z : ℝ)) (by norm_num) (by norm_num) x.property y.property
  have hformula := weightedSelfRealFormula_eq_weightedSelf
    (weightedSelfRealChart (3 / 5) (7 / 10) x y z).r
    (weightedSelfRealChart (3 / 5) (7 / 10) x y z).b
    (weightedSelfRealChart (3 / 5) (7 / 10) x y z).t (7 / 10) hrPos.ne'
  dsimp only [exactP] at hexact
  rwa [hformula.1] at hexact

end

end WeightedSelfTaylorBin4
end Bescovitch
