/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfDirectInterval
import Mathlib.Data.Rat.Cast.Order

/-!
# Exact perturbation arithmetic for weighted-self formulas
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfApproximation

noncomputable section

/-- An exact interval, a nominal interval, and a uniform error between represented values. -/
structure Approximation where
  exact : RationalInterval
  nominal : RationalInterval
  error : ℚ

namespace Approximation

/-- The largest absolute value allowed by a rational interval. -/
def absBound (I : RationalInterval) : ℚ := max (-I.lower) I.upper

/-- Semantic interpretation of an approximation datum. -/
def Rel (a : Approximation) (x y : ℝ) : Prop :=
  a.exact.Contains x ∧ a.nominal.Contains y ∧ |x - y| ≤ a.error

/-- Membership in an interval bounds the absolute value by `absBound`. -/
theorem abs_le_abs_bound {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    |x| ≤ (absBound I : ℝ) := by
  rw [abs_le]
  have hlq : -(absBound I) ≤ I.lower := by
    exact neg_le.mp (le_max_left (-I.lower) I.upper)
  have huq : I.upper ≤ absBound I := le_max_right _ _
  have hlr : (-(absBound I) : ℝ) ≤ (I.lower : ℝ) := by exact_mod_cast hlq
  have hur : (I.upper : ℝ) ≤ (absBound I : ℝ) := by exact_mod_cast huq
  norm_num only [RationalInterval.Contains] at hx
  constructor
  · exact hlr.trans hx.1
  · exact hx.2.trans hur

/-- Approximate an exact interval by a nominal rational value. -/
def around (I : RationalInterval) (q : ℚ) : Approximation :=
  ⟨I, RationalInterval.singleton q,
    absBound (I.add (RationalInterval.singleton q).neg)⟩

/-- Regard one interval as both the exact and nominal enclosure. -/
def same (I : RationalInterval) : Approximation := ⟨I, I, 0⟩

/-- An interval member is related to a nominal rational surrounded by that interval. -/
theorem around_rel {I : RationalInterval} {q : ℚ} {x : ℝ} (hx : I.Contains x) :
    (around I q).Rel x q := by
  refine ⟨hx, RationalInterval.singleton_contains q, ?_⟩
  have hq : (RationalInterval.singleton q).Contains (q : ℝ) :=
    RationalInterval.singleton_contains q
  have hdiff := RationalInterval.add_contains hx (RationalInterval.neg_contains hq)
  simpa only [around, Rat.cast_sub, sub_eq_add_neg] using abs_le_abs_bound hdiff

/-- An interval member is related to itself with zero error. -/
theorem same_rel {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    (same I).Rel x x := by
  refine ⟨hx, hx, ?_⟩
  change |x - x| ≤ ((0 : ℚ) : ℝ)
  simp

open scoped unitInterval

/-- Every unit-interval value is related to itself by the unit interval. -/
theorem unit_rel (u : I) : (same RationalInterval.unit).Rel u u := by
  apply same_rel
  simpa only [RationalInterval.unit, RationalInterval.Contains, Rat.cast_zero,
    Rat.cast_one, Set.mem_Icc] using u.property

/-- The exact approximation of a rational constant. -/
def rational (q : ℚ) : Approximation :=
  ⟨RationalInterval.singleton q, RationalInterval.singleton q, 0⟩

/-- Add approximation data and their error bounds. -/
def add (a b : Approximation) : Approximation :=
  ⟨a.exact.add b.exact, a.nominal.add b.nominal, a.error + b.error⟩

/-- Negate approximation data without changing its error bound. -/
def neg (a : Approximation) : Approximation :=
  ⟨a.exact.neg, a.nominal.neg, a.error⟩

/-- Multiply approximation data using the standard product-error bound. -/
def mul (a b : Approximation) : Approximation :=
  ⟨a.exact.mul b.exact, a.nominal.mul b.nominal,
    absBound a.exact * b.error + absBound b.nominal * a.error⟩

/-- Raise approximation data to a natural power by repeated multiplication. -/
def pow (a : Approximation) : ℕ → Approximation
  | 0 => rational 1
  | n + 1 => mul (pow a n) a

/-- A rational constant represents itself exactly. -/
theorem rational_rel (q : ℚ) : (rational q).Rel q q := by
  norm_num [Rel, rational, RationalInterval.singleton_contains]

/-- Addition preserves the approximation relation. -/
theorem add_rel {a b : Approximation} {x x' y y' : ℝ}
    (ha : a.Rel x x') (hb : b.Rel y y') : (add a b).Rel (x + y) (x' + y') := by
  refine ⟨RationalInterval.add_contains ha.1 hb.1,
    RationalInterval.add_contains ha.2.1 hb.2.1, ?_⟩
  dsimp only [add]
  norm_num only [Rat.cast_add]
  calc
    |x + y - (x' + y')| = |(x - x') + (y - y')| := by
      congr 1
      all_goals ring
    _ ≤ |x - x'| + |y - y'| := abs_add_le _ _
    _ ≤ (a.error : ℝ) + b.error := add_le_add ha.2.2 hb.2.2

/-- Negation preserves the approximation relation. -/
theorem neg_rel {a : Approximation} {x x' : ℝ} (ha : a.Rel x x') :
    (neg a).Rel (-x) (-x') := by
  refine ⟨RationalInterval.neg_contains ha.1,
    RationalInterval.neg_contains ha.2.1, ?_⟩
  rw [show -x - -x' = -(x - x') by ring, abs_neg]
  exact ha.2.2

/-- Multiplication preserves the approximation relation with the recorded error. -/
theorem mul_rel {a b : Approximation} {x x' y y' : ℝ}
    (ha : a.Rel x x') (hb : b.Rel y y') : (mul a b).Rel (x * y) (x' * y') := by
  refine ⟨RationalInterval.mul_contains ha.1 hb.1,
    RationalInterval.mul_contains ha.2.1 hb.2.1, ?_⟩
  have hax := abs_le_abs_bound ha.1
  have hby := abs_le_abs_bound hb.2.1
  have hea : 0 ≤ (a.error : ℝ) := (abs_nonneg (x - x')).trans ha.2.2
  have heb : 0 ≤ (b.error : ℝ) := (abs_nonneg (y - y')).trans hb.2.2
  have habsA : 0 ≤ (absBound a.exact : ℝ) := (abs_nonneg x).trans hax
  have habsB : 0 ≤ (absBound b.nominal : ℝ) := (abs_nonneg y').trans hby
  have hfirst : |x| * |y - y'| ≤
      (absBound a.exact : ℝ) * b.error :=
    mul_le_mul hax hb.2.2 (abs_nonneg _) habsA
  have hsecond : |y'| * |x - x'| ≤
      (absBound b.nominal : ℝ) * a.error :=
    mul_le_mul hby ha.2.2 (abs_nonneg _) habsB
  dsimp only [mul]
  norm_num only [Rat.cast_add, Rat.cast_mul]
  calc
    |x * y - x' * y'| = |x * (y - y') + y' * (x - x')| := by
      congr 1
      all_goals ring
    _ ≤ |x * (y - y')| + |y' * (x - x')| := abs_add_le _ _
    _ = |x| * |y - y'| + |y'| * |x - x'| := by rw [abs_mul, abs_mul]
    _ ≤ (absBound a.exact : ℝ) * b.error +
        (absBound b.nominal : ℝ) * a.error := add_le_add hfirst hsecond

/-- Natural powers preserve the approximation relation. -/
theorem pow_rel {a : Approximation} {x x' : ℝ} (ha : a.Rel x x') :
    ∀ n, (pow a n).Rel (x ^ n) (x' ^ n)
  | 0 => by simpa [pow] using rational_rel 1
  | n + 1 => by
      simpa only [pow, pow_succ] using mul_rel (pow_rel ha n) ha

/-- Propagate approximation data through `p² - q²r`. -/
def discriminant (p q r : Approximation) : Approximation :=
  add (mul p p) (neg (mul (mul q q) r))

/-- The same compact recurrence controls the derived discriminant. -/
theorem discriminant_rel {p q r : Approximation}
    {exactP exactQ exactR nominalP nominalQ nominalR : ℝ}
    (hp : p.Rel exactP nominalP) (hq : q.Rel exactQ nominalQ)
    (hr : r.Rel exactR nominalR) :
    (discriminant p q r).Rel
      (exactP ^ 2 - exactQ ^ 2 * exactR)
      (nominalP ^ 2 - nominalQ ^ 2 * nominalR) := by
  simpa only [discriminant, pow_two, sub_eq_add_neg] using
    add_rel (mul_rel hp hp) (neg_rel (mul_rel (mul_rel hq hq) hr))

/-- Componentwise errors control the error in `p² - q²r`. -/
theorem discriminant_difference_abs_le (p q r p₀ q₀ r₀ : ℝ) :
    |(p ^ 2 - q ^ 2 * r) - (p₀ ^ 2 - q₀ ^ 2 * r₀)| ≤
      (|p| + |p₀|) * |p - p₀| + |q| ^ 2 * |r - r₀| +
        |r₀| * (|q| + |q₀|) * |q - q₀| := by
  have hpadd : |p + p₀| * |p - p₀| ≤
      (|p| + |p₀|) * |p - p₀| :=
    mul_le_mul_of_nonneg_right (abs_add_le p p₀) (abs_nonneg _)
  have hqadd : |r₀| * |q + q₀| * |q - q₀| ≤
      |r₀| * (|q| + |q₀|) * |q - q₀| := by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left (abs_add_le q q₀) (abs_nonneg _)
  calc
    |(p ^ 2 - q ^ 2 * r) - (p₀ ^ 2 - q₀ ^ 2 * r₀)| =
        |(p + p₀) * (p - p₀) - q ^ 2 * (r - r₀) -
          r₀ * (q + q₀) * (q - q₀)| := by
      congr 1
      ring
    _ ≤ |(p + p₀) * (p - p₀)| + |q ^ 2 * (r - r₀)| +
        |r₀ * (q + q₀) * (q - q₀)| := by
      calc
        _ ≤ |(p + p₀) * (p - p₀) - q ^ 2 * (r - r₀)| +
            |r₀ * (q + q₀) * (q - q₀)| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            abs_sub_le
              ((p + p₀) * (p - p₀) - q ^ 2 * (r - r₀)) 0
              (r₀ * (q + q₀) * (q - q₀))
        _ ≤ (|(p + p₀) * (p - p₀)| + |q ^ 2 * (r - r₀)|) +
            |r₀ * (q + q₀) * (q - q₀)| := by
          apply add_le_add _ le_rfl
          simpa only [sub_zero, zero_sub, abs_neg] using
            abs_sub_le ((p + p₀) * (p - p₀)) 0 (q ^ 2 * (r - r₀))
    _ = |p + p₀| * |p - p₀| + |q| ^ 2 * |r - r₀| +
        |r₀| * |q + q₀| * |q - q₀| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow]
    _ ≤ (|p| + |p₀|) * |p - p₀| + |q| ^ 2 * |r - r₀| +
        |r₀| * (|q| + |q₀|) * |q - q₀| :=
      add_le_add (add_le_add hpadd le_rfl) hqadd

/-- Strict component bounds give a strict numerical discriminant-error budget. -/
theorem discriminant_difference_abs_lt_of_bounds
    {p q r p₀ q₀ r₀ P P₀ Q Q₀ R₀ eP eQ eR : ℝ}
    (hp : |p| ≤ P) (hp₀ : |p₀| ≤ P₀)
    (hq : |q| ≤ Q) (hq₀ : |q₀| ≤ Q₀) (hr₀ : |r₀| ≤ R₀)
    (hep : |p - p₀| < eP) (heq : |q - q₀| < eQ)
    (her : |r - r₀| < eR)
    (hP : 0 < P) (hP₀ : 0 < P₀) (hQ : 0 < Q)
    (hQ₀ : 0 < Q₀) (hR₀ : 0 < R₀) :
    |(p ^ 2 - q ^ 2 * r) - (p₀ ^ 2 - q₀ ^ 2 * r₀)| <
      (P + P₀) * eP + Q ^ 2 * eR + R₀ * (Q + Q₀) * eQ := by
  apply (discriminant_difference_abs_le p q r p₀ q₀ r₀).trans_lt
  have hpTerm : (|p| + |p₀|) * |p - p₀| < (P + P₀) * eP := by
    calc
      _ ≤ (P + P₀) * |p - p₀| :=
        mul_le_mul_of_nonneg_right (add_le_add hp hp₀) (abs_nonneg _)
      _ < (P + P₀) * eP := mul_lt_mul_of_pos_left hep (add_pos hP hP₀)
  have hqSq : |q| ^ 2 ≤ Q ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (abs_nonneg q) hq
  have hqTerm : |q| ^ 2 * |r - r₀| < Q ^ 2 * eR := by
    calc
      _ ≤ Q ^ 2 * |r - r₀| :=
        mul_le_mul_of_nonneg_right hqSq (abs_nonneg _)
      _ < Q ^ 2 * eR := mul_lt_mul_of_pos_left her (pow_pos hQ 2)
  have hrq : |r₀| * (|q| + |q₀|) ≤ R₀ * (Q + Q₀) := by
    calc
      _ ≤ R₀ * (|q| + |q₀|) :=
        mul_le_mul_of_nonneg_right hr₀ (add_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ R₀ * (Q + Q₀) :=
        mul_le_mul_of_nonneg_left (add_le_add hq hq₀) hR₀.le
  have hrqTerm : |r₀| * (|q| + |q₀|) * |q - q₀| <
      R₀ * (Q + Q₀) * eQ := by
    calc
      _ ≤ R₀ * (Q + Q₀) * |q - q₀| :=
        mul_le_mul_of_nonneg_right hrq (abs_nonneg _)
      _ < R₀ * (Q + Q₀) * eQ :=
        mul_lt_mul_of_pos_left heq (mul_pos hR₀ (add_pos hQ hQ₀))
  exact add_lt_add (add_lt_add hpTerm hqTerm) hrqTerm

/-- Weighted-self formula operations on approximation data. -/
def operations : WeightedSelfFormulaOperations Approximation :=
  ⟨rational, add, neg, mul, pow⟩

/-- Componentwise weighted-self operations on pairs of real numbers. -/
def pairOperations : WeightedSelfFormulaOperations (ℝ × ℝ) :=
  ⟨fun q ↦ (q, q), fun a b ↦ (a.1 + b.1, a.2 + b.2),
    fun a ↦ (-a.1, -a.2), fun a b ↦ (a.1 * b.1, a.2 * b.2),
    fun a n ↦ (a.1 ^ n, a.2 ^ n)⟩

/-- Lift the approximation relation to a pair of exact and nominal values. -/
def pair_rel (a : Approximation) (p : ℝ × ℝ) : Prop := a.Rel p.1 p.2

/-- The compact error recurrence is sound for all three weighted-self formula outputs. -/
theorem formula_rel {atom : Fin 18 → Approximation}
    {exactAtom nominalAtom : Fin 18 → ℝ}
    (hatom : ∀ i, (atom i).Rel (exactAtom i) (nominalAtom i))
    {r b t : Approximation} {exactR exactB exactT nominalR nominalB nominalT : ℝ}
    (hr : r.Rel exactR nominalR) (hb : b.Rel exactB nominalB)
    (ht : t.Rel exactT nominalT) :
    let data := weightedSelfFormula operations atom r b t
    let pairedData := weightedSelfFormula pairOperations
      (fun i ↦ (exactAtom i, nominalAtom i)) (exactR, nominalR) (exactB, nominalB)
        (exactT, nominalT)
    data.p.Rel pairedData.p.1 pairedData.p.2 ∧
      data.q.Rel pairedData.q.1 pairedData.q.2 ∧
      data.radicand.Rel pairedData.radicand.1 pairedData.radicand.2 := by
  exact weightedSelfFormula_rel operations pairOperations pair_rel
    (fun q ↦ rational_rel q) (fun ha hb ↦ add_rel ha hb) (fun ha ↦ neg_rel ha)
    (fun ha hb ↦ mul_rel ha hb) (fun ha n ↦ pow_rel ha n)
    (fun i ↦ show pair_rel (atom i) (exactAtom i, nominalAtom i) from hatom i)
    (show pair_rel r (exactR, nominalR) from hr)
    (show pair_rel b (exactB, nominalB) from hb)
    (show pair_rel t (exactT, nominalT) from ht)

end Approximation

open Approximation

/-- Interpret the paired formula relation as exact and nominal real formulas. -/
theorem formula_rel_real {atom : Fin 18 → Approximation}
    {exactAtom nominalAtom : Fin 18 → ℝ}
    (hatom : ∀ i, (atom i).Rel (exactAtom i) (nominalAtom i))
    {r b t : Approximation} {exactR exactB exactT nominalR nominalB nominalT : ℝ}
    (hr : r.Rel exactR nominalR) (hb : b.Rel exactB nominalB)
    (ht : t.Rel exactT nominalT) :
    let data := weightedSelfFormula operations atom r b t
    let exactData := weightedSelfFormula weightedSelfRealFormulaOperations
      exactAtom exactR exactB exactT
    let nominalData := weightedSelfFormula weightedSelfRealFormulaOperations
      nominalAtom nominalR nominalB nominalT
    data.p.Rel exactData.p nominalData.p ∧
      data.q.Rel exactData.q nominalData.q ∧
      data.radicand.Rel exactData.radicand nominalData.radicand := by
  let pairedAtom := fun i ↦ (exactAtom i, nominalAtom i)
  let pairedData := weightedSelfFormula pairOperations pairedAtom
    (exactR, nominalR) (exactB, nominalB) (exactT, nominalT)
  let exactData := weightedSelfFormula weightedSelfRealFormulaOperations
    exactAtom exactR exactB exactT
  let nominalData := weightedSelfFormula weightedSelfRealFormulaOperations
    nominalAtom nominalR nominalB nominalT
  have h := formula_rel hatom hr hb ht
  change (weightedSelfFormula operations atom r b t).p.Rel pairedData.p.1 pairedData.p.2 ∧
    (weightedSelfFormula operations atom r b t).q.Rel pairedData.q.1 pairedData.q.2 ∧
    (weightedSelfFormula operations atom r b t).radicand.Rel
      pairedData.radicand.1 pairedData.radicand.2 at h
  have hleft := weightedSelfFormula_map pairOperations weightedSelfRealFormulaOperations
    Prod.fst (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) pairedAtom
    (exactR, nominalR) (exactB, nominalB) (exactT, nominalT)
  have hright := weightedSelfFormula_map pairOperations weightedSelfRealFormulaOperations
    Prod.snd (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) pairedAtom
    (exactR, nominalR) (exactB, nominalB) (exactT, nominalT)
  change pairedData.p.1 = exactData.p ∧ pairedData.q.1 = exactData.q ∧
    pairedData.radicand.1 = exactData.radicand at hleft
  change pairedData.p.2 = nominalData.p ∧ pairedData.q.2 = nominalData.q ∧
    pairedData.radicand.2 = nominalData.radicand at hright
  rw [hleft.1, hright.1] at h
  rw [hleft.2.1, hright.2.1] at h
  rw [hleft.2.2, hright.2.2] at h
  exact h

end

end WeightedSelfApproximation
end Bescovitch
