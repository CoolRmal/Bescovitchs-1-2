/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.RationalInterval
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact local certificate for the equality mixed chart

Near the endpoint equality configuration, the mixed score increases with both transverse
coordinates.  On the resulting unit-circle faces, its Hessian in the two antisymmetric swap
directions is negative definite.  This file builds the rational expressions and exact interval
checker used for those two facts.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Bescovitch

namespace WeightedMixedEqualityLocal

/-- Rational expressions in `n` real variables. -/
abbrev Expression (n : ℕ) := RationalExpression n

/-- A plane vector whose coordinates are rational expressions. -/
structure Vector (n : ℕ) where
  /-- First coordinate. -/
  first : Expression n
  /-- Second coordinate. -/
  second : Expression n

namespace Expression

/-- Difference of two rational expressions. -/
@[reducible] def sub {n : ℕ} (p q : Expression n) : Expression n := .add p (.neg q)

/-- Quotient of two rational expressions. -/
@[reducible] def div {n : ℕ} (p q : Expression n) : Expression n := .mul p (.inv q)

/-- Square of a rational expression. -/
@[reducible] def square {n : ℕ} (p : Expression n) : Expression n := .mul p p

/-- Formal partial derivative of a rational expression. -/
@[reducible] def partialDerivative {n : ℕ} (i : Fin n) : Expression n → Expression n
  | .var j => if i = j then .constant 1 else .constant 0
  | .constant _ => .constant 0
  | .add f g => .add (partialDerivative i f) (partialDerivative i g)
  | .neg f => .neg (partialDerivative i f)
  | .mul f g => .add (.mul (partialDerivative i f) g) (.mul f (partialDerivative i g))
  | .inv f => .neg (.mul (partialDerivative i f) (.mul (.inv f) (.inv f)))

/-- Finite sum of rational expressions. -/
@[reducible] def sum : {N n : ℕ} → (Fin N → Expression n) → Expression n
  | 0, _, _ => .constant 0
  | _ + 1, _, f => .add (f 0) (sum fun i ↦ f i.succ)

/-- Evaluation of a formal difference. -/
@[simp]
theorem eval_sub {n : ℕ} (p q : Expression n) (x : Fin n → ℝ) :
    (sub p q).eval x = p.eval x - q.eval x := by
  simp [RationalExpression.eval, sub_eq_add_neg]

/-- Evaluation of a formal quotient. -/
theorem eval_div {n : ℕ} (p q : Expression n) (x : Fin n → ℝ) :
    (div p q).eval x = p.eval x / q.eval x := by
  simp [RationalExpression.eval, div_eq_mul_inv]

/-- Evaluation of a formal square. -/
@[simp]
theorem eval_square {n : ℕ} (p : Expression n) (x : Fin n → ℝ) :
    (square p).eval x = p.eval x ^ 2 := by
  simp [RationalExpression.eval, pow_two]

/-- Evaluation of a finite formal sum. -/
@[simp]
theorem eval_sum {N n : ℕ} (f : Fin N → Expression n) (x : Fin n → ℝ) :
    (sum f).eval x = ∑ i, (f i).eval x := by
  induction N with
  | zero => simp [RationalExpression.eval]
  | succ N ih =>
      rw [Fin.sum_univ_succ]
      simp only [RationalExpression.eval]
      rw [ih]

end Expression

namespace Vector

/-- Sum of two rational plane vectors. -/
@[reducible] def add {n : ℕ} (p q : Vector n) : Vector n :=
  ⟨.add p.first q.first, .add p.second q.second⟩

/-- Negation of a rational plane vector. -/
@[reducible] def neg {n : ℕ} (p : Vector n) : Vector n := ⟨.neg p.first, .neg p.second⟩

/-- Difference of two rational plane vectors. -/
@[reducible] def sub {n : ℕ} (p q : Vector n) : Vector n := add p (neg q)

/-- Scalar multiplication of a rational plane vector. -/
@[reducible] def smul {n : ℕ} (a : Expression n) (p : Vector n) : Vector n :=
  ⟨.mul a p.first, .mul a p.second⟩

/-- Dot product of rational plane vectors. -/
@[reducible] def dot {n : ℕ} (p q : Vector n) : Expression n :=
  .add (.mul p.first q.first) (.mul p.second q.second)

/-- Coordinatewise formal partial derivative of a rational plane vector. -/
@[reducible] def partialDerivative {n : ℕ} (i : Fin n) (p : Vector n) : Vector n :=
  ⟨Expression.partialDerivative i p.first, Expression.partialDerivative i p.second⟩

/-- Evaluate a rational plane vector. -/
def eval {n : ℕ} (p : Vector n) (x : Fin n → ℝ) : (EuclideanSpace ℝ (Fin 2)) :=
  !₂[p.first.eval x, p.second.eval x]

/-- Evaluation preserves vector addition. -/
@[simp]
theorem eval_add {n : ℕ} (p q : Vector n) (x : Fin n → ℝ) :
    (add p q).eval x = p.eval x + q.eval x := by
  ext i
  fin_cases i <;> simp [eval, RationalExpression.eval]

/-- Evaluation preserves vector negation. -/
@[simp]
theorem eval_neg {n : ℕ} (p : Vector n) (x : Fin n → ℝ) :
    (neg p).eval x = -p.eval x := by
  ext i
  fin_cases i <;> simp [eval, RationalExpression.eval]

/-- Evaluation preserves vector subtraction. -/
theorem eval_sub {n : ℕ} (p q : Vector n) (x : Fin n → ℝ) :
    (sub p q).eval x = p.eval x - q.eval x := by
  simp [sub, sub_eq_add_neg]

/-- Evaluation preserves scalar multiplication. -/
@[simp]
theorem eval_smul {n : ℕ} (a : Expression n) (p : Vector n) (x : Fin n → ℝ) :
    (smul a p).eval x = a.eval x • p.eval x := by
  ext i
  fin_cases i <;> simp [eval, RationalExpression.eval]

/-- Evaluation preserves the dot product. -/
@[simp]
theorem eval_dot {n : ℕ} (p q : Vector n) (x : Fin n → ℝ) :
    (dot p q).eval x = ⟪p.eval x, q.eval x⟫_ℝ := by
  simp [eval, RationalExpression.eval, PiLp.inner_apply, Fin.sum_univ_two]
  ring

end Vector

/-- Stereographic unit direction with coordinate `z`, oriented toward the equality chart. -/
@[reducible] def direction {n : ℕ} (z : Expression n) : Vector n :=
  let denominator : Expression n := .add (.constant 1) z.square
  ⟨Expression.div (RationalExpression.neg (Expression.sub (.constant 1) z.square)) denominator,
    Expression.div (RationalExpression.mul (.constant 2) z) denominator⟩

/-- Counterclockwise quarter-turn of a rational plane vector. -/
@[reducible] def turn {n : ℕ} (v : Vector n) : Vector n := ⟨.neg v.second, v.first⟩

/-- The two endpoints of a chord in the equality lens chart. -/
@[reducible] def lensPair {n : ℕ} (c a h z : Expression n) : Vector n × Vector n :=
  let direction := direction z
  let first := (direction.smul a).add ((turn direction).smul h)
  let second := (direction.smul (a.sub c)).add ((turn direction).smul h)
  (first, second)

/-- A lens-chart chord whose first endpoint lies on the unit-circle face. -/
@[reducible] def facePair {n : ℕ} (c t z : Expression n) : Vector n × Vector n :=
  let denominator : Expression n := .add (.constant 1) t.square
  let a := (Expression.sub (.constant 1) t.square).div denominator
  let h := Expression.div (RationalExpression.mul (.constant 2) t) denominator
  lensPair c a h z

/-- The ten vectors whose norms occur in the weighted mixed score. -/
@[reducible] def scoreVectors {n : ℕ} (p₁ p₂ w₁ w₂ : Vector n) : Fin 10 → Vector n
  | 0 => ((⟨.constant 1, .constant 0⟩ : Vector n).sub p₁).sub w₁
  | 1 => ((⟨.constant 1, .constant 0⟩ : Vector n).sub p₂).sub w₂
  | 2 => (⟨.constant 1, .constant 0⟩ : Vector n).sub p₁
  | 3 => (⟨.constant 1, .constant 0⟩ : Vector n).sub w₁
  | 4 => ((⟨.constant 1, .constant 0⟩ : Vector n).sub p₁).sub w₂
  | 5 => ((⟨.constant 1, .constant 0⟩ : Vector n).sub w₁).sub p₂
  | 6 => p₁
  | 7 => w₁
  | 8 => p₂
  | 9 => w₂

/-- The ten coefficients of the weighted mixed score. -/
@[reducible] def scoreWeights {n : ℕ} (c lambda mu : Expression n) : Fin 10 → Expression n
  | 0 => .add (.constant 1) lambda
  | 1 => .constant 1
  | 2 | 3 | 4 | 5 => .mul mu (.constant (1 / 2))
  | 6 | 7 => .neg (.mul
      (.mul (Expression.sub c (.constant 1))
        (.add (.mul lambda (.constant (1 / 2))) mu)) (.constant (1 / 2)))
  | 8 | 9 => .neg (.mul
      (.add (.mul (.add c (.constant 1)) (.mul lambda (.constant (1 / 2))))
        (.mul (.mul (.constant 3) c) mu)) (.constant (1 / 2)))

/-- The ten norm vectors in the transverse-coordinate score. -/
@[reducible] def transverseVectors : Fin 10 → Vector 9 :=
  let c : Expression 9 := .var 0
  let p := lensPair c (.var 3) (.var 4) (.var 5)
  let w := lensPair c (.var 6) (.var 7) (.var 8)
  scoreVectors p.1 p.2 w.1 w.2

/-- The exact derivative of the local score with respect to the first transverse coordinate.
The last ten inputs are the ten positive norm values. -/
@[reducible] def transverseDerivativeVectors : Fin 10 → Vector 19 :=
  let c : Expression 19 := .var 0
  let p := lensPair c (.var 3) (.var 4) (.var 5)
  let w := lensPair c (.var 6) (.var 7) (.var 8)
  scoreVectors p.1 p.2 w.1 w.2

/-- The symbolic weights in the transverse derivative certificate. -/
@[reducible] def transverseDerivativeWeights : Fin 10 → Expression 19 :=
  scoreWeights (.var 0) (.var 1) (.var 2)

/-- The exact derivative of the local score with respect to the first transverse coordinate.
The last ten inputs are the ten positive norm values. -/
@[reducible] def transverseDerivativeExpression : Expression 19 :=
  Expression.sum fun i ↦
    Expression.div
      (RationalExpression.mul (transverseDerivativeWeights i)
        ((transverseDerivativeVectors i).dot
          ((transverseDerivativeVectors i).partialDerivative 4)))
      (.var (Fin.natAdd 9 i))

/-- Difference of two formal coordinate derivatives. -/
@[reducible] def antiDerivative {n : ℕ} (i j : Fin n) (v : Vector n) : Vector n :=
  (v.partialDerivative i).sub (v.partialDerivative j)

/-- Iterated antisymmetric formal derivative in two coordinate pairs. -/
@[reducible] def antiSecondDerivative {n : ℕ} (i₁ i₂ j₁ j₂ : Fin n)
    (v : Vector n) : Vector n :=
  (((v.partialDerivative i₁).partialDerivative j₁).sub
      ((v.partialDerivative i₁).partialDerivative j₂)).sub
    (((v.partialDerivative i₂).partialDerivative j₁).sub
      ((v.partialDerivative i₂).partialDerivative j₂))

/-- Formal mixed Hessian entry for the norm of a rational vector. -/
@[reducible] def normAntiHessian {n : ℕ} (v : Vector n) (r : Expression n)
    (i₁ i₂ j₁ j₂ : Fin n) : Expression n :=
  let di := antiDerivative i₁ i₂ v
  let dj := antiDerivative j₁ j₂ v
  let dij := antiSecondDerivative i₁ i₂ j₁ j₂ v
  Expression.sub
    (Expression.div (RationalExpression.add (di.dot dj) (v.dot dij)) r)
    (Expression.div (RationalExpression.mul (v.dot di) (v.dot dj))
      (RationalExpression.mul r (RationalExpression.mul r r)))

/-- The ten norm vectors in the unit-circle face score. -/
@[reducible] def faceVectors : Fin 10 → Vector 7 :=
  let c : Expression 7 := .var 0
  let p := facePair c (.var 3) (.var 4)
  let w := facePair c (.var 5) (.var 6)
  scoreVectors p.1 p.2 w.1 w.2

/-- The symbolic score vectors used by the 17-variable face Hessian certificate. -/
@[reducible] def faceHessianVectors : Fin 10 → Vector 17 :=
  let c : Expression 17 := .var 0
  let p := facePair c (.var 3) (.var 4)
  let w := facePair c (.var 5) (.var 6)
  scoreVectors p.1 p.2 w.1 w.2

/-- The symbolic weights used by the face Hessian certificate. -/
@[reducible] def faceHessianWeights : Fin 10 → Expression 17 :=
  scoreWeights (.var 0) (.var 1) (.var 2)

/-- One entry of minus the antisymmetric Hessian of the face score. -/
@[reducible] def faceNegativeHessianEntry (first second : Bool) : Expression 17 :=
  let i : Fin 17 := if first then 3 else 4
  let i' : Fin 17 := if first then 5 else 6
  let j : Fin 17 := if second then 3 else 4
  let j' : Fin 17 := if second then 5 else 6
  .neg (Expression.sum fun k ↦
    .mul (faceHessianWeights k)
      (normAntiHessian (faceHessianVectors k) (.var (Fin.natAdd 7 k)) i i' j j'))

/-- The first diagonal entry of minus the antisymmetric face Hessian. -/
@[reducible] def faceNegativeHessian00 : Expression 17 := faceNegativeHessianEntry true true

/-- The off-diagonal entry of minus the antisymmetric face Hessian. -/
@[reducible] def faceNegativeHessian01 : Expression 17 := faceNegativeHessianEntry true false

/-- The transposed off-diagonal entry of minus the antisymmetric face Hessian. -/
@[reducible] def faceNegativeHessian10 : Expression 17 := faceNegativeHessianEntry false true

/-- The second diagonal entry of minus the antisymmetric face Hessian. -/
@[reducible] def faceNegativeHessian11 : Expression 17 := faceNegativeHessianEntry false false

/-- The determinant of minus the antisymmetric face Hessian. -/
@[reducible] def faceNegativeHessianDeterminant : Expression 17 :=
  Expression.sub (.mul faceNegativeHessian00 faceNegativeHessian11)
    (.mul faceNegativeHessian01 faceNegativeHessian10)

/-- Dyadic norm bounds stored by their lower numerator and nonnegative width. -/
structure NormBounds (N : ℕ) where
  /-- Lower endpoint numerator, with common denominator `2 ^ 41`. -/
  lowerNumerator : Fin N → ℤ
  /-- Nonnegative interval-width numerator, with common denominator `2 ^ 41`. -/
  widthNumerator : Fin N → ℕ

/-- A binary midpoint subdivision whose leaves carry dyadic norm bounds. -/
inductive LocalCertificateTree (n N : ℕ) where
  | leaf (bounds : NormBounds N)
  | split (axis : Fin n) (left right : LocalCertificateTree n N)

/-- Boolean universal quantification over a finite type. -/
@[reducible] def allFin : {N : ℕ} → (Fin N → Bool) → Bool
  | 0, _ => true
  | _ + 1, predicate => predicate 0 && allFin fun i ↦ predicate i.succ

/-- Characterization of Boolean universal quantification over `Fin N`. -/
theorem all_fin_eq_true {N : ℕ} (predicate : Fin N → Bool) :
    allFin predicate = true ↔ ∀ i, predicate i = true := by
  induction N with
  | zero => simp [allFin]
  | succ N ih =>
      rw [allFin, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hzero, hsucc⟩ i
        exact Fin.cases hzero hsucc i
      · intro h
        exact ⟨h 0, fun i ↦ h i.succ⟩

/-- The exact interval image under squaring. -/
@[reducible]
def intervalSquare (I : RationalInterval) : RationalInterval where
  lower := if I.upper ≤ 0 then I.upper ^ 2 else if 0 ≤ I.lower then I.lower ^ 2 else 0
  upper := max (I.lower ^ 2) (I.upper ^ 2)
  lower_le_upper := by
    split_ifs
    · exact le_max_right _ _
    · exact le_max_left _ _
    · exact (sq_nonneg _).trans (le_max_left _ _)

private theorem interval_square_contains {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) : (intervalSquare I).Contains (x ^ 2) := by
  norm_num only [RationalInterval.Contains, intervalSquare, Rat.cast_pow, Rat.cast_zero,
    Rat.cast_max] at hx ⊢
  split_ifs with hu hl
  · norm_num only [Rat.cast_pow] at ⊢
    have hlu : (I.lower : ℝ) ≤ I.upper := by exact_mod_cast I.lower_le_upper
    have hzero : (I.upper : ℝ) ≤ 0 := by exact_mod_cast hu
    have hl0 : (I.lower : ℝ) ≤ 0 := hlu.trans hzero
    have hx0 : x ≤ 0 := hx.2.trans hzero
    have hlower : (I.upper : ℝ) ^ 2 ≤ x ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (neg_nonneg.mpr <| add_nonpos hx0 hzero)]
    have hupper : x ^ 2 ≤ (I.lower : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (neg_nonneg.mpr <| add_nonpos hx0 hl0)]
    exact ⟨hlower, hupper.trans (le_max_left _ _)⟩
  · norm_num only [Rat.cast_pow] at ⊢
    have hl' : (0 : ℝ) ≤ I.lower := by exact_mod_cast hl
    have hlu : (I.lower : ℝ) ≤ I.upper := by exact_mod_cast I.lower_le_upper
    have hu' : (0 : ℝ) ≤ I.upper := hl'.trans hlu
    have hx0 : 0 ≤ x := hl'.trans hx.1
    have hlower : (I.lower : ℝ) ^ 2 ≤ x ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (add_nonneg hx0 hl')]
    have hupper : x ^ 2 ≤ (I.upper : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hu' hx0)]
    exact ⟨hlower, hupper.trans (le_max_right _ _)⟩
  · norm_num only [Rat.cast_zero, Rat.cast_pow] at ⊢
    constructor
    · exact sq_nonneg x
    · by_cases hx0 : 0 ≤ x
      · have hu0 : (0 : ℝ) ≤ I.upper := hx0.trans hx.2
        have hupper : x ^ 2 ≤ (I.upper : ℝ) ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hu0 hx0)]
        exact hupper.trans (le_max_right _ _)
      · have hl0 : (I.lower : ℝ) ≤ 0 := hx.1.trans (le_of_not_ge hx0)
        have hupper : x ^ 2 ≤ (I.lower : ℝ) ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hx.1)
            (neg_nonneg.mpr <| add_nonpos (le_of_not_ge hx0) hl0)]
        exact hupper.trans (le_max_left _ _)

/-- The exact dyadic interval encoded by one norm-bound witness. -/
@[reducible]
def NormBounds.exactInterval {N : ℕ} (bounds : NormBounds N) (i : Fin N) :
    RationalInterval where
  lower := (bounds.lowerNumerator i : ℚ) / 1099511627776
  upper := (bounds.lowerNumerator i : ℚ) / 1099511627776 +
    (bounds.widthNumerator i : ℚ) / 1099511627776
  lower_le_upper := le_add_of_nonneg_right (by positivity)

/-- Midpoint of an exact rational interval. -/
@[reducible]
def exactMidpoint (I : RationalInterval) : ℚ := (I.lower + I.upper) / 2

/-- Lower midpoint half of an exact interval. -/
@[reducible]
def exactLowerHalf (I : RationalInterval) : RationalInterval :=
  ⟨I.lower, exactMidpoint I, by dsimp [exactMidpoint]; linarith [I.lower_le_upper]⟩

/-- Upper midpoint half of an exact interval. -/
@[reducible]
def exactUpperHalf (I : RationalInterval) : RationalInterval :=
  ⟨exactMidpoint I, I.upper, by dsimp [exactMidpoint]; linarith [I.lower_le_upper]⟩

/-- Replace one box coordinate by its lower midpoint half. -/
@[reducible]
def exactSplitLower {n : ℕ} (box : Fin n → RationalInterval) (axis : Fin n) :
    Fin n → RationalInterval :=
  Function.update box axis (exactLowerHalf (box axis))

/-- Replace one box coordinate by its upper midpoint half. -/
@[reducible]
def exactSplitUpper {n : ℕ} (box : Fin n → RationalInterval) (axis : Fin n) :
    Fin n → RationalInterval :=
  Function.update box axis (exactUpperHalf (box axis))

/-- Append the encoded norm intervals to a geometric coordinate box. -/
@[reducible]
def exactExtendedBox {n N : ℕ} (box : Fin n → RationalInterval) (bounds : NormBounds N) :
    Fin (n + N) → RationalInterval :=
  Fin.addCases box bounds.exactInterval

/-- Check one exact dyadic witness for the norm of a symbolic vector. -/
@[reducible]
def exactNormWitnessCheck {n N : ℕ} (vectors : Fin N → Vector n)
    (box : Fin n → RationalInterval) (bounds : NormBounds N) (i : Fin N) : Bool :=
  match RationalExpression.enclosure (vectors i).first box,
      RationalExpression.enclosure (vectors i).second box with
  | some first, some second =>
      let squareNorm := (intervalSquare first).add (intervalSquare second)
      let norm := bounds.exactInterval i
      decide (0 < norm.lower ∧ norm.lower ^ 2 ≤ squareNorm.lower ∧
        squareNorm.upper ≤ norm.upper ^ 2)
  | _, _ => false

/-- Check that exact interval evaluation proves strict positivity. -/
@[reducible]
def exactPositiveEnclosureCheck {n : ℕ} (expression : Expression n)
    (box : Fin n → RationalInterval) : Bool :=
  match RationalExpression.enclosure expression box with
  | some result => decide (0 < result.lower)
  | none => false

/-- Check all norm witnesses and the target sign at one exact tree leaf. -/
@[reducible]
def exactLocalLeafChecks {n N : ℕ} (vectors : Fin N → Vector n)
    (expression : Expression (n + N)) (box : Fin n → RationalInterval)
    (bounds : NormBounds N) : Bool :=
  allFin (exactNormWitnessCheck vectors box bounds) &&
    exactPositiveEnclosureCheck expression (exactExtendedBox box bounds)

/-- Reducibly check an exact local interval tree. -/
@[reducible]
def exactLocalTreeCertifies {n N : ℕ} [DecidableEq (Fin n)] (vectors : Fin N → Vector n)
    (expression : Expression (n + N)) : LocalCertificateTree n N →
      (Fin n → RationalInterval) → Bool
  | .leaf bounds, box => exactLocalLeafChecks vectors expression box bounds
  | .split axis left right, box =>
      exactLocalTreeCertifies vectors expression left (exactSplitLower box axis) &&
        exactLocalTreeCertifies vectors expression right (exactSplitUpper box axis)

/-- Check only the target expression on every leaf of an exact local tree. -/
@[reducible]
def exactPositiveTreeCertifies {n N : ℕ} [DecidableEq (Fin n)]
    (expression : Expression (n + N)) : LocalCertificateTree n N →
      (Fin n → RationalInterval) → Bool
  | .leaf bounds, box =>
      exactPositiveEnclosureCheck expression (exactExtendedBox box bounds)
  | .split axis left right, box =>
      exactPositiveTreeCertifies expression left (exactSplitLower box axis) &&
        exactPositiveTreeCertifies expression right (exactSplitUpper box axis)

/-- Reuse one tree's norm witnesses when checking a second expression on the same leaves. -/
theorem exact_local_tree_of_positive_tree {n N : ℕ} [DecidableEq (Fin n)]
    (vectors : Fin N → Vector n) (source target : Expression (n + N))
    (tree : LocalCertificateTree n N) (box : Fin n → RationalInterval)
    (hsource : exactLocalTreeCertifies vectors source tree box = true)
    (htarget : exactPositiveTreeCertifies target tree box = true) :
    exactLocalTreeCertifies vectors target tree box = true := by
  induction tree generalizing box with
  | leaf bounds =>
      simp only [exactLocalTreeCertifies, exactLocalLeafChecks, Bool.and_eq_true] at hsource ⊢
      simpa only [exactPositiveTreeCertifies] using ⟨hsource.1, htarget⟩
  | split axis left right ihleft ihright =>
      simp only [exactLocalTreeCertifies, exactPositiveTreeCertifies, Bool.and_eq_true]
        at hsource htarget ⊢
      exact ⟨ihleft _ hsource.1 htarget.1, ihright _ hsource.2 htarget.2⟩

private theorem exact_norm_mem_of_check {n N : ℕ} (vectors : Fin N → Vector n)
    (box : Fin n → RationalInterval) (bounds : NormBounds N) (x : Fin n → ℝ)
    (hx : ∀ i, (box i).Contains (x i)) (i : Fin N)
    (hcheck : exactNormWitnessCheck vectors box bounds i = true) :
    (bounds.exactInterval i).Contains ‖(vectors i).eval x‖ := by
  rw [exactNormWitnessCheck] at hcheck
  split at hcheck <;> try contradiction
  next first second hfirst hsecond =>
    have hvalid : 0 < (bounds.exactInterval i).lower ∧
        (bounds.exactInterval i).lower ^ 2 ≤
          ((intervalSquare first).add (intervalSquare second)).lower ∧
        ((intervalSquare first).add (intervalSquare second)).upper ≤
          (bounds.exactInterval i).upper ^ 2 :=
      of_decide_eq_true hcheck
    have hsquare := RationalInterval.add_contains
      (interval_square_contains <| RationalExpression.enclosure_sound hx hfirst)
      (interval_square_contains <| RationalExpression.enclosure_sound hx hsecond)
    have hnormsq : ‖(vectors i).eval x‖ ^ 2 =
        (vectors i).first.eval x ^ 2 + (vectors i).second.eval x ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Vector.eval, Fin.sum_univ_two]
    norm_num only [RationalInterval.Contains, Rat.cast_le] at hsquare ⊢
    have hlower0 : (0 : ℝ) ≤ (bounds.exactInterval i).lower := by
      exact_mod_cast hvalid.1.le
    have hupper0 : (0 : ℝ) ≤ (bounds.exactInterval i).upper := by
      have hleQ : (bounds.exactInterval i).lower ≤ (bounds.exactInterval i).upper := by
        change (bounds.lowerNumerator i : ℚ) / 1099511627776 ≤
          (bounds.lowerNumerator i : ℚ) / 1099511627776 +
            (bounds.widthNumerator i : ℚ) / 1099511627776
        exact le_add_of_nonneg_right (by positivity)
      exact hlower0.trans (by exact_mod_cast hleQ)
    have hlowerSquare :
        ((bounds.exactInterval i).lower : ℝ) ^ 2 ≤ ‖(vectors i).eval x‖ ^ 2 := by
      calc
        _ ≤ (((intervalSquare first).add (intervalSquare second)).lower : ℝ) := by
          exact_mod_cast hvalid.2.1
        _ ≤ (vectors i).first.eval x ^ 2 + (vectors i).second.eval x ^ 2 := hsquare.1
        _ = _ := hnormsq.symm
    have hupperSquare : ‖(vectors i).eval x‖ ^ 2 ≤
        ((bounds.exactInterval i).upper : ℝ) ^ 2 := by
      calc
        _ = (vectors i).first.eval x ^ 2 + (vectors i).second.eval x ^ 2 := hnormsq
        _ ≤ (((intervalSquare first).add (intervalSquare second)).upper : ℝ) := hsquare.2
        _ ≤ _ := by exact_mod_cast hvalid.2.2
    exact ⟨(sq_le_sq₀ hlower0 (norm_nonneg _)).mp hlowerSquare,
      (sq_le_sq₀ (norm_nonneg _) hupper0).mp hupperSquare⟩

private theorem exact_extended_box_contains {n N : ℕ} (vectors : Fin N → Vector n)
    (box : Fin n → RationalInterval) (bounds : NormBounds N) (x : Fin n → ℝ)
    (hx : ∀ i, (box i).Contains (x i))
    (hcheck : ∀ i, exactNormWitnessCheck vectors box bounds i = true) (i : Fin (n + N)) :
    (exactExtendedBox box bounds i).Contains
      (Fin.addCases x (fun j ↦ ‖(vectors j).eval x‖) i) := by
  refine Fin.addCases ?_ ?_ i
  · simpa [exactExtendedBox] using hx
  · intro j
    simpa [exactExtendedBox] using exact_norm_mem_of_check vectors box bounds x hx j (hcheck j)

private theorem exact_lower_or_upper_contains {n : ℕ} (box : Fin n → RationalInterval)
    (axis : Fin n) (x : Fin n → ℝ) (hx : ∀ i, (box i).Contains (x i)) :
    (∀ i, (exactSplitLower box axis i).Contains (x i)) ∨
      (∀ i, (exactSplitUpper box axis i).Contains (x i)) := by
  by_cases h : x axis ≤ exactMidpoint (box axis)
  · left
    norm_num [exactMidpoint] at h
    intro i
    by_cases hi : i = axis
    · subst i
      simpa [exactSplitLower, exactLowerHalf, RationalInterval.Contains] using
        ⟨(hx axis).1, h⟩
    · simpa [exactSplitLower, hi] using hx i
  · right
    intro i
    by_cases hi : i = axis
    · subst i
      have hmid : (exactMidpoint (box axis) : ℝ) ≤ x axis := le_of_not_ge h
      norm_num [exactMidpoint] at hmid
      simpa [exactSplitUpper, exactUpperHalf, RationalInterval.Contains] using
        ⟨hmid, (hx axis).2⟩
    · simpa [exactSplitUpper, hi] using hx i

/-- A successful exact tree proves the target sign and strict positivity of every norm. -/
theorem exact_local_tree_sound {n N : ℕ} [DecidableEq (Fin n)]
    (vectors : Fin N → Vector n) (expression : Expression (n + N))
    (tree : LocalCertificateTree n N) (box : Fin n → RationalInterval)
    (hcertificate : exactLocalTreeCertifies vectors expression tree box = true)
    (x : Fin n → ℝ) (hx : ∀ i, (box i).Contains (x i)) :
    0 < expression.eval (Fin.addCases x fun i ↦ ‖(vectors i).eval x‖) ∧
      ∀ i, 0 < ‖(vectors i).eval x‖ := by
  induction tree generalizing box with
  | leaf bounds =>
      simp only [exactLocalTreeCertifies, exactLocalLeafChecks, Bool.and_eq_true,
        all_fin_eq_true] at hcertificate
      cases hresult : RationalExpression.enclosure expression
          (exactExtendedBox box bounds) with
      | none =>
          simp [exactPositiveEnclosureCheck, hresult] at hcertificate
      | some result =>
        have hpositive : 0 < result.lower := by
          exact of_decide_eq_true (by
            simpa [exactPositiveEnclosureCheck, hresult] using hcertificate.2)
        have hcontains := RationalExpression.enclosure_sound
          (f := expression) (I := result)
          (exact_extended_box_contains vectors box bounds x hx hcertificate.1) hresult
        refine ⟨lt_of_lt_of_le (by exact_mod_cast hpositive) hcontains.1, ?_⟩
        intro i
        have hnorm := exact_norm_mem_of_check vectors box bounds x hx i
          (hcertificate.1 i)
        have hlower : (0 : ℝ) < (bounds.exactInterval i).lower := by
          have hcheck := hcertificate.1 i
          rw [exactNormWitnessCheck] at hcheck
          split at hcheck <;> try contradiction
          exact_mod_cast (of_decide_eq_true hcheck).1
        exact hlower.trans_le hnorm.1
  | split axis left right ihleft ihright =>
      simp only [exactLocalTreeCertifies, Bool.and_eq_true] at hcertificate
      rcases exact_lower_or_upper_contains box axis x hx with hlower | hupper
      · exact ihleft (exactSplitLower box axis) hcertificate.1 hlower
      · exact ihright (exactSplitUpper box axis) hcertificate.2 hupper

end WeightedMixedEqualityLocal

end Bescovitch
