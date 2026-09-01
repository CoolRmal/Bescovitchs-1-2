/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.ScalarTraceVerifier
public import Bescovitch.Certificates.DyadicIntervalPolynomial

/-!
# Scalar materialization for the exceptional weighted-self face

The exceptional face certificate is evaluated in short scalar stages. The expression in each
stage is fixed in Lean, while the certificate supplies only a claimed dyadic output. A successful
check identifies that output with the same outward-rounded computation over unbounded integers.
-/

@[expose] public section

namespace Bescovitch.ExceptionalFaceTrace

open ScalarTraceVerifier

variable {Input : Type*} {width precision : ℕ}

/-- A fixed scalar interval expression with named inputs. -/
inductive Expression (Input : Type*) where
  | input (index : Input)
  | rational (value : ℚ)
  | add (left right : Expression Input)
  | neg (value : Expression Input)
  | mul (left right : Expression Input)

/-- Evaluate a scalar expression with guarded fixed-width intervals. -/
def Expression.evalFixed (inputs : Input → FixedDyadicInterval width precision) :
    Expression Input → FixedDyadicInterval width precision
  | .input index => inputs index
  | .rational value => FixedDyadicInterval.ofRat width precision value
  | .add left right => (left.evalFixed inputs).add (right.evalFixed inputs)
  | .neg value => (value.evalFixed inputs).neg
  | .mul left right => (left.evalFixed inputs).mul (right.evalFixed inputs)

/-- Evaluate the same scalar expression with unbounded dyadic intervals. -/
def Expression.evalDyadic (inputs : Input → DyadicInterval precision) :
    Expression Input → DyadicInterval precision
  | .input index => inputs index
  | .rational value => DyadicInterval.ofRat precision value
  | .add left right => (left.evalDyadic inputs).add (right.evalDyadic inputs)
  | .neg value => (value.evalDyadic inputs).neg
  | .mul left right => (left.evalDyadic inputs).mul (right.evalDyadic inputs)

/-- Evaluate the interval expression before dyadic outward rounding. -/
def Expression.evalInterval (inputs : Input → RationalInterval) :
    Expression Input → RationalInterval
  | .input index => inputs index
  | .rational value => .singleton value
  | .add left right => (left.evalInterval inputs).add (right.evalInterval inputs)
  | .neg value => (value.evalInterval inputs).neg
  | .mul left right => (left.evalInterval inputs).mul (right.evalInterval inputs)

private theorem fromDyadic_represents (value : DyadicInterval precision)
    (hok : (FixedDyadicInterval.fromDyadic width value).ok = true) :
    (FixedDyadicInterval.fromDyadic width value).Represents value := by
  simp only [FixedDyadicInterval.Represents, FixedDyadicInterval.fromDyadic,
    Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  exact ⟨hok, hok.1.1, hok.1.2⟩

private theorem ok_left_of_add
    {left right : FixedDyadicInterval width precision}
    (h : (left.add right).ok = true) : left.ok = true := by
  simp only [FixedDyadicInterval.add, FixedDyadicInterval.additionSafe,
    Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1

private theorem ok_right_of_add
    {left right : FixedDyadicInterval width precision}
    (h : (left.add right).ok = true) : right.ok = true := by
  simp only [FixedDyadicInterval.add, FixedDyadicInterval.additionSafe,
    Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

private theorem ok_of_neg {value : FixedDyadicInterval width precision}
    (h : value.neg.ok = true) : value.ok = true := by
  simp only [FixedDyadicInterval.neg, FixedDyadicInterval.negationSafe,
    Bool.and_eq_true] at h
  exact h.1.1.1

private theorem ok_left_of_mul
    {left right : FixedDyadicInterval width precision}
    (h : (left.mul right).ok = true) : left.ok = true := by
  simp only [FixedDyadicInterval.mul, FixedDyadicInterval.multiplicationSafe,
    Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

private theorem ok_right_of_mul
    {left right : FixedDyadicInterval width precision}
    (h : (left.mul right).ok = true) : right.ok = true := by
  simp only [FixedDyadicInterval.mul, FixedDyadicInterval.multiplicationSafe,
    Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

/-- Guarded evaluation represents the unbounded evaluation of the fixed expression. -/
theorem Expression.evalFixed_represents
    {fixedInputs : Input → FixedDyadicInterval width precision}
    {dyadicInputs : Input → DyadicInterval precision}
    (hinputs : ∀ i, (fixedInputs i).Represents (dyadicInputs i))
    (expression : Expression Input) (hok : (expression.evalFixed fixedInputs).ok = true) :
    (expression.evalFixed fixedInputs).Represents
      (expression.evalDyadic dyadicInputs) := by
  induction expression with
  | input index => exact hinputs index
  | rational value =>
      exact FixedDyadicInterval.ofRat_represents width precision value hok
  | add left right leftIH rightIH =>
      exact FixedDyadicInterval.add_represents
        (leftIH (ok_left_of_add hok)) (rightIH (ok_right_of_add hok)) hok
  | neg value ih =>
      exact FixedDyadicInterval.neg_represents (ih (ok_of_neg hok)) hok
  | mul left right leftIH rightIH =>
      exact FixedDyadicInterval.mul_represents
        (leftIH (ok_left_of_mul hok)) (rightIH (ok_right_of_mul hok)) hok

/-- Check a proof-free claimed output against a fixed scalar expression. -/
def Expression.check (fixedInputs : Input → FixedDyadicInterval width precision)
    (expression : Expression Input) (claim : EncodedInterval width) : Bool :=
  matchClaim (expression.evalFixed fixedInputs) claim

/-- A successful scalar check makes the claim represent the fixed expression's exact value. -/
theorem Expression.claim_represents
    {fixedInputs : Input → FixedDyadicInterval width precision}
    {dyadicInputs : Input → DyadicInterval precision}
    (hinputs : ∀ i, (fixedInputs i).Represents (dyadicInputs i))
    {expression : Expression Input} {claim : EncodedInterval width}
    (hcheck : expression.check fixedInputs claim = true) :
    claim.decode.Represents (expression.evalDyadic dyadicInputs) := by
  have hmatch : matchClaim (expression.evalFixed fixedInputs) claim = true := hcheck
  have hok : (expression.evalFixed fixedInputs).ok = true := by
    have hparts := hmatch
    simp only [matchClaim, Bool.and_eq_true] at hparts
    exact hparts.1.1
  rw [← eq_decode_of_matches hmatch]
  exact expression.evalFixed_represents hinputs hok

/-- Unbounded dyadic evaluation encloses the corresponding rational interval expression. -/
theorem Expression.evalDyadic_widens
    {dyadicInputs : Input → DyadicInterval precision}
    {intervalInputs : Input → RationalInterval}
    (hinputs : ∀ i, (dyadicInputs i).Widens (intervalInputs i))
    (expression : Expression Input) :
    (expression.evalDyadic dyadicInputs).Widens
      (expression.evalInterval intervalInputs) := by
  induction expression with
  | input index => exact hinputs index
  | rational value => exact DyadicInterval.ofInterval_widens precision (.singleton value)
  | add left right leftIH rightIH => exact DyadicInterval.add_widens leftIH rightIH
  | neg value ih => exact DyadicInterval.neg_widens ih
  | mul left right leftIH rightIH => exact DyadicInterval.mul_widens leftIH rightIH

private theorem interpret_contains_of_widens
    {value : DyadicInterval precision} {interval : RationalInterval} {x : ℝ}
    (hvalue : value.Widens interval) (hx : interval.Contains x) :
    value.interpret.Contains x := by
  constructor
  · have hlower : (value.interpret.lower : ℝ) ≤ interval.lower := by
      exact_mod_cast hvalue.1.1
    exact hlower.trans hx.1
  · have hupper : (interval.upper : ℝ) ≤ value.interpret.upper := by
      exact_mod_cast hvalue.2.2
    exact hx.2.trans hupper

/-- A checked nonnegative claim proves every enclosed real expression is nonnegative. -/
theorem Expression.nonnegative_of_check
    {fixedInputs : Input → FixedDyadicInterval width precision}
    {dyadicInputs : Input → DyadicInterval precision}
    {intervalInputs : Input → RationalInterval}
    (hfixed : ∀ i, (fixedInputs i).Represents (dyadicInputs i))
    (hwide : ∀ i, (dyadicInputs i).Widens (intervalInputs i))
    {expression : Expression Input} {claim : EncodedInterval width}
    (hcheck : expression.check fixedInputs claim = true)
    (hsign : claim.lowerNonnegative = true) {x : ℝ}
    (hx : (expression.evalInterval intervalInputs).Contains x) : 0 ≤ x := by
  have hrep := expression.claim_represents hfixed hcheck
  have hdyadicSign := dyadic_lowerNonnegative_of_encoded hrep hsign
  have hcontains := interpret_contains_of_widens
    (expression.evalDyadic_widens hwide) hx
  simp only [DyadicInterval.lowerNonnegative, decide_eq_true_eq] at hdyadicSign
  have hlower : (0 : ℝ) ≤
      (expression.evalDyadic dyadicInputs).interpret.lower := by
    have hden : (0 : ℚ) ≤ DyadicInterval.denominator precision := by
      have hdenInt : (0 : ℤ) < DyadicInterval.denominator precision := by
        simp [DyadicInterval.denominator]
      exact_mod_cast hdenInt.le
    have hrat : (0 : ℚ) ≤
        ((expression.evalDyadic dyadicInputs).lower : ℚ) /
          DyadicInterval.denominator precision :=
      div_nonneg (by exact_mod_cast hdyadicSign) hden
    change (0 : ℝ) ≤
      (((expression.evalDyadic dyadicInputs).lower : ℚ) /
        DyadicInterval.denominator precision : ℚ)
    exact_mod_cast hrat
  exact hlower.trans hcontains.1

/-- Evaluate the same fixed expression over real scalar inputs. -/
noncomputable def Expression.evalReal (inputs : Input → ℝ) :
    Expression Input → ℝ
  | .input index => inputs index
  | .rational value => value
  | .add left right => left.evalReal inputs + right.evalReal inputs
  | .neg value => -value.evalReal inputs
  | .mul left right => left.evalReal inputs * right.evalReal inputs

/-- Relabel the named inputs of a scalar expression. -/
def Expression.relabel {NewInput : Type*} (f : Input → NewInput) :
    Expression Input → Expression NewInput
  | .input index => .input (f index)
  | .rational value => .rational value
  | .add left right => .add (left.relabel f) (right.relabel f)
  | .neg value => .neg (value.relabel f)
  | .mul left right => .mul (left.relabel f) (right.relabel f)

private theorem Expression.evalReal_relabel {NewInput : Type*}
    (f : Input → NewInput) (inputs : NewInput → ℝ) (expression : Expression Input) :
    (expression.relabel f).evalReal inputs =
      expression.evalReal (fun i ↦ inputs (f i)) := by
  induction expression with
  | input index => rfl
  | rational value => rfl
  | add left right leftIH rightIH => simp [Expression.relabel, Expression.evalReal, leftIH,
      rightIH]
  | neg value ih => simp [Expression.relabel, Expression.evalReal, ih]
  | mul left right leftIH rightIH => simp [Expression.relabel, Expression.evalReal, leftIH,
      rightIH]

/-- Horner expression for a padded power vector at one rational coordinate. -/
def powerHornerExpression : (count : ℕ) → ℚ → Expression (Fin count)
  | 0, _ => .rational 0
  | count + 1, x => .add (.input 0)
      (.mul (.rational x) ((powerHornerExpression count x).relabel Fin.succ))

/-- Real evaluation of the Horner expression is the corresponding padded power sum. -/
theorem evalReal_powerHornerExpression (count : ℕ) (x : ℚ)
    (inputs : Fin count → ℝ) :
    (powerHornerExpression count x).evalReal inputs =
      ∑ i, inputs i * (x : ℝ) ^ (i : ℕ) := by
  induction count with
  | zero => simp [powerHornerExpression, Expression.evalReal]
  | succ count ih =>
      rw [Fin.sum_univ_succ]
      simp only [powerHornerExpression, Expression.evalReal,
        Expression.evalReal_relabel, ih]
      rw [Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one]
      apply congrArg (inputs 0 + ·)
      apply Finset.sum_congr rfl
      intro i hi
      change (x : ℝ) * (inputs i.succ * (x : ℝ) ^ i.val) =
        inputs i.succ * (x : ℝ) ^ (i.val + 1)
      rw [pow_succ]
      ring

/-- A fixed expression for a rational linear combination of named inputs. -/
def linearCombinationExpression :
    (count : ℕ) → (Fin count → ℚ) → Expression (Fin count)
  | 0, _ => .rational 0
  | count + 1, weight =>
      .add (.mul (.rational (weight 0)) (.input 0))
        ((linearCombinationExpression count (fun i ↦ weight i.succ)).relabel Fin.succ)

/-- Real evaluation of the fixed expression is the specified linear combination. -/
theorem evalReal_linearCombinationExpression (count : ℕ)
    (weight : Fin count → ℚ) (inputs : Fin count → ℝ) :
    (linearCombinationExpression count weight).evalReal inputs =
      ∑ i, (weight i : ℝ) * inputs i := by
  induction count with
  | zero => simp [linearCombinationExpression, Expression.evalReal]
  | succ count ih =>
      rw [Fin.sum_univ_succ]
      simp only [linearCombinationExpression, Expression.evalReal,
        Expression.evalReal_relabel, ih]

/-- Interval evaluation contains real evaluation whenever it contains every input. -/
theorem Expression.evalInterval_contains
    {intervalInputs : Input → RationalInterval} {realInputs : Input → ℝ}
    (hinputs : ∀ i, (intervalInputs i).Contains (realInputs i))
    (expression : Expression Input) :
    (expression.evalInterval intervalInputs).Contains
      (expression.evalReal realInputs) := by
  induction expression with
  | input index => exact hinputs index
  | rational value => exact RationalInterval.singleton_contains value
  | add left right leftIH rightIH => exact RationalInterval.add_contains leftIH rightIH
  | neg value ih => exact RationalInterval.neg_contains ih
  | mul left right leftIH rightIH => exact RationalInterval.mul_contains leftIH rightIH

/-- Round interval inputs into the guarded boundary state used by a scalar check. -/
def fixedIntervalInputs (width precision : ℕ) (inputs : Input → RationalInterval) :
    Input → FixedDyadicInterval width precision :=
  fun i ↦ FixedDyadicInterval.fromDyadic width
    (DyadicInterval.ofInterval precision (inputs i))

/-- Round interval inputs into the exact dyadic state represented by the guarded state. -/
def dyadicIntervalInputs (precision : ℕ) (inputs : Input → RationalInterval) :
    Input → DyadicInterval precision :=
  fun i ↦ DyadicInterval.ofInterval precision (inputs i)

private theorem Expression.evalFixed_represents_interval_inputs
    (inputs : Input → RationalInterval) (expression : Expression Input)
    (hok : (expression.evalFixed
      (fixedIntervalInputs width precision inputs)).ok = true) :
    (expression.evalFixed (fixedIntervalInputs width precision inputs)).Represents
      (expression.evalDyadic (dyadicIntervalInputs precision inputs)) := by
  induction expression with
  | input index => exact fromDyadic_represents _ hok
  | rational value =>
      exact FixedDyadicInterval.ofRat_represents width precision value hok
  | add left right leftIH rightIH =>
      exact FixedDyadicInterval.add_represents
        (leftIH (ok_left_of_add hok)) (rightIH (ok_right_of_add hok)) hok
  | neg value ih =>
      exact FixedDyadicInterval.neg_represents (ih (ok_of_neg hok)) hok
  | mul left right leftIH rightIH =>
      exact FixedDyadicInterval.mul_represents
        (leftIH (ok_left_of_mul hok)) (rightIH (ok_right_of_mul hok)) hok

/-- A checked expression over rounded interval inputs represents its exact dyadic evaluation. -/
theorem Expression.claim_represents_of_interval_inputs
    {inputs : Input → RationalInterval} {expression : Expression Input}
    {claim : EncodedInterval width}
    (hcheck : expression.check (fixedIntervalInputs width precision inputs) claim = true) :
    claim.decode.Represents
      (expression.evalDyadic (dyadicIntervalInputs precision inputs)) := by
  have hmatch : matchClaim
      (expression.evalFixed (fixedIntervalInputs width precision inputs)) claim = true := hcheck
  have hok :
      (expression.evalFixed (fixedIntervalInputs width precision inputs)).ok = true := by
    have hparts := hmatch
    simp only [matchClaim, Bool.and_eq_true] at hparts
    exact hparts.1.1
  rw [← eq_decode_of_matches hmatch]
  exact expression.evalFixed_represents_interval_inputs inputs hok

end Bescovitch.ExceptionalFaceTrace
