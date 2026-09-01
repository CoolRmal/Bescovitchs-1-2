/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.DyadicInterval

/-!
# Unbounded dyadic endpoint arithmetic

This module computes fixed-precision dyadic endpoints with unbounded integers.  Unlike
`DyadicInterval`, the computational type carries no ordering proof, so large generated
certificates remain small.  The containment theorems recover the proof-carrying semantics.
-/

@[expose] public section

namespace Bescovitch

/-- Two unbounded integer endpoints at a common dyadic precision. -/
structure IntegerInterval where
  /-- Lower endpoint numerator. -/
  lower : ℤ
  /-- Upper endpoint numerator. -/
  upper : ℤ
  deriving DecidableEq, Repr

namespace IntegerInterval

variable {precision : ℕ}

/-- Rational membership in an integer endpoint pair at the prescribed dyadic precision. -/
def Contains (interval : IntegerInterval) (precision : ℕ) (value : ℚ) : Prop :=
  DyadicInterval.value precision interval.lower ≤ value ∧
    value ≤ DyadicInterval.value precision interval.upper

/-- Outward-round a rational into unbounded integer endpoints. -/
def ofRat (precision : ℕ) (value : ℚ) : IntegerInterval :=
  let interval := DyadicInterval.ofRat precision value
  ⟨interval.lower, interval.upper⟩

/-- Add two integer endpoint pairs. -/
def add (left right : IntegerInterval) : IntegerInterval :=
  ⟨left.lower + right.lower, left.upper + right.upper⟩

/-- Negate an integer endpoint pair. -/
def neg (value : IntegerInterval) : IntegerInterval :=
  ⟨-value.upper, -value.lower⟩

/-- Outward-round the product of two integer endpoint pairs. -/
def mul (precision : ℕ) (left right : IntegerInterval) : IntegerInterval :=
  let scale : ℤ := 2 ^ precision
  let lower := min (min (left.lower * right.lower) (left.lower * right.upper))
    (min (left.upper * right.lower) (left.upper * right.upper))
  let upper := max (max (left.lower * right.lower) (left.lower * right.upper))
    (max (left.upper * right.lower) (left.upper * right.upper))
  ⟨lower / scale, -((-upper) / scale)⟩

private theorem lower_le_upper_of_contains {interval : IntegerInterval} {value : ℚ}
    (hvalue : interval.Contains precision value) : interval.lower ≤ interval.upper := by
  have hvalues : DyadicInterval.value precision interval.lower ≤
      DyadicInterval.value precision interval.upper := hvalue.1.trans hvalue.2
  have hdenominatorInt : (0 : ℤ) < DyadicInterval.denominator precision := by
    simp [DyadicInterval.denominator]
  have hdenominator : (0 : ℚ) < DyadicInterval.denominator precision := by
    exact_mod_cast hdenominatorInt
  simp only [DyadicInterval.value] at hvalues
  exact_mod_cast (div_le_div_iff_of_pos_right hdenominator).mp hvalues

private def toDyadic (interval : IntegerInterval)
    (hinterval : interval.lower ≤ interval.upper) : DyadicInterval precision :=
  ⟨interval.lower, interval.upper, hinterval⟩

/-- Outward rounding contains the original rational. -/
theorem ofRat_contains (precision : ℕ) (value : ℚ) :
    (ofRat precision value).Contains precision value := by
  simpa only [Contains, ofRat, DyadicInterval.Contains]
    using DyadicInterval.ofRat_contains precision value

/-- Integer endpoint addition preserves rational containment. -/
theorem add_contains {left right : IntegerInterval} {x y : ℚ}
    (hx : left.Contains precision x) (hy : right.Contains precision y) :
    (left.add right).Contains precision (x + y) := by
  let left' : DyadicInterval precision :=
    left.toDyadic (lower_le_upper_of_contains hx)
  let right' : DyadicInterval precision :=
    right.toDyadic (lower_le_upper_of_contains hy)
  simpa only [Contains, add, toDyadic, left', right',
    DyadicInterval.Contains, DyadicInterval.add]
    using DyadicInterval.add_contains (I := left') (J := right') hx hy

/-- Integer endpoint negation preserves rational containment. -/
theorem neg_contains {interval : IntegerInterval} {value : ℚ}
    (hvalue : interval.Contains precision value) :
    interval.neg.Contains precision (-value) := by
  let interval' : DyadicInterval precision :=
    interval.toDyadic (lower_le_upper_of_contains hvalue)
  simpa only [Contains, neg, toDyadic, interval',
    DyadicInterval.Contains, DyadicInterval.neg]
    using DyadicInterval.neg_contains (I := interval') hvalue

/-- Integer outward-rounded multiplication preserves rational containment. -/
theorem mul_contains {left right : IntegerInterval} {x y : ℚ}
    (hx : left.Contains precision x) (hy : right.Contains precision y) :
    (left.mul precision right).Contains precision (x * y) := by
  let left' : DyadicInterval precision :=
    left.toDyadic (lower_le_upper_of_contains hx)
  let right' : DyadicInterval precision :=
    right.toDyadic (lower_le_upper_of_contains hy)
  simpa only [Contains, mul, toDyadic, left', right',
      DyadicInterval.Contains, DyadicInterval.mul, DyadicInterval.denominator]
    using DyadicInterval.mul_contains (I := left') (J := right') hx hy

end IntegerInterval

end Bescovitch
