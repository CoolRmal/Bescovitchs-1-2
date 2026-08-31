/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Unreduced exact rationals

This representation keeps arithmetic transparent to the kernel. Positive denominators exclude
junk values, while cross multiplication checks equality and order without normalization.
-/

@[expose] public section

namespace Bescovitch

/-- An unreduced rational with a positive denominator. -/
structure RawRat where
  /-- The signed numerator. -/
  num : ℤ
  /-- The positive denominator. -/
  den : PNat
  deriving DecidableEq, Repr

namespace RawRat

/-- Interpret an unreduced rational as an ordinary rational. -/
def interpret (value : RawRat) : ℚ := value.num / (value.den : ℕ)

/-- The canonical unreduced representative of an ordinary rational. -/
def ofRat (value : ℚ) : RawRat := ⟨value.num, ⟨value.den, value.den_pos⟩⟩

/-- Zero as an unreduced rational. -/
def zero : RawRat := ⟨0, 1⟩

/-- One as an unreduced rational. -/
def one : RawRat := ⟨1, 1⟩

/-- Addition without fraction reduction. -/
def add (left right : RawRat) : RawRat :=
  ⟨left.num * right.den + right.num * left.den, left.den * right.den⟩

/-- Additive inverse without fraction reduction. -/
def neg (value : RawRat) : RawRat := ⟨-value.num, value.den⟩

/-- Multiplication without fraction reduction. -/
def mul (left right : RawRat) : RawRat :=
  ⟨left.num * right.num, left.den * right.den⟩

private theorem coe_mul (left right : PNat) :
    ((left * right : PNat) : ℕ) = (left : ℕ) * (right : ℕ) := rfl

@[simp]
theorem interpret_ofRat (value : ℚ) : (ofRat value).interpret = value := by
  rw [interpret, ofRat]
  norm_num only [Int.cast_natCast]
  exact value.num_div_den

@[simp]
theorem interpret_zero : zero.interpret = 0 := by
  norm_num [interpret, zero]

@[simp]
theorem interpret_one : one.interpret = 1 := by
  norm_num [interpret, one]

@[simp]
theorem interpret_add (left right : RawRat) :
    (left.add right).interpret = left.interpret + right.interpret := by
  unfold interpret add
  simp only [coe_mul]
  norm_num only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  field_simp [show (left.den : ℕ) ≠ 0 from left.den.2.ne',
    show (right.den : ℕ) ≠ 0 from right.den.2.ne']

@[simp]
theorem interpret_neg (value : RawRat) : value.neg.interpret = -value.interpret := by
  rw [interpret, neg, interpret]
  norm_num only [Int.cast_neg]
  exact neg_div _ _

@[simp]
theorem interpret_mul (left right : RawRat) :
    (left.mul right).interpret = left.interpret * right.interpret := by
  unfold interpret mul
  simp only [coe_mul]
  norm_num only [Int.cast_mul, Nat.cast_mul]
  field_simp [show (left.den : ℕ) ≠ 0 from left.den.2.ne',
    show (right.den : ℕ) ≠ 0 from right.den.2.ne']

/-- Cross-multiplication equality for unreduced rationals. -/
def equivalent (left right : RawRat) : Bool :=
  decide (left.num * right.den = right.num * left.den)

/-- Cross-multiplication equality implies equality after interpretation. -/
theorem equivalent_sound {left right : RawRat} (h : equivalent left right = true) :
    left.interpret = right.interpret := by
  rw [equivalent, decide_eq_true_eq] at h
  rw [interpret, interpret]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  exact_mod_cast h

/-- Cross-multiplication comparison `≤` for positive denominators. -/
def lessEqual (left right : RawRat) : Bool :=
  decide (left.num * right.den ≤ right.num * left.den)

/-- The executable comparison `lessEqual` agrees with rational order. -/
theorem lessEqual_iff (left right : RawRat) :
    lessEqual left right = true ↔ left.interpret ≤ right.interpret := by
  rw [lessEqual, decide_eq_true_eq, interpret, interpret]
  constructor
  · intro h
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    exact_mod_cast h
  · intro h
    have h' := (div_le_div_iff₀ (by positivity) (by positivity)).1 h
    exact_mod_cast h'

/-- Cross-multiplication comparison `<` for positive denominators. -/
def lessThan (left right : RawRat) : Bool :=
  decide (left.num * right.den < right.num * left.den)

/-- The executable comparison `lessThan` agrees with rational order. -/
theorem lessThan_iff (left right : RawRat) :
    lessThan left right = true ↔ left.interpret < right.interpret := by
  rw [lessThan, decide_eq_true_eq, interpret, interpret]
  constructor
  · intro h
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    exact_mod_cast h
  · intro h
    have h' := (div_lt_div_iff₀ (by positivity) (by positivity)).1 h
    exact_mod_cast h'

end RawRat

end Bescovitch
