/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.DyadicRealInterval
public import Bescovitch.Certificates.IntegerInterval

/-!
# Encoding unbounded dyadic endpoints

An ordered unbounded endpoint pair can be encoded at a fixed signed width.  The public theorem
states the exact guard needed to transfer rational containment to the guarded real semantics.
-/

@[expose] public section

namespace Bescovitch.IntegerInterval

variable {precision : ℕ}

/-- Regard an ordered integer endpoint pair as a proof-carrying dyadic interval. -/
def asDyadic (interval : IntegerInterval)
    (hordered : interval.lower ≤ interval.upper) : DyadicInterval precision :=
  ⟨interval.lower, interval.upper, hordered⟩

/-- Encode an ordered integer endpoint pair at a fixed signed width. -/
def toFixed (width : ℕ) (interval : IntegerInterval)
    (hordered : interval.lower ≤ interval.upper) : FixedDyadicInterval width precision :=
  FixedDyadicInterval.fromDyadic width (interval.asDyadic hordered)

private theorem toFixed_represents {width : ℕ} {interval : IntegerInterval}
    {hordered : interval.lower ≤ interval.upper}
    (hok : (interval.toFixed (precision := precision) width hordered).ok = true) :
    (interval.toFixed (precision := precision) width hordered).Represents
      (interval.asDyadic (precision := precision) hordered) := by
  simp only [toFixed, FixedDyadicInterval.Represents,
    FixedDyadicInterval.fromDyadic, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  exact ⟨hok, hok.1.1, hok.1.2⟩

private theorem asDyadic_contains_real {interval : IntegerInterval} {value : ℚ}
    {hordered : interval.lower ≤ interval.upper}
    (hcontains : interval.Contains precision value) :
    (interval.asDyadic (precision := precision) hordered).ContainsReal (value : ℝ) := by
  simp only [IntegerInterval.Contains, DyadicInterval.value] at hcontains
  simp only [DyadicInterval.ContainsReal, DyadicInterval.interpret,
    RationalInterval.Contains, DyadicInterval.value, Rat.cast_div,
    Rat.cast_intCast, asDyadic]
  constructor
  · exact_mod_cast hcontains.1
  · exact_mod_cast hcontains.2

/-- Successful fixed-width encoding preserves rational containment over the reals. -/
theorem toFixed_contains_real {width : ℕ} {interval : IntegerInterval} {value : ℚ}
    {hordered : interval.lower ≤ interval.upper}
    (hcontains : interval.Contains precision value)
    (hok : (interval.toFixed (precision := precision) width hordered).ok = true) :
    (interval.toFixed (precision := precision) width hordered).ContainsReal (value : ℝ) :=
  ⟨interval.asDyadic (precision := precision) hordered,
    toFixed_represents hok, asDyadic_contains_real hcontains⟩

end Bescovitch.IntegerInterval
