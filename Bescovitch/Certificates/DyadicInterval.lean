/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.RationalInterval
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Fixed-precision dyadic intervals

This module implements outward-rounded interval arithmetic with denominator `2 ^ precision`.
The fixed denominator keeps large exact certificate computations small while every rounding step
has a kernel-checked rational semantics.
-/

@[expose] public section

namespace Bescovitch

/-- A nonempty interval whose endpoints have the common denominator `2 ^ precision`. -/
structure DyadicInterval (precision : ℕ) where
  /-- Numerator of the lower endpoint. -/
  lower : ℤ
  /-- Numerator of the upper endpoint. -/
  upper : ℤ
  lower_le_upper : lower ≤ upper
  deriving DecidableEq, Repr

namespace DyadicInterval

variable {precision : ℕ}

/-- The positive common denominator of a dyadic interval. -/
def denominator (precision : ℕ) : ℤ := 2 ^ precision

private theorem denominator_pos (precision : ℕ) : 0 < denominator precision := by
  simp [denominator]

/-- Interpret a dyadic numerator at the prescribed precision. -/
def value (precision : ℕ) (numerator : ℤ) : ℚ :=
  numerator / denominator precision

/-- Rational membership in a dyadic interval. -/
def Contains (I : DyadicInterval precision) (q : ℚ) : Prop :=
  value precision I.lower ≤ q ∧ q ≤ value precision I.upper

/-- Interpret a dyadic interval as an ordinary rational interval. -/
def interpret (I : DyadicInterval precision) : RationalInterval where
  lower := value precision I.lower
  upper := value precision I.upper
  lower_le_upper := by
    have hden : (0 : ℚ) < denominator precision := by
      exact_mod_cast denominator_pos precision
    exact div_le_div_of_nonneg_right (by exact_mod_cast I.lower_le_upper)
      hden.le

private theorem ediv_mul_le (n d : ℤ) (hd : 0 < d) : n / d * d ≤ n :=
  Int.ediv_mul_le n hd.ne'

private theorem le_neg_ediv_neg_mul (n d : ℤ) (hd : 0 < d) :
    n ≤ -((-n) / d) * d := by
  have h := ediv_mul_le (-n) d hd
  linarith

private theorem ediv_le_neg_ediv_neg (n d : ℤ) (hd : 0 < d) :
    n / d ≤ -((-n) / d) := by
  apply (Int.mul_le_mul_right hd).mp
  exact (ediv_mul_le n d hd).trans (le_neg_ediv_neg_mul n d hd)

private theorem floorDiv_le (n d : ℤ) (hd : 0 < d) :
    ((n / d : ℤ) : ℚ) ≤ n / d := by
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast ediv_mul_le n d hd

private theorem le_ceilDiv (n d : ℤ) (hd : 0 < d) :
    (n : ℚ) / d ≤ ((-((-n) / d) : ℤ) : ℚ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast le_neg_ediv_neg_mul n d hd

/-- Outward-round one rational to the fixed dyadic precision. -/
def ofRat (precision : ℕ) (q : ℚ) : DyadicInterval precision :=
  let scaledNumerator : ℤ := q.num * denominator precision
  let rationalDenominator : ℤ := q.den
  ⟨scaledNumerator / rationalDenominator,
    -((-scaledNumerator) / rationalDenominator), by
      have hd : 0 < rationalDenominator := by positivity
      apply (Int.mul_le_mul_right hd).mp
      exact (Int.ediv_mul_le scaledNumerator hd.ne').trans (by
        have h := Int.ediv_mul_le (-scaledNumerator) hd.ne'
        linarith)⟩

/-- Exact interval addition at a fixed dyadic precision. -/
def add (I J : DyadicInterval precision) : DyadicInterval precision :=
  ⟨I.lower + J.lower, I.upper + J.upper,
    add_le_add I.lower_le_upper J.lower_le_upper⟩

/-- Exact interval negation at a fixed dyadic precision. -/
def neg (I : DyadicInterval precision) : DyadicInterval precision :=
  ⟨-I.upper, -I.lower, neg_le_neg I.lower_le_upper⟩

private def productLower (I J : DyadicInterval precision) : ℤ :=
  min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper))

private def productUpper (I J : DyadicInterval precision) : ℤ :=
  max (max (I.lower * J.lower) (I.lower * J.upper))
    (max (I.upper * J.lower) (I.upper * J.upper))

private theorem productLower_le_productUpper (I J : DyadicInterval precision) :
    productLower I J ≤ productUpper I J :=
  (min_le_left _ _).trans <| (min_le_left _ _).trans <|
    (le_max_left _ _).trans (le_max_left _ _)

/-- Outward-rounded interval multiplication at a fixed dyadic precision. -/
def mul (I J : DyadicInterval precision) : DyadicInterval precision :=
  let scale := denominator precision
  let lower := min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper))
  let upper := max (max (I.lower * J.lower) (I.lower * J.upper))
    (max (I.upper * J.lower) (I.upper * J.upper))
  ⟨lower / scale, -((-upper) / scale), by
    have hscale := denominator_pos precision
    have hlowerUpper : lower ≤ upper :=
      (min_le_left _ _).trans <| (min_le_left _ _).trans <|
        (le_max_left _ _).trans (le_max_left _ _)
    apply le_trans (Int.ediv_le_ediv hscale hlowerUpper)
    apply (Int.mul_le_mul_right hscale).mp
    exact (Int.ediv_mul_le upper hscale.ne').trans (by
      have h := Int.ediv_mul_le (-upper) hscale.ne'
      linarith)⟩

/-- The outward dyadic rounding of a rational contains that rational. -/
theorem ofRat_contains (precision : ℕ) (q : ℚ) : (ofRat precision q).Contains q := by
  let n : ℤ := q.num * denominator precision
  let d : ℤ := q.den
  have hd : 0 < d := by positivity
  have hscale : (0 : ℚ) < denominator precision := by
    exact_mod_cast denominator_pos precision
  constructor
  · change ((n / d : ℤ) : ℚ) / denominator precision ≤ q
    have h := floorDiv_le n d hd
    have h' := div_le_div_of_nonneg_right h hscale.le
    calc
      ((n / d : ℤ) : ℚ) / denominator precision ≤
          ((n : ℚ) / d) / denominator precision := h'
      _ = q := by
        rw [← Rat.num_div_den q]
        dsimp only [n, d]
        norm_num only [Int.cast_mul, Int.cast_natCast]
        field_simp [show (denominator precision : ℤ) ≠ 0 from
          (denominator_pos precision).ne']
  · change q ≤ (-((-n) / d) : ℤ) / denominator precision
    have h := le_ceilDiv n d hd
    have h' := div_le_div_of_nonneg_right h hscale.le
    calc
      q = ((n : ℚ) / d) / denominator precision := by
        rw [← Rat.num_div_den q]
        dsimp only [n, d]
        norm_num only [Int.cast_mul, Int.cast_natCast]
        field_simp [show (denominator precision : ℤ) ≠ 0 from
          (denominator_pos precision).ne']
      _ ≤ (-((-n) / d) : ℤ) / denominator precision := h'

/-- Outward-round both endpoints of an ordinary rational interval. -/
def ofInterval (precision : ℕ) (I : RationalInterval) : DyadicInterval precision where
  lower := (ofRat precision I.lower).lower
  upper := (ofRat precision I.upper).upper
  lower_le_upper := by
    have hl := (ofRat_contains precision I.lower).1
    have hu := (ofRat_contains precision I.upper).2
    have hvalues := hl.trans (I.lower_le_upper.trans hu)
    apply (Int.cast_le (R := ℚ)).mp
    apply (div_le_div_iff_of_pos_right (by
      exact_mod_cast denominator_pos precision :
        (0 : ℚ) < denominator precision)).mp
    exact hvalues

/-- Outward endpoint rounding contains the original rational interval. -/
theorem ofInterval_contains {I : RationalInterval} {q : ℚ}
    (hq : I.lower ≤ q ∧ q ≤ I.upper) : (ofInterval precision I).Contains q := by
  have hl := ofRat_contains precision I.lower
  have hu := ofRat_contains precision I.upper
  exact ⟨hl.1.trans hq.1, hq.2.trans hu.2⟩

/-- Dyadic interval addition preserves rational membership. -/
theorem add_contains {I J : DyadicInterval precision} {x y : ℚ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.add J).Contains (x + y) := by
  constructor <;> simp only [Contains, add, value] at hx hy ⊢
  · rw [Int.cast_add, add_div]
    exact add_le_add hx.1 hy.1
  · rw [Int.cast_add, add_div]
    exact add_le_add hx.2 hy.2

/-- Dyadic interval negation preserves rational membership. -/
theorem neg_contains {I : DyadicInterval precision} {x : ℚ}
    (hx : I.Contains x) : I.neg.Contains (-x) := by
  constructor <;> simp only [Contains, neg, value] at hx ⊢
  · rw [Int.cast_neg, neg_div]
    exact neg_le_neg hx.2
  · rw [Int.cast_neg, neg_div]
    exact neg_le_neg hx.1

private theorem exactProduct_contains {I J : DyadicInterval precision} {x y : ℚ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (productLower I J : ℚ) / denominator precision ^ 2 ≤ x * y ∧
      x * y ≤ (productUpper I J : ℚ) / denominator precision ^ 2 := by
  have hx' : I.interpret.Contains (x : ℝ) := by
    constructor
    · exact_mod_cast hx.1
    · exact_mod_cast hx.2
  have hy' : J.interpret.Contains (y : ℝ) := by
    constructor
    · exact_mod_cast hy.1
    · exact_mod_cast hy.2
  have h := RationalInterval.mul_contains
    (I := I.interpret) (J := J.interpret) (x := (x : ℝ)) (y := (y : ℝ))
    hx' hy'
  have h' :
      (I.interpret.mul J.interpret).lower ≤ x * y ∧
        x * y ≤ (I.interpret.mul J.interpret).upper := by
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have min_div (a b d : ℚ) (hd : 0 < d) :
      min a b / d = min (a / d) (b / d) := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab,
        min_eq_left ((div_le_div_iff_of_pos_right hd).2 hab)]
    · rw [min_eq_right hba,
        min_eq_right ((div_le_div_iff_of_pos_right hd).2 hba)]
  have max_div (a b d : ℚ) (hd : 0 < d) :
      max a b / d = max (a / d) (b / d) := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab,
        max_eq_right ((div_le_div_iff_of_pos_right hd).2 hab)]
    · rw [max_eq_left hba,
        max_eq_left ((div_le_div_iff_of_pos_right hd).2 hba)]
  have hden0 : (0 : ℚ) < denominator precision := by
    exact_mod_cast denominator_pos precision
  have hden : (0 : ℚ) < denominator precision ^ 2 := sq_pos_of_pos hden0
  rw [productLower, productUpper]
  simp only [Int.cast_min, Int.cast_max, Int.cast_mul]
  rw [min_div _ _ _ hden, min_div _ _ _ hden, min_div _ _ _ hden]
  rw [max_div _ _ _ hden, max_div _ _ _ hden, max_div _ _ _ hden]
  simpa only [RationalInterval.mul, interpret, value, Int.cast_mul,
    div_mul_div_comm, pow_two] using h'

/-- Dyadic interval multiplication preserves rational membership. -/
theorem mul_contains {I J : DyadicInterval precision} {x y : ℚ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.mul J).Contains (x * y) := by
  let scale := denominator precision
  have hscale : (0 : ℤ) < scale := denominator_pos precision
  have hproduct := exactProduct_contains hx hy
  constructor
  · change ((productLower I J / scale : ℤ) : ℚ) / scale ≤ x * y
    have hround := floorDiv_le (productLower I J) scale hscale
    have hround' := div_le_div_of_nonneg_right hround
      (by exact_mod_cast hscale.le : (0 : ℚ) ≤ scale)
    have hround'' :
        ((productLower I J / scale : ℤ) : ℚ) / scale ≤
          (productLower I J : ℚ) / scale ^ 2 := by
      simpa only [div_div, pow_two] using hround'
    exact hround''.trans hproduct.1
  · change x * y ≤ (-((-productUpper I J) / scale) : ℤ) / scale
    have hround := le_ceilDiv (productUpper I J) scale hscale
    have hround' := div_le_div_of_nonneg_right hround
      (by exact_mod_cast hscale.le : (0 : ℚ) ≤ scale)
    have hround'' :
        (productUpper I J : ℚ) / scale ^ 2 ≤
          (-((-productUpper I J) / scale) : ℤ) / scale := by
      simpa only [div_div, pow_two] using hround'
    exact hproduct.2.trans hround''

/-- Check that every rational in a dyadic interval is nonnegative. -/
def lowerNonnegative (I : DyadicInterval precision) : Bool :=
  decide (0 ≤ I.lower)

/-- A successful lower-endpoint check proves nonnegativity of every contained rational. -/
theorem nonnegative_of_lowerNonnegative {I : DyadicInterval precision} {q : ℚ}
    (hcheck : I.lowerNonnegative = true) (hq : I.Contains q) : 0 ≤ q := by
  simp only [lowerNonnegative, decide_eq_true_eq] at hcheck
  have hden : (0 : ℚ) ≤ denominator precision := by
    exact_mod_cast (denominator_pos precision).le
  have hlower : 0 ≤ value precision I.lower :=
    div_nonneg (by exact_mod_cast hcheck) hden
  exact hlower.trans hq.1

/-- Check that every rational in a dyadic interval is nonpositive. -/
def upperNonpositive (I : DyadicInterval precision) : Bool :=
  decide (I.upper ≤ 0)

/-- A successful upper-endpoint check proves nonpositivity of every contained rational. -/
theorem nonpositive_of_upperNonpositive {I : DyadicInterval precision} {q : ℚ}
    (hcheck : I.upperNonpositive = true) (hq : I.Contains q) : q ≤ 0 := by
  simp only [upperNonpositive, decide_eq_true_eq] at hcheck
  have hden : (0 : ℚ) ≤ denominator precision := by
    exact_mod_cast (denominator_pos precision).le
  have hupper : value precision I.upper ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hcheck) hden
  exact hq.2.trans hupper

end DyadicInterval

end Bescovitch
