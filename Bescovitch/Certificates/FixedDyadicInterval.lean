/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.DyadicInterval

/-!
# Fixed-width dyadic intervals

This module evaluates dyadic interval arithmetic with signed bit vectors. Every operation records
whether its result fits, so a successful computation has the semantics of the unbounded dyadic
operation without any assumption about the chosen bit width.
-/

@[expose] public section

namespace Bescovitch

/-- A guarded dyadic interval whose endpoint numerators use `width` signed bits. -/
structure FixedDyadicInterval (width precision : ℕ) where
  /-- Fixed-width numerator of the lower endpoint. -/
  lower : BitVec width
  /-- Fixed-width numerator of the upper endpoint. -/
  upper : BitVec width
  /-- Whether all operations used to construct the interval were exact and overflow-free. -/
  ok : Bool
  /-- A successful interval has its endpoints in signed order. -/
  ordered : ok = true → lower.sle upper = true
  deriving DecidableEq, Repr

namespace FixedDyadicInterval

variable {width precision : ℕ}

/-- Signed minimum of two fixed-width integers. -/
def signedMin (left right : BitVec width) : BitVec width :=
  if left.slt right then left else right

/-- Signed maximum of two fixed-width integers. -/
def signedMax (left right : BitVec width) : BitVec width :=
  if left.slt right then right else left

/-- Minimum of four candidate products. -/
def productLower (ll lu ul uu : BitVec width) : BitVec width :=
  signedMin (signedMin ll lu) (signedMin ul uu)

/-- Maximum of four candidate products. -/
def productUpper (ll lu ul uu : BitVec width) : BitVec width :=
  signedMax (signedMax ll lu) (signedMax ul uu)

/-- Sign-extend a fixed-width integer to the doubled product width. -/
def widen (value : BitVec width) : BitVec (width * 2) :=
  value.signExtend (width * 2)

/-- Multiply two signed integers at the doubled product width. -/
def wideProduct (left right : BitVec width) : BitVec (width * 2) :=
  widen left * widen right

/-- Check that doubled-width signed multiplication did not overflow. -/
def productSafe (left right : BitVec width) : Bool :=
  !(widen left).smulOverflow (widen right)

/-- Check that a doubled-width integer fits at the original width. -/
def fits (value : BitVec (width * 2)) : Bool :=
  decide ((value.setWidth width).signExtend (width * 2) = value)

/-- Truncate a doubled-width integer after a successful fit check. -/
def narrow (value : BitVec (width * 2)) : BitVec width :=
  value.setWidth width

/-- Convert an unbounded dyadic interval when both endpoints fit. -/
def fromDyadic (width : ℕ) (value : DyadicInterval precision) :
    FixedDyadicInterval width precision :=
  let lower := BitVec.ofInt width value.lower
  let upper := BitVec.ofInt width value.upper
  let ok := decide (lower.toInt = value.lower) &&
    decide (upper.toInt = value.upper) && lower.sle upper
  ⟨lower, upper, ok, by simp [ok]⟩

/-- Outward-round a rational to a guarded fixed-width dyadic interval. -/
def ofRat (width precision : ℕ) (q : ℚ) : FixedDyadicInterval width precision :=
  fromDyadic width (DyadicInterval.ofRat precision q)

/-- Add two integers at the doubled width. -/
def wideAdd (left right : BitVec width) : BitVec (width * 2) :=
  widen left + widen right

/-- Check every overflow and narrowing condition for interval addition. -/
def additionSafe (left right : FixedDyadicInterval width precision) : Bool :=
  left.ok && right.ok && !(widen left.lower).saddOverflow (widen right.lower) &&
    !(widen left.upper).saddOverflow (widen right.upper) &&
    fits (wideAdd left.lower right.lower) && fits (wideAdd left.upper right.upper)

/-- Guarded fixed-width interval addition. -/
def add (left right : FixedDyadicInterval width precision) :
    FixedDyadicInterval width precision :=
  let lower := narrow (wideAdd left.lower right.lower)
  let upper := narrow (wideAdd left.upper right.upper)
  let ok := additionSafe left right && lower.sle upper
  ⟨lower, upper, ok, by simp [ok]⟩

/-- Check the signed-minimum corner case for interval negation. -/
def negationSafe (value : FixedDyadicInterval width precision) : Bool :=
  value.ok && decide (value.lower ≠ BitVec.intMin width) &&
    decide (value.upper ≠ BitVec.intMin width)

/-- Guarded fixed-width interval negation. -/
def neg (value : FixedDyadicInterval width precision) : FixedDyadicInterval width precision :=
  let lower := -value.upper
  let upper := -value.lower
  let ok := negationSafe value && lower.sle upper
  ⟨lower, upper, ok, by simp [ok]⟩

/-- Check that a guarded interval is valid and has nonpositive upper endpoint. -/
def upperNonpositive (value : FixedDyadicInterval width precision) : Bool :=
  value.ok && value.upper.sle 0

/-- Minimum of the four doubled-width endpoint products. -/
def lowerWide (left right : FixedDyadicInterval width precision) :
    BitVec (width * 2) :=
  productLower (wideProduct left.lower right.lower) (wideProduct left.lower right.upper)
    (wideProduct left.upper right.lower) (wideProduct left.upper right.upper)

/-- Maximum of the four doubled-width endpoint products. -/
def upperWide (left right : FixedDyadicInterval width precision) :
    BitVec (width * 2) :=
  productUpper (wideProduct left.lower right.lower) (wideProduct left.lower right.upper)
    (wideProduct left.upper right.lower) (wideProduct left.upper right.upper)

/-- Downward-rounded lower product numerator. -/
def lowerRounded (left right : FixedDyadicInterval width precision) :
    BitVec (width * 2) :=
  (lowerWide left right).sshiftRight precision

/-- Upward-rounded upper product numerator. -/
def upperRounded (left right : FixedDyadicInterval width precision) :
    BitVec (width * 2) :=
  -((-(upperWide left right)).sshiftRight precision)

/-- Check every overflow and narrowing condition for interval multiplication. -/
def multiplicationSafe (left right : FixedDyadicInterval width precision) : Bool :=
  left.ok && right.ok &&
    productSafe left.lower right.lower && productSafe left.lower right.upper &&
    productSafe left.upper right.lower && productSafe left.upper right.upper &&
    decide (upperWide left right ≠ BitVec.intMin (width * 2)) &&
    decide ((-(upperWide left right)).sshiftRight precision ≠
      BitVec.intMin (width * 2)) &&
    fits (lowerRounded left right) && fits (upperRounded left right)

/-- Guarded, outward-rounded fixed-width interval multiplication. -/
def mul (left right : FixedDyadicInterval width precision) :
    FixedDyadicInterval width precision :=
  let lower := narrow (lowerRounded left right)
  let upper := narrow (upperRounded left right)
  let ok := multiplicationSafe left right && lower.sle upper
  ⟨lower, upper, ok, by simp [ok]⟩

private theorem toInt_signedMin (left right : BitVec width) :
    (signedMin left right).toInt = min left.toInt right.toInt := by
  simp only [signedMin]
  split
  · rename_i h
    rw [min_eq_left]
    exact le_of_lt ((BitVec.slt_iff_toInt_lt).mp h)
  · rename_i h
    rw [min_eq_right]
    exact le_of_not_gt (fun hlt ↦ h ((BitVec.slt_iff_toInt_lt).mpr hlt))

private theorem toInt_signedMax (left right : BitVec width) :
    (signedMax left right).toInt = max left.toInt right.toInt := by
  simp only [signedMax]
  split
  · rename_i h
    rw [max_eq_right]
    exact le_of_lt ((BitVec.slt_iff_toInt_lt).mp h)
  · rename_i h
    rw [max_eq_left]
    exact le_of_not_gt (fun hlt ↦ h ((BitVec.slt_iff_toInt_lt).mpr hlt))

private theorem toInt_productLower (ll lu ul uu : BitVec width) :
    (productLower ll lu ul uu).toInt =
      min (min ll.toInt lu.toInt) (min ul.toInt uu.toInt) := by
  simp [productLower, toInt_signedMin]

private theorem toInt_productUpper (ll lu ul uu : BitVec width) :
    (productUpper ll lu ul uu).toInt =
      max (max ll.toInt lu.toInt) (max ul.toInt uu.toInt) := by
  simp [productUpper, toInt_signedMax]

private theorem toInt_wideProduct_of_safe (left right : BitVec width)
    (safe : productSafe left right = true) :
    (wideProduct left right).toInt = left.toInt * right.toInt := by
  rw [wideProduct, BitVec.toInt_mul_of_not_smulOverflow]
  · have hleft := BitVec.toInt_signExtend_of_le
        (x := left) (v := width * 2) (by omega)
    have hright := BitVec.toInt_signExtend_of_le
        (x := right) (v := width * 2) (by omega)
    simp [widen, hleft, hright]
  · simpa [productSafe] using safe

private theorem toInt_wideAdd_of_safe (left right : BitVec width)
    (safe : ¬(widen left).saddOverflow (widen right) = true) :
    (wideAdd left right).toInt = left.toInt + right.toInt := by
  rw [wideAdd, BitVec.toInt_add_of_not_saddOverflow]
  · have hleft := BitVec.toInt_signExtend_of_le
        (x := left) (v := width * 2) (by omega)
    have hright := BitVec.toInt_signExtend_of_le
        (x := right) (v := width * 2) (by omega)
    simp only [widen, hleft, hright]
  · exact safe

private theorem toInt_narrow_of_fits (value : BitVec (width * 2))
    (hfits : fits value = true) : (narrow value).toInt = value.toInt := by
  have heq : (value.setWidth width).signExtend (width * 2) = value := by
    simpa [fits] using hfits
  have := congrArg BitVec.toInt heq
  have hwiden := BitVec.toInt_signExtend_of_le
    (x := value.setWidth width) (v := width * 2) (by omega)
  simpa [narrow, hwiden] using this

private theorem toInt_lowerWide_of_safe (left right : FixedDyadicInterval width precision)
    (hll : productSafe left.lower right.lower = true)
    (hlu : productSafe left.lower right.upper = true)
    (hul : productSafe left.upper right.lower = true)
    (huu : productSafe left.upper right.upper = true) :
    (lowerWide left right).toInt =
      min (min (left.lower.toInt * right.lower.toInt)
        (left.lower.toInt * right.upper.toInt))
      (min (left.upper.toInt * right.lower.toInt)
        (left.upper.toInt * right.upper.toInt)) := by
  rw [lowerWide, toInt_productLower]
  rw [toInt_wideProduct_of_safe _ _ hll, toInt_wideProduct_of_safe _ _ hlu]
  rw [toInt_wideProduct_of_safe _ _ hul, toInt_wideProduct_of_safe _ _ huu]

private theorem toInt_upperWide_of_safe (left right : FixedDyadicInterval width precision)
    (hll : productSafe left.lower right.lower = true)
    (hlu : productSafe left.lower right.upper = true)
    (hul : productSafe left.upper right.lower = true)
    (huu : productSafe left.upper right.upper = true) :
    (upperWide left right).toInt =
      max (max (left.lower.toInt * right.lower.toInt)
        (left.lower.toInt * right.upper.toInt))
      (max (left.upper.toInt * right.lower.toInt)
        (left.upper.toInt * right.upper.toInt)) := by
  rw [upperWide, toInt_productUpper]
  rw [toInt_wideProduct_of_safe _ _ hll, toInt_wideProduct_of_safe _ _ hlu]
  rw [toInt_wideProduct_of_safe _ _ hul, toInt_wideProduct_of_safe _ _ huu]

private theorem toInt_lowerRounded_of_safe
    (left right : FixedDyadicInterval width precision)
    (hll : productSafe left.lower right.lower = true)
    (hlu : productSafe left.lower right.upper = true)
    (hul : productSafe left.upper right.lower = true)
    (huu : productSafe left.upper right.upper = true) :
    (lowerRounded left right).toInt =
      min (min (left.lower.toInt * right.lower.toInt)
        (left.lower.toInt * right.upper.toInt))
      (min (left.upper.toInt * right.lower.toInt)
        (left.upper.toInt * right.upper.toInt)) / (2 : ℤ) ^ precision := by
  rw [lowerRounded, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  rw [toInt_lowerWide_of_safe left right hll hlu hul huu]
  norm_num only [Int.natCast_pow]

private theorem toInt_upperRounded_of_safe
    (left right : FixedDyadicInterval width precision)
    (hll : productSafe left.lower right.lower = true)
    (hlu : productSafe left.lower right.upper = true)
    (hul : productSafe left.upper right.lower = true)
    (huu : productSafe left.upper right.upper = true)
    (hupper : upperWide left right ≠ BitVec.intMin (width * 2))
    (hrounded : (-(upperWide left right)).sshiftRight precision ≠
      BitVec.intMin (width * 2)) :
    (upperRounded left right).toInt =
      -( -(max (max (left.lower.toInt * right.lower.toInt)
          (left.lower.toInt * right.upper.toInt))
        (max (left.upper.toInt * right.lower.toInt)
          (left.upper.toInt * right.upper.toInt))) / (2 : ℤ) ^ precision) := by
  rw [upperRounded, BitVec.toInt_neg_of_ne_intMin hrounded,
    BitVec.toInt_sshiftRight, BitVec.toInt_neg_of_ne_intMin hupper,
    Int.shiftRight_eq_div_pow]
  rw [toInt_upperWide_of_safe left right hll hlu hul huu]
  norm_num only [Int.natCast_pow]

/-- Exact agreement between a guarded interval and an unbounded dyadic interval. -/
def Represents (fixed : FixedDyadicInterval width precision)
    (exact : DyadicInterval precision) : Prop :=
  fixed.ok = true ∧ fixed.lower.toInt = exact.lower ∧ fixed.upper.toInt = exact.upper

private theorem fromDyadic_represents (exact : DyadicInterval precision)
    (hok : (fromDyadic width exact).ok = true) : Represents (fromDyadic width exact) exact := by
  simp only [Represents, fromDyadic, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  exact ⟨hok, hok.1.1, hok.1.2⟩

/-- A successful rational conversion represents the unbounded outward rounding. -/
theorem ofRat_represents (width precision : ℕ) (q : ℚ)
    (hok : (ofRat width precision q).ok = true) :
    Represents (ofRat width precision q) (DyadicInterval.ofRat precision q) := by
  exact fromDyadic_represents _ hok

/-- Successful guarded addition represents unbounded dyadic addition. -/
theorem add_represents {left right : FixedDyadicInterval width precision}
    {exactLeft exactRight : DyadicInterval precision} (hleft : Represents left exactLeft)
    (hright : Represents right exactRight) (hok : (add left right).ok = true) :
    Represents (add left right) (exactLeft.add exactRight) := by
  have hokParts := hok
  rw [add, Bool.and_eq_true] at hokParts
  have hsafe := hokParts.1
  simp only [additionSafe, Bool.and_eq_true] at hsafe
  rcases hsafe with ⟨⟨⟨⟨⟨_, _⟩, hlowerSafe⟩, hupperSafe⟩, hfitLower⟩, hfitUpper⟩
  refine ⟨hok, ?_, ?_⟩
  · rw [add, toInt_narrow_of_fits _ hfitLower,
      toInt_wideAdd_of_safe left.lower right.lower (by simpa using hlowerSafe)]
    simp only [DyadicInterval.add]
    rw [hleft.2.1, hright.2.1]
  · rw [add, toInt_narrow_of_fits _ hfitUpper,
      toInt_wideAdd_of_safe left.upper right.upper (by simpa using hupperSafe)]
    simp only [DyadicInterval.add]
    rw [hleft.2.2, hright.2.2]

/-- Successful guarded negation represents unbounded dyadic negation. -/
theorem neg_represents {value : FixedDyadicInterval width precision}
    {exact : DyadicInterval precision} (hvalue : Represents value exact)
    (hok : (neg value).ok = true) : Represents (neg value) exact.neg := by
  have hokParts := hok
  rw [neg, Bool.and_eq_true] at hokParts
  have hsafe := hokParts.1
  simp only [negationSafe, Bool.and_eq_true, decide_eq_true_eq] at hsafe
  rcases hsafe with ⟨⟨_, hlower⟩, hupper⟩
  refine ⟨hok, ?_, ?_⟩
  · rw [neg, BitVec.toInt_neg_of_ne_intMin hupper]
    simp only [DyadicInterval.neg]
    rw [hvalue.2.2]
  · rw [neg, BitVec.toInt_neg_of_ne_intMin hlower]
    simp only [DyadicInterval.neg]
    rw [hvalue.2.1]

/-- Successful guarded multiplication represents unbounded dyadic multiplication. -/
theorem mul_represents {left right : FixedDyadicInterval width precision}
    {exactLeft exactRight : DyadicInterval precision} (hleft : Represents left exactLeft)
    (hright : Represents right exactRight) (hok : (mul left right).ok = true) :
    Represents (mul left right) (exactLeft.mul exactRight) := by
  have hokParts := hok
  rw [mul, Bool.and_eq_true] at hokParts
  have hsafe := hokParts.1
  simp only [multiplicationSafe, Bool.and_eq_true, decide_eq_true_eq] at hsafe
  rcases hsafe with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hll⟩, hlu⟩, hul⟩, huu⟩, hupper⟩, hrounded⟩,
      hfitLower⟩, hfitUpper⟩
  refine ⟨hok, ?_, ?_⟩
  · rw [mul, toInt_narrow_of_fits _ hfitLower,
      toInt_lowerRounded_of_safe left right hll hlu hul huu]
    simp only [DyadicInterval.mul, DyadicInterval.denominator]
    rw [hleft.2.1, hleft.2.2, hright.2.1, hright.2.2]
  · rw [mul, toInt_narrow_of_fits _ hfitUpper,
      toInt_upperRounded_of_safe left right hll hlu hul huu hupper hrounded]
    simp only [DyadicInterval.mul, DyadicInterval.denominator]
    rw [hleft.2.1, hleft.2.2, hright.2.1, hright.2.2]

/-- A successful fixed-width sign check gives the corresponding unbounded sign check. -/
theorem upperNonpositive_of_represents {fixed : FixedDyadicInterval width precision}
    {exact : DyadicInterval precision} (hfixed : Represents fixed exact)
    (hcheck : upperNonpositive fixed = true) : exact.upperNonpositive = true := by
  simp only [upperNonpositive, Bool.and_eq_true] at hcheck
  simp only [DyadicInterval.upperNonpositive, decide_eq_true_eq]
  rw [← hfixed.2.2]
  simpa using (BitVec.sle_iff_toInt_le).mp hcheck.2

/-- Every rational represented by a successfully checked fixed interval is nonpositive. -/
theorem nonpositive_of_upperNonpositive {fixed : FixedDyadicInterval width precision}
    {exact : DyadicInterval precision} {q : ℚ} (hfixed : Represents fixed exact)
    (hcheck : upperNonpositive fixed = true) (hq : exact.Contains q) : q ≤ 0 := by
  exact DyadicInterval.nonpositive_of_upperNonpositive
    (upperNonpositive_of_represents hfixed hcheck) hq

end FixedDyadicInterval

end Bescovitch
