/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.IntervalPolynomial
public import Bescovitch.Certificates.RadicalBernstein

/-!
# Bernstein certificates computed with interval coefficients

This file converts a coefficientwise interval enclosure from the power basis to the fixed
`12 × 12 × 4` Bernstein basis. It checks adaptive dyadic subdivisions using rational
interval endpoints, while its soundness theorem applies to the original exact polynomial.
-/

@[expose] public section

noncomputable section

open scoped BigOperators unitInterval

namespace Bescovitch

namespace RationalInterval

/-- Add a finite family of intervals in increasing `Fin` order. -/
def finSum : (N : ℕ) → (Fin N → RationalInterval) → RationalInterval
  | 0, _ => singleton 0
  | k + 1, f => (f 0).add (finSum k fun i => f i.succ)

/-- An interval finite sum contains the corresponding real finite sum. -/
theorem finSum_contains {N : ℕ} (intervals : Fin N → RationalInterval)
    (values : Fin N → ℝ) (h : ∀ i, (intervals i).Contains (values i)) :
    (finSum N intervals).Contains (∑ i, values i) := by
  induction N with
  | zero => simpa [finSum] using singleton_contains 0
  | succ N ih =>
      rw [Fin.sum_univ_succ]
      exact add_contains (h 0) (ih (fun i => intervals i.succ) (fun i => values i.succ)
        (fun i => h i.succ))

end RationalInterval

/-- Convert one interval power coefficient vector to the Bernstein basis. -/
def intervalPowerToBernstein (degree : ℕ)
    (a : Fin (degree + 1) → RationalInterval) (i : Fin (degree + 1)) : RationalInterval :=
  RationalInterval.finSum (degree + 1) fun j => if (j : ℕ) ≤ i then
    (a j).mul (.singleton (Nat.choose (i : ℕ) (j : ℕ) / Nat.choose degree (j : ℕ)))
  else .singleton 0

/-- Interval power-to-Bernstein conversion contains the exact real conversion. -/
theorem intervalPowerToBernstein_contains {degree : ℕ}
    {intervals : Fin (degree + 1) → RationalInterval}
    {values : Fin (degree + 1) → ℝ} (h : ∀ i, (intervals i).Contains (values i))
    (i : Fin (degree + 1)) :
    (intervalPowerToBernstein degree intervals i).Contains (powerToBernstein degree values i) := by
  rw [intervalPowerToBernstein, powerToBernstein]
  apply RationalInterval.finSum_contains
  intro j
  split_ifs with hj
  · apply RationalInterval.mul_contains (h j)
    simpa only [Rat.cast_div, Rat.cast_natCast] using
      RationalInterval.singleton_contains
        (Nat.choose (i : ℕ) (j : ℕ) / Nat.choose degree (j : ℕ) : ℚ)
  · simpa using RationalInterval.singleton_contains (0 : ℚ)

/-- Convert all coordinates of a `12 × 12 × 4` interval power tensor. -/
def intervalTensorPowerToBernstein
    (a : Fin 13 → Fin 13 → Fin 5 → RationalInterval)
    (i j : Fin 13) (k : Fin 5) : RationalInterval :=
  intervalPowerToBernstein 4
    (fun k' => intervalPowerToBernstein 12
      (fun j' => intervalPowerToBernstein 12 (fun i' => a i' j' k') i) j) k

/-- Interval tensor conversion contains the exact real tensor conversion. -/
theorem intervalTensorPowerToBernstein_contains
    {intervals : Fin 13 → Fin 13 → Fin 5 → RationalInterval}
    {values : Fin 13 → Fin 13 → Fin 5 → ℝ}
    (h : ∀ i j k, (intervals i j k).Contains (values i j k))
    (i j : Fin 13) (k : Fin 5) :
    (intervalTensorPowerToBernstein intervals i j k).Contains
      (tensorPowerToBernstein values i j k) := by
  apply intervalPowerToBernstein_contains
  intro k'
  apply intervalPowerToBernstein_contains
  intro j'
  apply intervalPowerToBernstein_contains
  intro i'
  exact h i' j' k'

/-- The interval Bernstein tensor of a dense interval polynomial. -/
def IntervalTrivariate.bernsteinCoefficients (p : IntervalTrivariate) :
    Fin 13 → Fin 13 → Fin 5 → RationalInterval :=
  intervalTensorPowerToBernstein fun i j k => p.coefficient i j k

/-- Interval Bernstein coefficients contain the exact evaluated Bernstein coefficients. -/
theorem IntervalTrivariate.bernsteinCoefficients_contains {n : ℕ}
    {P : IntervalTrivariate} {p : RadicalTrivariate n} {input : Fin n → ℝ}
    (h : P.Contains input p) (i j : Fin 13) (k : Fin 5) :
    (P.bernsteinCoefficients i j k).Contains ((p.bernsteinCoefficients i j k).eval input) := by
  rw [IntervalTrivariate.bernsteinCoefficients, RadicalTrivariate.bernsteinCoefficients,
    eval_radicalTensorPowerToBernstein]
  exact intervalTensorPowerToBernstein_contains
    (fun i j k => IntervalTrivariate.coefficient_contains h i j k) i j k

/-- Left-half interval de Casteljau coefficients in degree twelve. -/
def intervalBernsteinLeftTwelve (a : Fin 13 → RationalInterval)
    (i : Fin 13) : RationalInterval :=
  RationalInterval.finSum 13 fun j => if (j : ℕ) ≤ i then
    (a j).mul (.singleton (Nat.choose (i : ℕ) (j : ℕ) / 2 ^ (i : ℕ)))
  else .singleton 0

/-- Right-half interval de Casteljau coefficients in degree twelve. -/
def intervalBernsteinRightTwelve (a : Fin 13 → RationalInterval)
    (i : Fin 13) : RationalInterval :=
  RationalInterval.finSum 13 fun j => if h : (j : ℕ) ≤ 12 - (i : ℕ) then
    (a ⟨(i : ℕ) + j, by omega⟩).mul
      (.singleton (Nat.choose (12 - (i : ℕ)) (j : ℕ) / 2 ^ (12 - (i : ℕ))))
  else .singleton 0

/-- Left-half interval de Casteljau coefficients in degree four. -/
def intervalBernsteinLeftFour (a : Fin 5 → RationalInterval)
    (i : Fin 5) : RationalInterval :=
  RationalInterval.finSum 5 fun j => if (j : ℕ) ≤ i then
    (a j).mul (.singleton (Nat.choose (i : ℕ) (j : ℕ) / 2 ^ (i : ℕ)))
  else .singleton 0

/-- Right-half interval de Casteljau coefficients in degree four. -/
def intervalBernsteinRightFour (a : Fin 5 → RationalInterval)
    (i : Fin 5) : RationalInterval :=
  RationalInterval.finSum 5 fun j => if h : (j : ℕ) ≤ 4 - (i : ℕ) then
    (a ⟨(i : ℕ) + j, by omega⟩).mul
      (.singleton (Nat.choose (4 - (i : ℕ)) (j : ℕ) / 2 ^ (4 - (i : ℕ))))
  else .singleton 0

private theorem intervalBernsteinLeftTwelve_contains
    {intervals : Fin 13 → RationalInterval} {values : Fin 13 → ℝ}
    (h : ∀ i, (intervals i).Contains (values i)) (i : Fin 13) :
    (intervalBernsteinLeftTwelve intervals i).Contains (bernsteinLeftTwelve values i) := by
  rw [intervalBernsteinLeftTwelve, bernsteinLeftTwelve]
  apply RationalInterval.finSum_contains
  intro j
  split_ifs with hj
  · apply RationalInterval.mul_contains (h j)
    simpa [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow] using
      RationalInterval.singleton_contains
        (Nat.choose (i : ℕ) (j : ℕ) / 2 ^ (i : ℕ) : ℚ)
  · simpa using RationalInterval.singleton_contains (0 : ℚ)

private theorem intervalBernsteinRightTwelve_contains
    {intervals : Fin 13 → RationalInterval} {values : Fin 13 → ℝ}
    (h : ∀ i, (intervals i).Contains (values i)) (i : Fin 13) :
    (intervalBernsteinRightTwelve intervals i).Contains (bernsteinRightTwelve values i) := by
  rw [intervalBernsteinRightTwelve, bernsteinRightTwelve]
  apply RationalInterval.finSum_contains
  intro j
  split_ifs with hj
  · apply RationalInterval.mul_contains (h ⟨(i : ℕ) + j, by omega⟩)
    simpa [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow] using
      RationalInterval.singleton_contains
        (Nat.choose (12 - (i : ℕ)) (j : ℕ) / 2 ^ (12 - (i : ℕ)) : ℚ)
  · simpa using RationalInterval.singleton_contains (0 : ℚ)

private theorem intervalBernsteinLeftFour_contains
    {intervals : Fin 5 → RationalInterval} {values : Fin 5 → ℝ}
    (h : ∀ i, (intervals i).Contains (values i)) (i : Fin 5) :
    (intervalBernsteinLeftFour intervals i).Contains (bernsteinLeftFour values i) := by
  rw [intervalBernsteinLeftFour, bernsteinLeftFour]
  apply RationalInterval.finSum_contains
  intro j
  split_ifs with hj
  · apply RationalInterval.mul_contains (h j)
    simpa [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow] using
      RationalInterval.singleton_contains
        (Nat.choose (i : ℕ) (j : ℕ) / 2 ^ (i : ℕ) : ℚ)
  · simpa using RationalInterval.singleton_contains (0 : ℚ)

private theorem intervalBernsteinRightFour_contains
    {intervals : Fin 5 → RationalInterval} {values : Fin 5 → ℝ}
    (h : ∀ i, (intervals i).Contains (values i)) (i : Fin 5) :
    (intervalBernsteinRightFour intervals i).Contains (bernsteinRightFour values i) := by
  rw [intervalBernsteinRightFour, bernsteinRightFour]
  apply RationalInterval.finSum_contains
  intro j
  split_ifs with hj
  · apply RationalInterval.mul_contains (h ⟨(i : ℕ) + j, by omega⟩)
    simpa [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow] using
      RationalInterval.singleton_contains
        (Nat.choose (4 - (i : ℕ)) (j : ℕ) / 2 ^ (4 - (i : ℕ)) : ℚ)
  · simpa using RationalInterval.singleton_contains (0 : ℚ)

/-- Split an interval tensor along the left half of the first coordinate. -/
def intervalSplitFirstLeft
    (a : Fin 13 → Fin 13 → Fin 5 → RationalInterval) :=
  fun i j k => intervalBernsteinLeftTwelve (fun h => a h j k) i

/-- Split an interval tensor along the right half of the first coordinate. -/
def intervalSplitFirstRight
    (a : Fin 13 → Fin 13 → Fin 5 → RationalInterval) :=
  fun i j k => intervalBernsteinRightTwelve (fun h => a h j k) i

/-- Split an interval tensor along the left half of the second coordinate. -/
def intervalSplitSecondLeft
    (a : Fin 13 → Fin 13 → Fin 5 → RationalInterval) :=
  fun i j k => intervalBernsteinLeftTwelve (fun h => a i h k) j

/-- Split an interval tensor along the right half of the second coordinate. -/
def intervalSplitSecondRight
    (a : Fin 13 → Fin 13 → Fin 5 → RationalInterval) :=
  fun i j k => intervalBernsteinRightTwelve (fun h => a i h k) j

/-- Split an interval tensor along the left half of the third coordinate. -/
def intervalSplitThirdLeft
    (a : Fin 13 → Fin 13 → Fin 5 → RationalInterval) :=
  fun i j k => intervalBernsteinLeftFour (fun h => a i j h) k

/-- Split an interval tensor along the right half of the third coordinate. -/
def intervalSplitThirdRight
    (a : Fin 13 → Fin 13 → Fin 5 → RationalInterval) :=
  fun i j k => intervalBernsteinRightFour (fun h => a i j h) k

private noncomputable def splitFirstLeft
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :=
  fun i j k => bernsteinLeftTwelve (fun h => a h j k) i

private noncomputable def splitFirstRight
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :=
  fun i j k => bernsteinRightTwelve (fun h => a h j k) i

private noncomputable def splitSecondLeft
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :=
  fun i j k => bernsteinLeftTwelve (fun h => a i h k) j

private noncomputable def splitSecondRight
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :=
  fun i j k => bernsteinRightTwelve (fun h => a i h k) j

private noncomputable def splitThirdLeft
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :=
  fun i j k => bernsteinLeftFour (fun h => a i j h) k

private noncomputable def splitThirdRight
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :=
  fun i j k => bernsteinRightFour (fun h => a i j h) k

private theorem intervalSplitFirstLeft_contains
    {intervals : Fin 13 → Fin 13 → Fin 5 → RationalInterval}
    {values : Fin 13 → Fin 13 → Fin 5 → ℝ}
    (h : ∀ i j k, (intervals i j k).Contains (values i j k)) :
    ∀ i j k, (intervalSplitFirstLeft intervals i j k).Contains (splitFirstLeft values i j k) :=
  fun i j k => intervalBernsteinLeftTwelve_contains (fun h' => h h' j k) i

private theorem intervalSplitFirstRight_contains
    {intervals : Fin 13 → Fin 13 → Fin 5 → RationalInterval}
    {values : Fin 13 → Fin 13 → Fin 5 → ℝ}
    (h : ∀ i j k, (intervals i j k).Contains (values i j k)) :
    ∀ i j k, (intervalSplitFirstRight intervals i j k).Contains
      (splitFirstRight values i j k) :=
  fun i j k => intervalBernsteinRightTwelve_contains (fun h' => h h' j k) i

private theorem intervalSplitSecondLeft_contains
    {intervals : Fin 13 → Fin 13 → Fin 5 → RationalInterval}
    {values : Fin 13 → Fin 13 → Fin 5 → ℝ}
    (h : ∀ i j k, (intervals i j k).Contains (values i j k)) :
    ∀ i j k, (intervalSplitSecondLeft intervals i j k).Contains
      (splitSecondLeft values i j k) :=
  fun i j k => intervalBernsteinLeftTwelve_contains (fun h' => h i h' k) j

private theorem intervalSplitSecondRight_contains
    {intervals : Fin 13 → Fin 13 → Fin 5 → RationalInterval}
    {values : Fin 13 → Fin 13 → Fin 5 → ℝ}
    (h : ∀ i j k, (intervals i j k).Contains (values i j k)) :
    ∀ i j k, (intervalSplitSecondRight intervals i j k).Contains
      (splitSecondRight values i j k) :=
  fun i j k => intervalBernsteinRightTwelve_contains (fun h' => h i h' k) j

private theorem intervalSplitThirdLeft_contains
    {intervals : Fin 13 → Fin 13 → Fin 5 → RationalInterval}
    {values : Fin 13 → Fin 13 → Fin 5 → ℝ}
    (h : ∀ i j k, (intervals i j k).Contains (values i j k)) :
    ∀ i j k, (intervalSplitThirdLeft intervals i j k).Contains
      (splitThirdLeft values i j k) :=
  fun i j k => intervalBernsteinLeftFour_contains (fun h' => h i j h') k

private theorem intervalSplitThirdRight_contains
    {intervals : Fin 13 → Fin 13 → Fin 5 → RationalInterval}
    {values : Fin 13 → Fin 13 → Fin 5 → ℝ}
    (h : ∀ i j k, (intervals i j k).Contains (values i j k)) :
    ∀ i j k, (intervalSplitThirdRight intervals i j k).Contains
      (splitThirdRight values i j k) :=
  fun i j k => intervalBernsteinRightFour_contains (fun h' => h i j h') k

private theorem tensorBernstein_first_coordinate
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (chart : I → I)
    (convert : (Fin 13 → ℝ) → Fin 13 → ℝ)
    (hconvert : ∀ (coefficients : Fin 13 → ℝ) (x : I),
      (∑ i, coefficients i * bernstein 12 i (chart x)) =
        ∑ i, convert coefficients i * bernstein 12 i x)
    (x y z : I) :
    tensorBernstein a (chart x) y z =
      tensorBernstein (fun i j k => convert (fun h => a h j k) i) x y z := by
  unfold tensorBernstein
  calc
    _ = ∑ j, ∑ k, (∑ i, a i j k * bernstein 12 i (chart x)) *
        bernstein 12 j y * bernstein 4 k z := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ j, ∑ k, (∑ i, convert (fun h => a h j k) i * bernstein 12 i x) *
        bernstein 12 j y * bernstein 4 k z := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [hconvert]
    _ = ∑ j, ∑ i, ∑ k, convert (fun h => a h j k) i * bernstein 12 i x *
        bernstein 12 j y * bernstein 4 k z := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = _ := by rw [Finset.sum_comm]

private theorem tensorBernstein_second_coordinate
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (chart : I → I)
    (convert : (Fin 13 → ℝ) → Fin 13 → ℝ)
    (hconvert : ∀ (coefficients : Fin 13 → ℝ) (y : I),
      (∑ j, coefficients j * bernstein 12 j (chart y)) =
        ∑ j, convert coefficients j * bernstein 12 j y)
    (x y z : I) :
    tensorBernstein a x (chart y) z =
      tensorBernstein (fun i j k => convert (fun h => a i h k) j) x y z := by
  unfold tensorBernstein
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ k, (∑ j, a i j k * bernstein 12 j (chart y)) *
        bernstein 12 i x * bernstein 4 k z := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ k, (∑ j, convert (fun h => a i h k) j * bernstein 12 j y) *
        bernstein 12 i x * bernstein 4 k z := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hconvert]
    _ = ∑ j, ∑ k, convert (fun h => a i h k) j * bernstein 12 i x *
        bernstein 12 j y * bernstein 4 k z := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring

private theorem tensorBernstein_third_coordinate
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (chart : I → I)
    (convert : (Fin 5 → ℝ) → Fin 5 → ℝ)
    (hconvert : ∀ (coefficients : Fin 5 → ℝ) (z : I),
      (∑ k, coefficients k * bernstein 4 k (chart z)) =
        ∑ k, convert coefficients k * bernstein 4 k z)
    (x y z : I) :
    tensorBernstein a x y (chart z) =
      tensorBernstein (fun i j k => convert (fun h => a i j h) k) x y z := by
  unfold tensorBernstein
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (∑ k, a i j k * bernstein 12 i x * bernstein 12 j y *
      bernstein 4 k (chart z)) =
      (∑ k, a i j k * bernstein 4 k (chart z)) * bernstein 12 i x *
        bernstein 12 j y by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring]
  rw [hconvert]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem tensorBernstein_splitFirstLeft
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x y z : I) :
    tensorBernstein a (unitIntervalLeftHalf x) y z =
      tensorBernstein (splitFirstLeft a) x y z := by
  exact tensorBernstein_first_coordinate a unitIntervalLeftHalf bernsteinLeftTwelve
    bernstein_twelve_left_half x y z

private theorem tensorBernstein_splitFirstRight
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x y z : I) :
    tensorBernstein a (unitIntervalRightHalf x) y z =
      tensorBernstein (splitFirstRight a) x y z := by
  exact tensorBernstein_first_coordinate a unitIntervalRightHalf bernsteinRightTwelve
    bernstein_twelve_right_half x y z

private theorem tensorBernstein_splitSecondLeft
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x y z : I) :
    tensorBernstein a x (unitIntervalLeftHalf y) z =
      tensorBernstein (splitSecondLeft a) x y z := by
  exact tensorBernstein_second_coordinate a unitIntervalLeftHalf bernsteinLeftTwelve
    bernstein_twelve_left_half x y z

private theorem tensorBernstein_splitSecondRight
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x y z : I) :
    tensorBernstein a x (unitIntervalRightHalf y) z =
      tensorBernstein (splitSecondRight a) x y z := by
  exact tensorBernstein_second_coordinate a unitIntervalRightHalf bernsteinRightTwelve
    bernstein_twelve_right_half x y z

private theorem tensorBernstein_splitThirdLeft
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x y z : I) :
    tensorBernstein a x y (unitIntervalLeftHalf z) =
      tensorBernstein (splitThirdLeft a) x y z := by
  exact tensorBernstein_third_coordinate a unitIntervalLeftHalf bernsteinLeftFour
    bernstein_four_left_half x y z

private theorem tensorBernstein_splitThirdRight
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x y z : I) :
    tensorBernstein a x y (unitIntervalRightHalf z) =
      tensorBernstein (splitThirdRight a) x y z := by
  exact tensorBernstein_third_coordinate a unitIntervalRightHalf bernsteinRightFour
    bernstein_four_right_half x y z

/-- Check nonnegative lower endpoints in an interval Bernstein tensor. -/
def intervalTensorCoefficientsNonnegative
    (coefficients : Fin 13 → Fin 13 → Fin 5 → RationalInterval) : Bool :=
  decide (∀ i j k, 0 ≤ (coefficients i j k).lower)

/-- Check every leaf after the prescribed interval de Casteljau subdivisions. -/
def intervalTensorSubdivisionCertifiesNonnegative :
    TensorSubdivision → (Fin 13 → Fin 13 → Fin 5 → RationalInterval) → Bool
  | .leaf, coefficients => intervalTensorCoefficientsNonnegative coefficients
  | .splitFirst left right, coefficients =>
      intervalTensorSubdivisionCertifiesNonnegative left
          (intervalSplitFirstLeft coefficients) &&
        intervalTensorSubdivisionCertifiesNonnegative right
          (intervalSplitFirstRight coefficients)
  | .splitSecond left right, coefficients =>
      intervalTensorSubdivisionCertifiesNonnegative left
          (intervalSplitSecondLeft coefficients) &&
        intervalTensorSubdivisionCertifiesNonnegative right
          (intervalSplitSecondRight coefficients)
  | .splitThird left right, coefficients =>
      intervalTensorSubdivisionCertifiesNonnegative left
          (intervalSplitThirdLeft coefficients) &&
        intervalTensorSubdivisionCertifiesNonnegative right
          (intervalSplitThirdRight coefficients)

/-- A successful interval subdivision certificate makes the enclosed tensor nonnegative. -/
theorem tensorSubdivision_nonneg_of_interval_certificate (tree : TensorSubdivision)
    (intervals : Fin 13 → Fin 13 → Fin 5 → RationalInterval)
    (values : Fin 13 → Fin 13 → Fin 5 → ℝ)
    (hcontains : ∀ i j k, (intervals i j k).Contains (values i j k))
    (hcertificate : intervalTensorSubdivisionCertifiesNonnegative tree intervals = true)
    (x y z : I) : 0 ≤ tensorBernstein values x y z := by
  induction tree generalizing intervals values x y z with
  | leaf =>
      change intervalTensorCoefficientsNonnegative intervals = true at hcertificate
      have hlower : ∀ i j k, 0 ≤ (intervals i j k).lower :=
        of_decide_eq_true hcertificate
      apply tensorBernstein_nonneg
      intro i j k
      have hzero : (0 : ℝ) ≤ (intervals i j k).lower := by
        exact_mod_cast hlower i j k
      exact hzero.trans (hcontains i j k).1
  | splitFirst left right ihLeft ihRight =>
      change (intervalTensorSubdivisionCertifiesNonnegative left
        (intervalSplitFirstLeft intervals) &&
        intervalTensorSubdivisionCertifiesNonnegative right
          (intervalSplitFirstRight intervals)) = true at hcertificate
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases exists_unitInterval_half_chart x with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · rw [tensorBernstein_splitFirstLeft]
        exact ihLeft (intervalSplitFirstLeft intervals) (splitFirstLeft values)
          (intervalSplitFirstLeft_contains hcontains) hparts.1 u y z
      · rw [tensorBernstein_splitFirstRight]
        exact ihRight (intervalSplitFirstRight intervals) (splitFirstRight values)
          (intervalSplitFirstRight_contains hcontains) hparts.2 u y z
  | splitSecond left right ihLeft ihRight =>
      change (intervalTensorSubdivisionCertifiesNonnegative left
        (intervalSplitSecondLeft intervals) &&
        intervalTensorSubdivisionCertifiesNonnegative right
          (intervalSplitSecondRight intervals)) = true at hcertificate
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases exists_unitInterval_half_chart y with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · rw [tensorBernstein_splitSecondLeft]
        exact ihLeft (intervalSplitSecondLeft intervals) (splitSecondLeft values)
          (intervalSplitSecondLeft_contains hcontains) hparts.1 x u z
      · rw [tensorBernstein_splitSecondRight]
        exact ihRight (intervalSplitSecondRight intervals) (splitSecondRight values)
          (intervalSplitSecondRight_contains hcontains) hparts.2 x u z
  | splitThird left right ihLeft ihRight =>
      change (intervalTensorSubdivisionCertifiesNonnegative left
        (intervalSplitThirdLeft intervals) &&
        intervalTensorSubdivisionCertifiesNonnegative right
          (intervalSplitThirdRight intervals)) = true at hcertificate
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases exists_unitInterval_half_chart z with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · rw [tensorBernstein_splitThirdLeft]
        exact ihLeft (intervalSplitThirdLeft intervals) (splitThirdLeft values)
          (intervalSplitThirdLeft_contains hcontains) hparts.1 x y u
      · rw [tensorBernstein_splitThirdRight]
        exact ihRight (intervalSplitThirdRight intervals) (splitThirdRight values)
          (intervalSplitThirdRight_contains hcontains) hparts.2 x y u

/-- A fitted exact polynomial enclosed coefficientwise by a successful interval certificate
is nonnegative on the unit cube. -/
theorem RadicalTrivariate.nonneg_of_interval_bernstein_certificate {n : ℕ}
    (p : RadicalTrivariate n) (hfits : p.Fits 12 12 4)
    (P : IntervalTrivariate) (input : Fin n → ℝ) (hcontains : P.Contains input p)
    (tree : TensorSubdivision)
    (hcertificate : intervalTensorSubdivisionCertifiesNonnegative tree
      P.bernsteinCoefficients = true)
    (x y z : I) : 0 ≤ p.eval input x y z := by
  rw [p.eval_eq_tensorBernstein hfits]
  exact tensorSubdivision_nonneg_of_interval_certificate tree P.bernsteinCoefficients
    (fun i j k => (p.bernsteinCoefficients i j k).eval input)
    (fun i j k => P.bernsteinCoefficients_contains hcontains i j k)
    hcertificate x y z

end Bescovitch
