/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.IntervalBernstein

/-!
# Scaled-integer tensor Bernstein certificates

This file verifies the fixed `12 × 12 × 4` tensor certificates used for ordinary weighted-self
radius bins. Power-to-Bernstein conversion and dyadic de Casteljau subdivision are scaled by
positive integers, so every certified sign is decided using integer arithmetic.
-/

@[expose] public section

noncomputable section

open scoped BigOperators unitInterval

namespace Bescovitch.IntegerTensorBernstein

/-- An integer coefficient tensor in the fixed weighted-self degree box. -/
abbrev Tensor := Fin 13 → Fin 13 → Fin 5 → ℤ

/-- A recursive finite sum whose closed inputs reduce efficiently in the kernel. -/
def finSum : (n : ℕ) → (Fin n → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, f => f 0 + finSum n (fun i ↦ f i.succ)

/-- First-coordinate power-to-Bernstein conversion, scaled by `lcm(C(12,i)) = 27720`. -/
def convertFirst (a : Tensor) (i j : Fin 13) (k : Fin 5) : ℤ :=
  finSum 13 fun h ↦ if (h : ℕ) ≤ i then
    a h j k * Nat.choose i h * (27720 / Nat.choose 12 h)
  else 0

/-- Second-coordinate power-to-Bernstein conversion with the same positive scale. -/
def convertSecond (a : Tensor) (i j : Fin 13) (k : Fin 5) : ℤ :=
  finSum 13 fun h ↦ if (h : ℕ) ≤ j then
    a i h k * Nat.choose j h * (27720 / Nat.choose 12 h)
  else 0

/-- Third-coordinate power-to-Bernstein conversion, scaled by `lcm(C(4,i)) = 12`. -/
def convertThird (a : Tensor) (i j : Fin 13) (k : Fin 5) : ℤ :=
  finSum 5 fun h ↦ if (h : ℕ) ≤ k then
    a i j h * Nat.choose k h * (12 / Nat.choose 4 h)
  else 0

/-- Convert a power tensor to a uniformly positively scaled Bernstein tensor. -/
def convertPowerTensor (a : Tensor) : Tensor :=
  convertThird (convertSecond (convertFirst a))

/-- Scaled left-half de Casteljau restriction in degree twelve. -/
def leftTwelve (a : Fin 13 → ℤ) (i : Fin 13) : ℤ :=
  finSum 13 fun j ↦ if (j : ℕ) ≤ i then
    a j * Nat.choose i j * 2 ^ (12 - (i : ℕ))
  else 0

/-- Scaled right-half de Casteljau restriction in degree twelve. -/
def rightTwelve (a : Fin 13 → ℤ) (i : Fin 13) : ℤ :=
  finSum 13 fun j ↦ if h : (j : ℕ) ≤ 12 - (i : ℕ) then
    a ⟨(i : ℕ) + j, by omega⟩ * Nat.choose (12 - (i : ℕ)) j * 2 ^ (i : ℕ)
  else 0

/-- Scaled left-half de Casteljau restriction in degree four. -/
def leftFour (a : Fin 5 → ℤ) (i : Fin 5) : ℤ :=
  finSum 5 fun j ↦ if (j : ℕ) ≤ i then
    a j * Nat.choose i j * 2 ^ (4 - (i : ℕ))
  else 0

/-- Scaled right-half de Casteljau restriction in degree four. -/
def rightFour (a : Fin 5 → ℤ) (i : Fin 5) : ℤ :=
  finSum 5 fun j ↦ if h : (j : ℕ) ≤ 4 - (i : ℕ) then
    a ⟨(i : ℕ) + j, by omega⟩ * Nat.choose (4 - (i : ℕ)) j * 2 ^ (i : ℕ)
  else 0

/-- Restrict the first coordinate to its left dyadic half. -/
def splitFirstLeft (a : Tensor) : Tensor :=
  fun i j k ↦ leftTwelve (fun h ↦ a h j k) i

/-- Restrict the first coordinate to its right dyadic half. -/
def splitFirstRight (a : Tensor) : Tensor :=
  fun i j k ↦ rightTwelve (fun h ↦ a h j k) i

/-- Restrict the second coordinate to its left dyadic half. -/
def splitSecondLeft (a : Tensor) : Tensor :=
  fun i j k ↦ leftTwelve (fun h ↦ a i h k) j

/-- Restrict the second coordinate to its right dyadic half. -/
def splitSecondRight (a : Tensor) : Tensor :=
  fun i j k ↦ rightTwelve (fun h ↦ a i h k) j

/-- Restrict the third coordinate to its left dyadic half. -/
def splitThirdLeft (a : Tensor) : Tensor :=
  fun i j k ↦ leftFour (fun h ↦ a i j h) k

/-- Restrict the third coordinate to its right dyadic half. -/
def splitThirdRight (a : Tensor) : Tensor :=
  fun i j k ↦ rightFour (fun h ↦ a i j h) k

/-- Every coefficient in one fixed first-coordinate row is nonnegative. -/
def rowNonnegative (a : Tensor) (i : Fin 13) : Bool :=
  decide (∀ j k, 0 ≤ a i j k)

/-- A successful row check proves the corresponding integer inequalities. -/
theorem rowNonnegative_sound {a : Tensor} {i : Fin 13}
    (h : rowNonnegative a i = true) : ∀ j k, 0 ≤ a i j k :=
  of_decide_eq_true h

/-- Every leaf of a subdivision tree has nonnegative scaled integer coefficients. -/
def SubdivisionNonnegative : TensorSubdivision → Tensor → Prop
  | .leaf, a => ∀ i j k, 0 ≤ a i j k
  | .splitFirst left right, a =>
      SubdivisionNonnegative left (splitFirstLeft a) ∧
        SubdivisionNonnegative right (splitFirstRight a)
  | .splitSecond left right, a =>
      SubdivisionNonnegative left (splitSecondLeft a) ∧
        SubdivisionNonnegative right (splitSecondRight a)
  | .splitThird left right, a =>
      SubdivisionNonnegative left (splitThirdLeft a) ∧
        SubdivisionNonnegative right (splitThirdRight a)

private theorem finSum_cast (n : ℕ) (f : Fin n → ℤ) :
    ((finSum n f : ℤ) : ℝ) = ∑ i, (f i : ℝ) := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [finSum, Int.cast_add]
      rw [ih]

private theorem leftTwelve_cast (a : Fin 13 → ℤ) (i : Fin 13) :
    ((leftTwelve a i : ℤ) : ℝ) =
      2 ^ 12 * Bescovitch.bernsteinLeftTwelve (fun j ↦ (a j : ℝ)) i := by
  rw [leftTwelve, finSum_cast]
  unfold Bescovitch.bernsteinLeftTwelve
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · norm_num only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    have hi : (i : ℕ) ≤ 12 := Nat.le_of_lt_succ i.isLt
    have hpow : (4096 : ℝ) = 2 ^ (12 - (i : ℕ)) * 2 ^ (i : ℕ) := by
      rw [← pow_add, Nat.sub_add_cancel hi]
      norm_num
    rw [hpow]
    field_simp
  · simp

private theorem rightTwelve_cast (a : Fin 13 → ℤ) (i : Fin 13) :
    ((rightTwelve a i : ℤ) : ℝ) =
      2 ^ 12 * Bescovitch.bernsteinRightTwelve (fun j ↦ (a j : ℝ)) i := by
  rw [rightTwelve, finSum_cast]
  unfold Bescovitch.bernsteinRightTwelve
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · norm_num only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    have hi : (i : ℕ) ≤ 12 := Nat.le_of_lt_succ i.isLt
    have hpow : (4096 : ℝ) = 2 ^ (i : ℕ) * 2 ^ (12 - (i : ℕ)) := by
      rw [← pow_add, Nat.add_sub_of_le hi]
      norm_num
    rw [hpow]
    field_simp
  · simp

private theorem leftFour_cast (a : Fin 5 → ℤ) (i : Fin 5) :
    ((leftFour a i : ℤ) : ℝ) =
      2 ^ 4 * Bescovitch.bernsteinLeftFour (fun j ↦ (a j : ℝ)) i := by
  rw [leftFour, finSum_cast]
  unfold Bescovitch.bernsteinLeftFour
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · norm_num only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    have hi : (i : ℕ) ≤ 4 := Nat.le_of_lt_succ i.isLt
    have hpow : (16 : ℝ) = 2 ^ (4 - (i : ℕ)) * 2 ^ (i : ℕ) := by
      rw [← pow_add, Nat.sub_add_cancel hi]
      norm_num
    rw [hpow]
    field_simp
  · simp

private theorem rightFour_cast (a : Fin 5 → ℤ) (i : Fin 5) :
    ((rightFour a i : ℤ) : ℝ) =
      2 ^ 4 * Bescovitch.bernsteinRightFour (fun j ↦ (a j : ℝ)) i := by
  rw [rightFour, finSum_cast]
  unfold Bescovitch.bernsteinRightFour
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · norm_num only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    have hi : (i : ℕ) ≤ 4 := Nat.le_of_lt_succ i.isLt
    have hpow : (16 : ℝ) = 2 ^ (i : ℕ) * 2 ^ (4 - (i : ℕ)) := by
      rw [← pow_add, Nat.add_sub_of_le hi]
      norm_num
    rw [hpow]
    field_simp
  · simp

private theorem splitFirstLeft_cast (a : Tensor) (i j k) :
    ((splitFirstLeft a i j k : ℤ) : ℝ) =
      2 ^ 12 * Bescovitch.splitFirstLeft (fun i j k ↦ (a i j k : ℝ)) i j k :=
  leftTwelve_cast (fun h ↦ a h j k) i

private theorem splitFirstRight_cast (a : Tensor) (i j k) :
    ((splitFirstRight a i j k : ℤ) : ℝ) =
      2 ^ 12 * Bescovitch.splitFirstRight (fun i j k ↦ (a i j k : ℝ)) i j k :=
  rightTwelve_cast (fun h ↦ a h j k) i

private theorem splitSecondLeft_cast (a : Tensor) (i j k) :
    ((splitSecondLeft a i j k : ℤ) : ℝ) =
      2 ^ 12 * Bescovitch.splitSecondLeft (fun i j k ↦ (a i j k : ℝ)) i j k :=
  leftTwelve_cast (fun h ↦ a i h k) j

private theorem splitSecondRight_cast (a : Tensor) (i j k) :
    ((splitSecondRight a i j k : ℤ) : ℝ) =
      2 ^ 12 * Bescovitch.splitSecondRight (fun i j k ↦ (a i j k : ℝ)) i j k :=
  rightTwelve_cast (fun h ↦ a i h k) j

private theorem splitThirdLeft_cast (a : Tensor) (i j k) :
    ((splitThirdLeft a i j k : ℤ) : ℝ) =
      2 ^ 4 * Bescovitch.splitThirdLeft (fun i j k ↦ (a i j k : ℝ)) i j k :=
  leftFour_cast (fun h ↦ a i j h) k

private theorem splitThirdRight_cast (a : Tensor) (i j k) :
    ((splitThirdRight a i j k : ℤ) : ℝ) =
      2 ^ 4 * Bescovitch.splitThirdRight (fun i j k ↦ (a i j k : ℝ)) i j k :=
  rightFour_cast (fun h ↦ a i j h) k

private theorem tensorBernstein_scale (c : ℝ) (a : Fin 13 → Fin 13 → Fin 5 → ℝ)
    (x y z : I) :
    tensorBernstein (fun i j k ↦ c * a i j k) x y z =
      c * tensorBernstein a x y z := by
  unfold tensorBernstein
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem tensorBernstein_splitFirstLeft (a : Tensor) (x y z : I) :
    tensorBernstein (fun i j k ↦ ((splitFirstLeft a i j k : ℤ) : ℝ)) x y z =
      2 ^ 12 * tensorBernstein (fun i j k ↦ (a i j k : ℝ))
        (unitIntervalLeftHalf x) y z := by
  rw [show (fun i j k ↦ ((splitFirstLeft a i j k : ℤ) : ℝ)) =
      fun i j k ↦ 2 ^ 12 * Bescovitch.splitFirstLeft
        (fun i j k ↦ (a i j k : ℝ)) i j k by
    funext i j k
    exact splitFirstLeft_cast a i j k]
  rw [tensorBernstein_scale, ← Bescovitch.tensorBernstein_splitFirstLeft]

private theorem tensorBernstein_splitFirstRight (a : Tensor) (x y z : I) :
    tensorBernstein (fun i j k ↦ ((splitFirstRight a i j k : ℤ) : ℝ)) x y z =
      2 ^ 12 * tensorBernstein (fun i j k ↦ (a i j k : ℝ))
        (unitIntervalRightHalf x) y z := by
  rw [show (fun i j k ↦ ((splitFirstRight a i j k : ℤ) : ℝ)) =
      fun i j k ↦ 2 ^ 12 * Bescovitch.splitFirstRight
        (fun i j k ↦ (a i j k : ℝ)) i j k by
    funext i j k
    exact splitFirstRight_cast a i j k]
  rw [tensorBernstein_scale, ← Bescovitch.tensorBernstein_splitFirstRight]

private theorem tensorBernstein_splitSecondLeft (a : Tensor) (x y z : I) :
    tensorBernstein (fun i j k ↦ ((splitSecondLeft a i j k : ℤ) : ℝ)) x y z =
      2 ^ 12 * tensorBernstein (fun i j k ↦ (a i j k : ℝ))
        x (unitIntervalLeftHalf y) z := by
  rw [show (fun i j k ↦ ((splitSecondLeft a i j k : ℤ) : ℝ)) =
      fun i j k ↦ 2 ^ 12 * Bescovitch.splitSecondLeft
        (fun i j k ↦ (a i j k : ℝ)) i j k by
    funext i j k
    exact splitSecondLeft_cast a i j k]
  rw [tensorBernstein_scale, ← Bescovitch.tensorBernstein_splitSecondLeft]

private theorem tensorBernstein_splitSecondRight (a : Tensor) (x y z : I) :
    tensorBernstein (fun i j k ↦ ((splitSecondRight a i j k : ℤ) : ℝ)) x y z =
      2 ^ 12 * tensorBernstein (fun i j k ↦ (a i j k : ℝ))
        x (unitIntervalRightHalf y) z := by
  rw [show (fun i j k ↦ ((splitSecondRight a i j k : ℤ) : ℝ)) =
      fun i j k ↦ 2 ^ 12 * Bescovitch.splitSecondRight
        (fun i j k ↦ (a i j k : ℝ)) i j k by
    funext i j k
    exact splitSecondRight_cast a i j k]
  rw [tensorBernstein_scale, ← Bescovitch.tensorBernstein_splitSecondRight]

private theorem tensorBernstein_splitThirdLeft (a : Tensor) (x y z : I) :
    tensorBernstein (fun i j k ↦ ((splitThirdLeft a i j k : ℤ) : ℝ)) x y z =
      2 ^ 4 * tensorBernstein (fun i j k ↦ (a i j k : ℝ))
        x y (unitIntervalLeftHalf z) := by
  rw [show (fun i j k ↦ ((splitThirdLeft a i j k : ℤ) : ℝ)) =
      fun i j k ↦ 2 ^ 4 * Bescovitch.splitThirdLeft
        (fun i j k ↦ (a i j k : ℝ)) i j k by
    funext i j k
    exact splitThirdLeft_cast a i j k]
  rw [tensorBernstein_scale, ← Bescovitch.tensorBernstein_splitThirdLeft]

private theorem tensorBernstein_splitThirdRight (a : Tensor) (x y z : I) :
    tensorBernstein (fun i j k ↦ ((splitThirdRight a i j k : ℤ) : ℝ)) x y z =
      2 ^ 4 * tensorBernstein (fun i j k ↦ (a i j k : ℝ))
        x y (unitIntervalRightHalf z) := by
  rw [show (fun i j k ↦ ((splitThirdRight a i j k : ℤ) : ℝ)) =
      fun i j k ↦ 2 ^ 4 * Bescovitch.splitThirdRight
        (fun i j k ↦ (a i j k : ℝ)) i j k by
    funext i j k
    exact splitThirdRight_cast a i j k]
  rw [tensorBernstein_scale, ← Bescovitch.tensorBernstein_splitThirdRight]

private theorem tensorBernstein_nonnegative_of_subdivision
    (tree : TensorSubdivision) (a : Tensor)
    (htree : SubdivisionNonnegative tree a) (x y z : I) :
    0 ≤ tensorBernstein (fun i j k ↦ (a i j k : ℝ)) x y z := by
  induction tree generalizing a x y z with
  | leaf =>
      apply Bescovitch.tensorBernstein_nonneg
      intro i j k
      exact_mod_cast htree i j k
  | splitFirst left right ihLeft ihRight =>
      rcases exists_unitInterval_half_chart x with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · have h := ihLeft (splitFirstLeft a) htree.1 u y z
        rw [tensorBernstein_splitFirstLeft] at h
        nlinarith
      · have h := ihRight (splitFirstRight a) htree.2 u y z
        rw [tensorBernstein_splitFirstRight] at h
        nlinarith
  | splitSecond left right ihLeft ihRight =>
      rcases exists_unitInterval_half_chart y with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · have h := ihLeft (splitSecondLeft a) htree.1 x u z
        rw [tensorBernstein_splitSecondLeft] at h
        nlinarith
      · have h := ihRight (splitSecondRight a) htree.2 x u z
        rw [tensorBernstein_splitSecondRight] at h
        nlinarith
  | splitThird left right ihLeft ihRight =>
      rcases exists_unitInterval_half_chart z with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · have h := ihLeft (splitThirdLeft a) htree.1 x y u
        rw [tensorBernstein_splitThirdLeft] at h
        nlinarith
      · have h := ihRight (splitThirdRight a) htree.2 x y u
        rw [tensorBernstein_splitThirdRight] at h
        nlinarith

private theorem choose_twelve_divides (h : Fin 13) :
    (Nat.choose 12 h : ℤ) ∣ 27720 := by
  fin_cases h <;> norm_num [Nat.choose]

private theorem choose_four_divides (h : Fin 5) :
    (Nat.choose 4 h : ℤ) ∣ 12 := by
  fin_cases h <;> norm_num [Nat.choose]

private theorem convertFirst_cast (a : Tensor) (i j : Fin 13) (k : Fin 5) :
    ((convertFirst a i j k : ℤ) : ℝ) =
      27720 * powerToBernstein 12 (fun h ↦ (a h j k : ℝ)) i := by
  rw [convertFirst, finSum_cast, powerToBernstein, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs
  · norm_num only [Int.cast_mul, Int.cast_natCast]
    rw [Int.cast_div (choose_twelve_divides h)]
    · norm_num only [Int.cast_natCast]
      ring
    · exact_mod_cast Nat.choose_ne_zero (Nat.lt_succ_iff.mp h.isLt)
  · simp

private theorem convertSecond_cast (a : Tensor) (i j : Fin 13) (k : Fin 5) :
    ((convertSecond (convertFirst a) i j k : ℤ) : ℝ) =
      27720 ^ 2 * powerToBernstein 12
        (fun h ↦ powerToBernstein 12 (fun q ↦ (a q h k : ℝ)) i) j := by
  rw [convertSecond, finSum_cast, powerToBernstein, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs
  · norm_num only [Int.cast_mul, Int.cast_natCast]
    rw [convertFirst_cast, Int.cast_div (choose_twelve_divides h)]
    · norm_num only [Int.cast_natCast]
      ring
    · exact_mod_cast Nat.choose_ne_zero (Nat.lt_succ_iff.mp h.isLt)
  · simp

private theorem convertPowerTensor_cast (a : Tensor) (i j : Fin 13) (k : Fin 5) :
    ((convertPowerTensor a i j k : ℤ) : ℝ) =
      (27720 ^ 2 * 12 : ℝ) * tensorPowerToBernstein
        (fun i j k ↦ (a i j k : ℝ)) i j k := by
  rw [convertPowerTensor, convertThird, finSum_cast, tensorPowerToBernstein,
    powerToBernstein, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs
  · norm_num only [Int.cast_mul, Int.cast_natCast]
    rw [convertSecond_cast, Int.cast_div (choose_four_divides h)]
    · norm_num only [Int.cast_natCast]
      ring
    · exact_mod_cast Nat.choose_ne_zero (Nat.lt_succ_iff.mp h.isLt)
  · simp

/-- A nonnegative scaled-integer subdivision certifies its original power tensor on the cube. -/
theorem paddedPowerTensor_nonnegative (tree : TensorSubdivision) (power : Tensor)
    (htree : SubdivisionNonnegative tree (convertPowerTensor power)) (x y z : I) :
    0 ≤ ∑ i : Fin 13, ∑ j : Fin 13, ∑ k : Fin 5,
      (power i j k : ℝ) * (x : ℝ) ^ (i : ℕ) *
        (y : ℝ) ^ (j : ℕ) * (z : ℝ) ^ (k : ℕ) := by
  have h := tensorBernstein_nonnegative_of_subdivision
    tree (convertPowerTensor power) htree x y z
  rw [show (fun i j k ↦ (convertPowerTensor power i j k : ℝ)) =
      fun i j k ↦ (27720 ^ 2 * 12 : ℝ) *
        tensorPowerToBernstein (fun i j k ↦ (power i j k : ℝ)) i j k by
    funext i j k
    exact convertPowerTensor_cast power i j k] at h
  rw [tensorBernstein_scale] at h
  rw [paddedPowerTensor_eq_tensorBernstein]
  nlinarith

end Bescovitch.IntegerTensorBernstein
