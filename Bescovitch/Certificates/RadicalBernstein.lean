/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.RadicalPolynomial
public import Bescovitch.Certificates.TensorBernstein

/-!
# Bernstein conversion for exact radical polynomials

This file converts the fixed degree box used by the weighted-self certificate from the power
basis to the Bernstein basis.  Its coefficient expressions remain exact.
-/

@[expose] public section

open scoped BigOperators unitInterval

namespace Bescovitch

namespace RadicalExpression

/-- A finite sum in the syntax of radical expressions. -/
def finSum {n : ℕ} : (N : ℕ) → (Fin N → RadicalExpression n) → RadicalExpression n
  | 0, _ => .constant 0
  | k + 1, f => .add (f 0) (finSum k fun i => f i.succ)

theorem eval_finSum {n N : ℕ} (f : Fin N → RadicalExpression n) (input : Fin n → ℝ) :
    (finSum N f).eval input = ∑ i, (f i).eval input := by
  induction N with
  | zero => simp [finSum, RadicalExpression.eval]
  | succ N ih =>
      rw [Fin.sum_univ_succ]
      simp [finSum, RadicalExpression.eval, ih]

end RadicalExpression

/-- Evaluate a degree-`degree` padded power coefficient vector. -/
noncomputable def paddedPowerEval (degree : ℕ) (a : Fin (degree + 1) → ℝ)
    (x : ℝ) : ℝ :=
  ∑ i, a i * x ^ (i : ℕ)

/-- Convert one padded power coefficient to the Bernstein basis. -/
noncomputable def powerToBernstein (degree : ℕ) (a : Fin (degree + 1) → ℝ)
    (i : Fin (degree + 1)) : ℝ :=
  ∑ j : Fin (degree + 1), if (j : ℕ) ≤ i then
    a j * (Nat.choose (i : ℕ) (j : ℕ) / (Nat.choose degree (j : ℕ) : ℝ)) else 0

/-- The exact expression for one converted Bernstein coefficient. -/
def radicalPowerToBernstein {n : ℕ} (degree : ℕ)
    (a : Fin (degree + 1) → RadicalExpression n) (i : Fin (degree + 1)) :
    RadicalExpression n :=
  RadicalExpression.finSum (degree + 1) fun j => if (j : ℕ) ≤ i then
    .mul (a j) (.constant (Nat.choose (i : ℕ) (j : ℕ) / Nat.choose degree (j : ℕ)))
  else .constant 0

theorem eval_radicalPowerToBernstein {n degree : ℕ}
    (a : Fin (degree + 1) → RadicalExpression n) (i : Fin (degree + 1))
    (input : Fin n → ℝ) :
    (radicalPowerToBernstein degree a i).eval input =
      powerToBernstein degree (fun j => (a j).eval input) i := by
  rw [radicalPowerToBernstein, RadicalExpression.eval_finSum]
  unfold powerToBernstein
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · simp [RadicalExpression.eval]
  · simp [RadicalExpression.eval]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
theorem paddedPowerEval_twelve_eq (a : Fin 13 → ℝ) (x : I) :
    paddedPowerEval 12 a x =
      ∑ i, powerToBernstein 12 a i * bernstein 12 i x := by
  simp [paddedPowerEval, powerToBernstein, bernstein_apply, Fin.sum_univ_succ]
  norm_num [Nat.choose]
  ring

theorem paddedPowerEval_four_eq (a : Fin 5 → ℝ) (x : I) :
    paddedPowerEval 4 a x =
      ∑ i, powerToBernstein 4 a i * bernstein 4 i x := by
  simp [paddedPowerEval, powerToBernstein, bernstein_apply, Fin.sum_univ_succ]
  norm_num [Nat.choose]
  ring

/-- Convert all three coordinates of a `12 × 12 × 4` padded power tensor. -/
noncomputable def tensorPowerToBernstein (a : Fin 13 → Fin 13 → Fin 5 → ℝ)
    (i j : Fin 13) (k : Fin 5) : ℝ :=
  powerToBernstein 4
    (fun k' => powerToBernstein 12
      (fun j' => powerToBernstein 12 (fun i' => a i' j' k') i) j) k

/-- The exact expression for a converted `12 × 12 × 4` tensor coefficient. -/
def radicalTensorPowerToBernstein {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n)
    (i j : Fin 13) (k : Fin 5) :
    RadicalExpression n :=
  radicalPowerToBernstein 4
    (fun k' => radicalPowerToBernstein 12
      (fun j' => radicalPowerToBernstein 12 (fun i' => a i' j' k') i) j) k

theorem eval_radicalTensorPowerToBernstein {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n)
    (i j : Fin 13) (k : Fin 5)
    (input : Fin n → ℝ) :
    (radicalTensorPowerToBernstein a i j k).eval input =
      tensorPowerToBernstein (fun i j k => (a i j k).eval input) i j k := by
  simp only [radicalTensorPowerToBernstein, tensorPowerToBernstein,
    eval_radicalPowerToBernstein]

private theorem first_power_coordinate_to_bernstein
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x : I)
    (second : Fin 13 → ℝ) (third : Fin 5 → ℝ) :
    (∑ i, ∑ j, ∑ k, a i j k * (x : ℝ) ^ (i : ℕ) * second j * third k) =
      ∑ i, ∑ j, ∑ k,
        powerToBernstein 12 (fun h => a h j k) i * bernstein 12 i x *
          second j * third k := by
  calc
    _ = ∑ j, ∑ k, (∑ i, a i j k * (x : ℝ) ^ (i : ℕ)) * second j * third k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ j, ∑ k,
        (∑ i, powerToBernstein 12 (fun h => a h j k) i * bernstein 12 i x) *
          second j * third k := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [show (∑ i, a i j k * (x : ℝ) ^ (i : ℕ)) =
        ∑ i, powerToBernstein 12 (fun h => a h j k) i * bernstein 12 i x by
          simpa [paddedPowerEval] using paddedPowerEval_twelve_eq (fun h => a h j k) x]
    _ = ∑ j, ∑ i, ∑ k,
        powerToBernstein 12 (fun h => a h j k) i * bernstein 12 i x *
          second j * third k := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = _ := by rw [Finset.sum_comm]

private theorem second_power_coordinate_to_bernstein
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (first : Fin 13 → ℝ)
    (y : I) (third : Fin 5 → ℝ) :
    (∑ i, ∑ j, ∑ k, a i j k * first i * (y : ℝ) ^ (j : ℕ) * third k) =
      ∑ i, ∑ j, ∑ k,
        powerToBernstein 12 (fun h => a i h k) j * first i * bernstein 12 j y * third k := by
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ k, (∑ j, a i j k * (y : ℝ) ^ (j : ℕ)) * first i * third k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ k,
        (∑ j, powerToBernstein 12 (fun h => a i h k) j * bernstein 12 j y) *
          first i * third k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show (∑ j, a i j k * (y : ℝ) ^ (j : ℕ)) =
        ∑ j, powerToBernstein 12 (fun h => a i h k) j * bernstein 12 j y by
          simpa [paddedPowerEval] using paddedPowerEval_twelve_eq (fun h => a i h k) y]
    _ = ∑ j, ∑ k,
        powerToBernstein 12 (fun h => a i h k) j * first i * bernstein 12 j y * third k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring

private theorem third_power_coordinate_to_bernstein
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (first second : Fin 13 → ℝ) (z : I) :
    (∑ i, ∑ j, ∑ k, a i j k * first i * second j * (z : ℝ) ^ (k : ℕ)) =
      ∑ i, ∑ j, ∑ k,
        powerToBernstein 4 (fun h => a i j h) k * first i * second j * bernstein 4 k z := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h : (∑ k, a i j k * (z : ℝ) ^ (k : ℕ)) =
      ∑ k, powerToBernstein 4 (fun h => a i j h) k * bernstein 4 k z := by
    simpa [paddedPowerEval] using paddedPowerEval_four_eq (fun k => a i j k) z
  calc
    _ = (∑ k, a i j k * (z : ℝ) ^ (k : ℕ)) * first i * second j := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (∑ k, powerToBernstein 4 (fun h => a i j h) k * bernstein 4 k z) *
        first i * second j := by rw [h]
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- The fixed padded power tensor equals its tensor-Bernstein expansion. -/
theorem paddedPowerTensor_eq_tensorBernstein (a : Fin 13 → Fin 13 → Fin 5 → ℝ)
    (x y z : I) :
    (∑ i, ∑ j, ∑ k,
      a i j k * (x : ℝ) ^ (i : ℕ) * (y : ℝ) ^ (j : ℕ) * (z : ℝ) ^ (k : ℕ)) =
      tensorBernstein (fun i j k => tensorPowerToBernstein a i j k) x y z := by
  rw [first_power_coordinate_to_bernstein a x
    (fun j => (y : ℝ) ^ (j : ℕ)) (fun k => (z : ℝ) ^ (k : ℕ))]
  rw [second_power_coordinate_to_bernstein
    (fun i j k => powerToBernstein 12 (fun h => a h j k) i)
    (fun i => bernstein 12 i x) y (fun k => (z : ℝ) ^ (k : ℕ))]
  rw [third_power_coordinate_to_bernstein
    (fun i j k => powerToBernstein 12
      (fun h => powerToBernstein 12 (fun h' => a h' h k) i) j)
    (fun i => bernstein 12 i x) (fun j => bernstein 12 j y) z]
  unfold tensorBernstein tensorPowerToBernstein
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Left-half de Casteljau coefficients in degree twelve. -/
noncomputable def bernsteinLeftTwelve (a : Fin 13 → ℝ) (i : Fin 13) : ℝ :=
  ∑ j : Fin 13, if (j : ℕ) ≤ i then
    a j * (Nat.choose (i : ℕ) (j : ℕ) / 2 ^ (i : ℕ) : ℝ) else 0

/-- Right-half de Casteljau coefficients in degree twelve. -/
noncomputable def bernsteinRightTwelve (a : Fin 13 → ℝ) (i : Fin 13) : ℝ :=
  ∑ j : Fin 13, if h : (j : ℕ) ≤ 12 - (i : ℕ) then
    a ⟨(i : ℕ) + j, by omega⟩ *
      (Nat.choose (12 - (i : ℕ)) (j : ℕ) / 2 ^ (12 - (i : ℕ)) : ℝ) else 0

/-- Left-half de Casteljau coefficients in degree four. -/
noncomputable def bernsteinLeftFour (a : Fin 5 → ℝ) (i : Fin 5) : ℝ :=
  ∑ j : Fin 5, if (j : ℕ) ≤ i then
    a j * (Nat.choose (i : ℕ) (j : ℕ) / 2 ^ (i : ℕ) : ℝ) else 0

/-- Right-half de Casteljau coefficients in degree four. -/
noncomputable def bernsteinRightFour (a : Fin 5 → ℝ) (i : Fin 5) : ℝ :=
  ∑ j : Fin 5, if h : (j : ℕ) ≤ 4 - (i : ℕ) then
    a ⟨(i : ℕ) + j, by omega⟩ *
      (Nat.choose (4 - (i : ℕ)) (j : ℕ) / 2 ^ (4 - (i : ℕ)) : ℝ) else 0

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
theorem bernstein_twelve_left_half (a : Fin 13 → ℝ) (x : I) :
    (∑ i, a i * bernstein 12 i (unitIntervalLeftHalf x)) =
      ∑ i, bernsteinLeftTwelve a i * bernstein 12 i x := by
  simp [bernsteinLeftTwelve, bernstein_apply, unitIntervalLeftHalf, Fin.sum_univ_succ]
  norm_num [Nat.choose]
  ring

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
theorem bernstein_twelve_right_half (a : Fin 13 → ℝ) (x : I) :
    (∑ i, a i * bernstein 12 i (unitIntervalRightHalf x)) =
      ∑ i, bernsteinRightTwelve a i * bernstein 12 i x := by
  simp [bernsteinRightTwelve, bernstein_apply, unitIntervalRightHalf, Fin.sum_univ_succ]
  norm_num [Nat.choose]
  ring

theorem bernstein_four_left_half (a : Fin 5 → ℝ) (x : I) :
    (∑ i, a i * bernstein 4 i (unitIntervalLeftHalf x)) =
      ∑ i, bernsteinLeftFour a i * bernstein 4 i x := by
  simp [bernsteinLeftFour, bernstein_apply, unitIntervalLeftHalf, Fin.sum_univ_succ]
  norm_num [Nat.choose]
  ring

theorem bernstein_four_right_half (a : Fin 5 → ℝ) (x : I) :
    (∑ i, a i * bernstein 4 i (unitIntervalRightHalf x)) =
      ∑ i, bernsteinRightFour a i * bernstein 4 i x := by
  simp [bernsteinRightFour, bernstein_apply, unitIntervalRightHalf, Fin.sum_univ_succ]
  norm_num [Nat.choose]
  ring

/-- Exact left-half de Casteljau coefficients in degree twelve. -/
def radicalBernsteinLeftTwelve {n : ℕ}
    (a : Fin 13 → RadicalExpression n) (i : Fin 13) : RadicalExpression n :=
  RadicalExpression.finSum 13 fun j => if (j : ℕ) ≤ i then
    .mul (a j) (.constant (Nat.choose (i : ℕ) (j : ℕ) / 2 ^ (i : ℕ))) else .constant 0

/-- Exact right-half de Casteljau coefficients in degree twelve. -/
def radicalBernsteinRightTwelve {n : ℕ}
    (a : Fin 13 → RadicalExpression n) (i : Fin 13) : RadicalExpression n :=
  RadicalExpression.finSum 13 fun j => if h : (j : ℕ) ≤ 12 - (i : ℕ) then
    .mul (a ⟨(i : ℕ) + j, by omega⟩)
      (.constant (Nat.choose (12 - (i : ℕ)) (j : ℕ) / 2 ^ (12 - (i : ℕ))))
  else .constant 0

/-- Exact left-half de Casteljau coefficients in degree four. -/
def radicalBernsteinLeftFour {n : ℕ}
    (a : Fin 5 → RadicalExpression n) (i : Fin 5) : RadicalExpression n :=
  RadicalExpression.finSum 5 fun j => if (j : ℕ) ≤ i then
    .mul (a j) (.constant (Nat.choose (i : ℕ) (j : ℕ) / 2 ^ (i : ℕ))) else .constant 0

/-- Exact right-half de Casteljau coefficients in degree four. -/
def radicalBernsteinRightFour {n : ℕ}
    (a : Fin 5 → RadicalExpression n) (i : Fin 5) : RadicalExpression n :=
  RadicalExpression.finSum 5 fun j => if h : (j : ℕ) ≤ 4 - (i : ℕ) then
    .mul (a ⟨(i : ℕ) + j, by omega⟩)
      (.constant (Nat.choose (4 - (i : ℕ)) (j : ℕ) / 2 ^ (4 - (i : ℕ))))
  else .constant 0

private theorem eval_radicalBernsteinLeftTwelve {n : ℕ}
    (a : Fin 13 → RadicalExpression n) (i : Fin 13) (input : Fin n → ℝ) :
    (radicalBernsteinLeftTwelve a i).eval input =
      bernsteinLeftTwelve (fun j => (a j).eval input) i := by
  rw [radicalBernsteinLeftTwelve, RadicalExpression.eval_finSum]
  unfold bernsteinLeftTwelve
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp [RadicalExpression.eval]

private theorem eval_radicalBernsteinRightTwelve {n : ℕ}
    (a : Fin 13 → RadicalExpression n) (i : Fin 13) (input : Fin n → ℝ) :
    (radicalBernsteinRightTwelve a i).eval input =
      bernsteinRightTwelve (fun j => (a j).eval input) i := by
  rw [radicalBernsteinRightTwelve, RadicalExpression.eval_finSum]
  unfold bernsteinRightTwelve
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp [RadicalExpression.eval]

private theorem eval_radicalBernsteinLeftFour {n : ℕ}
    (a : Fin 5 → RadicalExpression n) (i : Fin 5) (input : Fin n → ℝ) :
    (radicalBernsteinLeftFour a i).eval input =
      bernsteinLeftFour (fun j => (a j).eval input) i := by
  rw [radicalBernsteinLeftFour, RadicalExpression.eval_finSum]
  unfold bernsteinLeftFour
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp [RadicalExpression.eval]

private theorem eval_radicalBernsteinRightFour {n : ℕ}
    (a : Fin 5 → RadicalExpression n) (i : Fin 5) (input : Fin n → ℝ) :
    (radicalBernsteinRightFour a i).eval input =
      bernsteinRightFour (fun j => (a j).eval input) i := by
  rw [radicalBernsteinRightFour, RadicalExpression.eval_finSum]
  unfold bernsteinRightFour
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp [RadicalExpression.eval]

private noncomputable def splitFirstLeft (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :
    Fin 13 → Fin 13 → Fin 5 → ℝ :=
  fun i j k => bernsteinLeftTwelve (fun h => a h j k) i

private noncomputable def splitFirstRight (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :
    Fin 13 → Fin 13 → Fin 5 → ℝ :=
  fun i j k => bernsteinRightTwelve (fun h => a h j k) i

private noncomputable def splitSecondLeft (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :
    Fin 13 → Fin 13 → Fin 5 → ℝ :=
  fun i j k => bernsteinLeftTwelve (fun h => a i h k) j

private noncomputable def splitSecondRight (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :
    Fin 13 → Fin 13 → Fin 5 → ℝ :=
  fun i j k => bernsteinRightTwelve (fun h => a i h k) j

private noncomputable def splitThirdLeft (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :
    Fin 13 → Fin 13 → Fin 5 → ℝ :=
  fun i j k => bernsteinLeftFour (fun h => a i j h) k

private noncomputable def splitThirdRight (a : Fin 13 → Fin 13 → Fin 5 → ℝ) :
    Fin 13 → Fin 13 → Fin 5 → ℝ :=
  fun i j k => bernsteinRightFour (fun h => a i j h) k

/-- Split exact tensor coefficients along the left half of the first coordinate. -/
def radicalSplitFirstLeft {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) :=
  fun i j k => radicalBernsteinLeftTwelve (fun h => a h j k) i

/-- Split exact tensor coefficients along the right half of the first coordinate. -/
def radicalSplitFirstRight {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) :=
  fun i j k => radicalBernsteinRightTwelve (fun h => a h j k) i

/-- Split exact tensor coefficients along the left half of the second coordinate. -/
def radicalSplitSecondLeft {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) :=
  fun i j k => radicalBernsteinLeftTwelve (fun h => a i h k) j

/-- Split exact tensor coefficients along the right half of the second coordinate. -/
def radicalSplitSecondRight {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) :=
  fun i j k => radicalBernsteinRightTwelve (fun h => a i h k) j

/-- Split exact tensor coefficients along the left half of the third coordinate. -/
def radicalSplitThirdLeft {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) :=
  fun i j k => radicalBernsteinLeftFour (fun h => a i j h) k

/-- Split exact tensor coefficients along the right half of the third coordinate. -/
def radicalSplitThirdRight {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) :=
  fun i j k => radicalBernsteinRightFour (fun h => a i j h) k

private theorem eval_radicalSplitFirstLeft {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) (input : Fin n → ℝ) :
    (fun i j k => ((radicalSplitFirstLeft a) i j k).eval input) =
      splitFirstLeft (fun i j k => (a i j k).eval input) := by
  funext i j k
  exact eval_radicalBernsteinLeftTwelve (fun h => a h j k) i input

private theorem eval_radicalSplitFirstRight {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) (input : Fin n → ℝ) :
    (fun i j k => ((radicalSplitFirstRight a) i j k).eval input) =
      splitFirstRight (fun i j k => (a i j k).eval input) := by
  funext i j k
  exact eval_radicalBernsteinRightTwelve (fun h => a h j k) i input

private theorem eval_radicalSplitSecondLeft {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) (input : Fin n → ℝ) :
    (fun i j k => ((radicalSplitSecondLeft a) i j k).eval input) =
      splitSecondLeft (fun i j k => (a i j k).eval input) := by
  funext i j k
  exact eval_radicalBernsteinLeftTwelve (fun h => a i h k) j input

private theorem eval_radicalSplitSecondRight {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) (input : Fin n → ℝ) :
    (fun i j k => ((radicalSplitSecondRight a) i j k).eval input) =
      splitSecondRight (fun i j k => (a i j k).eval input) := by
  funext i j k
  exact eval_radicalBernsteinRightTwelve (fun h => a i h k) j input

private theorem eval_radicalSplitThirdLeft {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) (input : Fin n → ℝ) :
    (fun i j k => ((radicalSplitThirdLeft a) i j k).eval input) =
      splitThirdLeft (fun i j k => (a i j k).eval input) := by
  funext i j k
  exact eval_radicalBernsteinLeftFour (fun h => a i j h) k input

private theorem eval_radicalSplitThirdRight {n : ℕ}
    (a : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) (input : Fin n → ℝ) :
    (fun i j k => ((radicalSplitThirdRight a) i j k).eval input) =
      splitThirdRight (fun i j k => (a i j k).eval input) := by
  funext i j k
  exact eval_radicalBernsteinRightFour (fun h => a i j h) k input

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
  unfold splitFirstLeft
  exact tensorBernstein_first_coordinate a unitIntervalLeftHalf bernsteinLeftTwelve
    bernstein_twelve_left_half x y z

private theorem tensorBernstein_splitFirstRight
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x y z : I) :
    tensorBernstein a (unitIntervalRightHalf x) y z =
      tensorBernstein (splitFirstRight a) x y z := by
  unfold splitFirstRight
  exact tensorBernstein_first_coordinate a unitIntervalRightHalf bernsteinRightTwelve
    bernstein_twelve_right_half x y z

private theorem tensorBernstein_splitSecondLeft
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x y z : I) :
    tensorBernstein a x (unitIntervalLeftHalf y) z =
      tensorBernstein (splitSecondLeft a) x y z := by
  unfold splitSecondLeft
  exact tensorBernstein_second_coordinate a unitIntervalLeftHalf bernsteinLeftTwelve
    bernstein_twelve_left_half x y z

private theorem tensorBernstein_splitSecondRight
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x y z : I) :
    tensorBernstein a x (unitIntervalRightHalf y) z =
      tensorBernstein (splitSecondRight a) x y z := by
  unfold splitSecondRight
  exact tensorBernstein_second_coordinate a unitIntervalRightHalf bernsteinRightTwelve
    bernstein_twelve_right_half x y z

private theorem tensorBernstein_splitThirdLeft
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x y z : I) :
    tensorBernstein a x y (unitIntervalLeftHalf z) =
      tensorBernstein (splitThirdLeft a) x y z := by
  unfold splitThirdLeft
  exact tensorBernstein_third_coordinate a unitIntervalLeftHalf bernsteinLeftFour
    bernstein_four_left_half x y z

private theorem tensorBernstein_splitThirdRight
    (a : Fin 13 → Fin 13 → Fin 5 → ℝ) (x y z : I) :
    tensorBernstein a x y (unitIntervalRightHalf z) =
      tensorBernstein (splitThirdRight a) x y z := by
  unfold splitThirdRight
  exact tensorBernstein_third_coordinate a unitIntervalRightHalf bernsteinRightFour
    bernstein_four_right_half x y z

namespace RadicalExpression

/-- Check that interval evaluation gives a nonnegative lower endpoint. -/
def certifiesNonnegative {n : ℕ} (f : RadicalExpression n)
    (box : Fin n → RationalInterval) : Bool :=
  match f.enclosure box with
  | none => false
  | some enclosure => decide (0 ≤ enclosure.lower)

theorem certifiesNonnegative_sound {n : ℕ} {f : RadicalExpression n}
    {box : Fin n → RationalInterval} {input : Fin n → ℝ}
    (hinput : ∀ i, (box i).Contains (input i))
    (h : f.certifiesNonnegative box = true) : 0 ≤ f.eval input := by
  unfold certifiesNonnegative at h
  cases hEnclosure : f.enclosure box with
  | none => simp [hEnclosure] at h
  | some enclosure =>
      rw [hEnclosure] at h
      have hlower := of_decide_eq_true h
      have hvalue := enclosure_sound hinput hEnclosure
      have hzero : (0 : ℝ) ≤ enclosure.lower := by exact_mod_cast hlower
      exact hzero.trans hvalue.1

end RadicalExpression

/-- A finite adaptive subdivision of a three-dimensional unit cube. -/
inductive TensorSubdivision where
  | leaf
  | splitFirst (left right : TensorSubdivision)
  | splitSecond (left right : TensorSubdivision)
  | splitThird (left right : TensorSubdivision)

/-- Check nonnegativity of every coefficient in an exact fixed tensor. -/
def radicalTensorCoefficientsNonnegative {n : ℕ}
    (coefficients : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n)
    (box : Fin n → RationalInterval) : Bool :=
  decide (∀ i j k, (coefficients i j k).certifiesNonnegative box = true)

/-- Check every leaf coefficient after the prescribed dyadic subdivisions. -/
def tensorSubdivisionCertifiesNonnegative {n : ℕ} :
    TensorSubdivision → (Fin 13 → Fin 13 → Fin 5 → RadicalExpression n) →
      (Fin n → RationalInterval) → Bool
  | .leaf, coefficients, box => radicalTensorCoefficientsNonnegative coefficients box
  | .splitFirst left right, coefficients, box =>
      tensorSubdivisionCertifiesNonnegative left (radicalSplitFirstLeft coefficients) box &&
        tensorSubdivisionCertifiesNonnegative right (radicalSplitFirstRight coefficients) box
  | .splitSecond left right, coefficients, box =>
      tensorSubdivisionCertifiesNonnegative left (radicalSplitSecondLeft coefficients) box &&
        tensorSubdivisionCertifiesNonnegative right (radicalSplitSecondRight coefficients) box
  | .splitThird left right, coefficients, box =>
      tensorSubdivisionCertifiesNonnegative left (radicalSplitThirdLeft coefficients) box &&
        tensorSubdivisionCertifiesNonnegative right (radicalSplitThirdRight coefficients) box

theorem tensorSubdivision_nonneg_of_certificate {n : ℕ} (tree : TensorSubdivision)
    (coefficients : Fin 13 → Fin 13 → Fin 5 → RadicalExpression n)
    (box : Fin n → RationalInterval) (input : Fin n → ℝ)
    (hinput : ∀ i, (box i).Contains (input i))
    (hcertificate : tensorSubdivisionCertifiesNonnegative tree coefficients box = true)
    (x y z : I) :
    0 ≤ tensorBernstein (fun i j k => (coefficients i j k).eval input) x y z := by
  induction tree generalizing coefficients x y z with
  | leaf =>
      change radicalTensorCoefficientsNonnegative coefficients box = true at hcertificate
      unfold radicalTensorCoefficientsNonnegative at hcertificate
      have hcoefficients :
          ∀ i j k, (coefficients i j k).certifiesNonnegative box = true :=
        of_decide_eq_true hcertificate
      exact tensorBernstein_nonneg (fun i j k =>
        RadicalExpression.certifiesNonnegative_sound hinput (hcoefficients i j k)) x y z
  | splitFirst left right ihLeft ihRight =>
      change (tensorSubdivisionCertifiesNonnegative left
        (radicalSplitFirstLeft coefficients) box &&
        tensorSubdivisionCertifiesNonnegative right
          (radicalSplitFirstRight coefficients) box) = true at hcertificate
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases exists_unitInterval_half_chart x with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · rw [tensorBernstein_splitFirstLeft]
        have hleft := ihLeft (radicalSplitFirstLeft coefficients) hparts.1 u y z
        rw [eval_radicalSplitFirstLeft] at hleft
        exact hleft
      · rw [tensorBernstein_splitFirstRight]
        have hright := ihRight (radicalSplitFirstRight coefficients) hparts.2 u y z
        rw [eval_radicalSplitFirstRight] at hright
        exact hright
  | splitSecond left right ihLeft ihRight =>
      change (tensorSubdivisionCertifiesNonnegative left
        (radicalSplitSecondLeft coefficients) box &&
        tensorSubdivisionCertifiesNonnegative right
          (radicalSplitSecondRight coefficients) box) = true at hcertificate
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases exists_unitInterval_half_chart y with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · rw [tensorBernstein_splitSecondLeft]
        have hleft := ihLeft (radicalSplitSecondLeft coefficients) hparts.1 x u z
        rw [eval_radicalSplitSecondLeft] at hleft
        exact hleft
      · rw [tensorBernstein_splitSecondRight]
        have hright := ihRight (radicalSplitSecondRight coefficients) hparts.2 x u z
        rw [eval_radicalSplitSecondRight] at hright
        exact hright
  | splitThird left right ihLeft ihRight =>
      change (tensorSubdivisionCertifiesNonnegative left
        (radicalSplitThirdLeft coefficients) box &&
        tensorSubdivisionCertifiesNonnegative right
          (radicalSplitThirdRight coefficients) box) = true at hcertificate
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases exists_unitInterval_half_chart z with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · rw [tensorBernstein_splitThirdLeft]
        have hleft := ihLeft (radicalSplitThirdLeft coefficients) hparts.1 x y u
        rw [eval_radicalSplitThirdLeft] at hleft
        exact hleft
      · rw [tensorBernstein_splitThirdRight]
        have hright := ihRight (radicalSplitThirdRight coefficients) hparts.2 x y u
        rw [eval_radicalSplitThirdRight] at hright
        exact hright

/-- The exact root Bernstein coefficients of a fitted radical polynomial. -/
def RadicalTrivariate.bernsteinCoefficients {n : ℕ} (p : RadicalTrivariate n) :
    Fin 13 → Fin 13 → Fin 5 → RadicalExpression n :=
  radicalTensorPowerToBernstein fun i j k => p.coefficient i j k

theorem RadicalTrivariate.eval_eq_tensorBernstein {n : ℕ} (p : RadicalTrivariate n)
    (hfits : p.Fits 12 12 4) (input : Fin n → ℝ) (x y z : I) :
    p.eval input x y z =
      tensorBernstein (fun i j k => (p.bernsteinCoefficients i j k).eval input) x y z := by
  rw [p.eval_eq_power_sum hfits]
  rw [paddedPowerTensor_eq_tensorBernstein]
  congr 1
  funext i j k
  exact (eval_radicalTensorPowerToBernstein
    (fun i j k => p.coefficient i j k) i j k input).symm

/-- A fitted radical polynomial with a successful adaptive certificate is nonnegative. -/
theorem RadicalTrivariate.nonneg_of_bernstein_certificate {n : ℕ}
    (p : RadicalTrivariate n) (hfits : p.Fits 12 12 4) (tree : TensorSubdivision)
    (box : Fin n → RationalInterval) (input : Fin n → ℝ)
    (hinput : ∀ i, (box i).Contains (input i))
    (hcertificate : tensorSubdivisionCertifiesNonnegative tree
      p.bernsteinCoefficients box = true)
    (x y z : I) : 0 ≤ p.eval input x y z := by
  rw [p.eval_eq_tensorBernstein hfits]
  exact tensorSubdivision_nonneg_of_certificate tree p.bernsteinCoefficients box input hinput
    hcertificate x y z

end Bescovitch
