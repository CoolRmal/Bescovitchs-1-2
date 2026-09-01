/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.RadicalBernstein

/-!
# Bivariate tensor Bernstein polynomials
-/

@[expose] public section

open scoped BigOperators unitInterval

namespace Bescovitch

noncomputable section

/-- Evaluate a rectangular padded power tensor. -/
def paddedPowerTensorEval {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (x y : I) : ℝ :=
  ∑ i, ∑ j, a i j * (x : ℝ) ^ (i : ℕ) * (y : ℝ) ^ (j : ℕ)

/-- Convert both coordinates of a rectangular padded power tensor to Bernstein coefficients. -/
def powerTensorToBernstein {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) : ℝ :=
  powerToBernstein n (fun j' ↦ powerToBernstein m (fun i' ↦ a i' j') i) j

/-- Evaluate a rectangular tensor product of Bernstein polynomials. -/
def tensorBernsteinTwo {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (x y : I) : ℝ :=
  ∑ i, ∑ j, a i j * bernstein m i x * bernstein n j y

private theorem first_power_coordinate_to_bernstein {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1) → ℝ) (x : I) (second : Fin (n + 1) → ℝ) :
    (∑ i, ∑ j, a i j * (x : ℝ) ^ (i : ℕ) * second j) =
      ∑ i, ∑ j, powerToBernstein m (fun h ↦ a h j) i * bernstein m i x * second j := by
  calc
    _ = ∑ j, (∑ i, a i j * (x : ℝ) ^ (i : ℕ)) * second j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ = ∑ j, (∑ i, powerToBernstein m (fun h ↦ a h j) i * bernstein m i x) *
        second j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show (∑ i, a i j * (x : ℝ) ^ (i : ℕ)) =
        ∑ i, powerToBernstein m (fun h ↦ a h j) i * bernstein m i x by
          simpa only [paddedPowerEval] using
            paddedPowerEval_eq_bernstein_sum m (fun h ↦ a h j) x]
    _ = ∑ j, ∑ i, powerToBernstein m (fun h ↦ a h j) i * bernstein m i x *
        second j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ = _ := by rw [Finset.sum_comm]

private theorem second_power_coordinate_to_bernstein {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1) → ℝ) (first : Fin (m + 1) → ℝ) (y : I) :
    (∑ i, ∑ j, a i j * first i * (y : ℝ) ^ (j : ℕ)) =
      ∑ i, ∑ j, powerToBernstein n (fun h ↦ a i h) j * first i * bernstein n j y := by
  apply Finset.sum_congr rfl
  intro i hi
  have h : (∑ j, a i j * (y : ℝ) ^ (j : ℕ)) =
      ∑ j, powerToBernstein n (fun h ↦ a i h) j * bernstein n j y := by
    simpa only [paddedPowerEval] using
      paddedPowerEval_eq_bernstein_sum n (fun h ↦ a i h) y
  calc
    _ = (∑ j, a i j * (y : ℝ) ^ (j : ℕ)) * first i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j, powerToBernstein n (fun h ↦ a i h) j * bernstein n j y) * first i := by
      rw [h]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- A padded power tensor equals the tensor Bernstein polynomial of its converted coefficients. -/
theorem paddedPowerTensorEval_eq_tensorBernsteinTwo {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1) → ℝ) (x y : I) :
    paddedPowerTensorEval a x y =
      tensorBernsteinTwo (fun i j ↦ powerTensorToBernstein a i j) x y := by
  rw [paddedPowerTensorEval,
    first_power_coordinate_to_bernstein a x (fun j ↦ (y : ℝ) ^ (j : ℕ))]
  rw [second_power_coordinate_to_bernstein
    (fun i j ↦ powerToBernstein m (fun h ↦ a h j) i)
    (fun i ↦ bernstein m i x) y]
  unfold tensorBernsteinTwo powerTensorToBernstein
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Nonnegative coefficients give a nonnegative bivariate tensor Bernstein polynomial. -/
theorem tensorBernsteinTwo_nonneg {m n : ℕ}
    {a : Fin (m + 1) → Fin (n + 1) → ℝ} (ha : ∀ i j, 0 ≤ a i j) (x y : I) :
    0 ≤ tensorBernsteinTwo a x y := by
  unfold tensorBernsteinTwo
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (mul_nonneg (ha i j) bernstein_nonneg) bernstein_nonneg

/-- Nonnegative converted coefficients certify a nonnegative padded power tensor. -/
theorem paddedPowerTensorEval_nonneg_of_bernstein {m n : ℕ}
    {a : Fin (m + 1) → Fin (n + 1) → ℝ}
    (ha : ∀ i j, 0 ≤ powerTensorToBernstein a i j) (x y : I) :
    0 ≤ paddedPowerTensorEval a x y := by
  rw [paddedPowerTensorEval_eq_tensorBernsteinTwo]
  exact tensorBernsteinTwo_nonneg ha x y

end

end Bescovitch
