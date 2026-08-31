/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Tensor Bernstein certificates

This file gives the convex-hull certificate for a polynomial in three variables.  An adaptive
tree permits dyadic subdivision along different coordinates without filling the enclosing grid.
-/

@[expose] public section

noncomputable section

open scoped BigOperators unitInterval

namespace Bescovitch

/-- A trivariate tensor product of Bernstein polynomials. -/
def tensorBernstein {m n l : ℕ}
    (coeff : Fin (m + 1) → Fin (n + 1) → Fin (l + 1) → ℝ) (x y z : I) : ℝ :=
  ∑ i, ∑ j, ∑ k,
    coeff i j k * bernstein m i x * bernstein n j y * bernstein l k z

/-- Nonnegative coefficients give a nonnegative tensor Bernstein polynomial. -/
theorem tensorBernstein_nonneg {m n l : ℕ}
    {coeff : Fin (m + 1) → Fin (n + 1) → Fin (l + 1) → ℝ}
    (hcoeff : ∀ i j k, 0 ≤ coeff i j k) (x y z : I) :
    0 ≤ tensorBernstein coeff x y z := by
  unfold tensorBernstein
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    Finset.sum_nonneg fun k _ ↦ mul_nonneg
      (mul_nonneg (mul_nonneg (hcoeff i j k) bernstein_nonneg) bernstein_nonneg)
      bernstein_nonneg

/-- The left-half affine chart of the unit interval. -/
def unitIntervalLeftHalf (x : I) : I :=
  ⟨(x : ℝ) / 2, by constructor <;> nlinarith [x.2.1, x.2.2]⟩

/-- The right-half affine chart of the unit interval. -/
def unitIntervalRightHalf (x : I) : I :=
  ⟨(1 + (x : ℝ)) / 2, by constructor <;> nlinarith [x.2.1, x.2.2]⟩

/-- Every point of the unit interval lies in one of its two affine half charts. -/
theorem exists_unitInterval_half_chart (x : I) :
    (∃ u, unitIntervalLeftHalf u = x) ∨ (∃ u, unitIntervalRightHalf u = x) := by
  by_cases hx : (x : ℝ) ≤ 1 / 2
  · left
    let u : I := ⟨2 * (x : ℝ), by constructor <;> nlinarith [x.2.1, x.2.2]⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    simp only [unitIntervalLeftHalf, u]
    ring
  · right
    let u : I := ⟨2 * (x : ℝ) - 1, by constructor <;> nlinarith [x.2.1, x.2.2]⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    simp only [unitIntervalRightHalf, u]
    ring

/-- An adaptive dyadic subdivision whose leaves carry Bernstein coefficients. -/
inductive TensorBernsteinTree (m n l : ℕ) where
  | leaf (coeff : Fin (m + 1) → Fin (n + 1) → Fin (l + 1) → ℝ)
  | splitFirst (left right : TensorBernsteinTree m n l)
  | splitSecond (left right : TensorBernsteinTree m n l)
  | splitThird (left right : TensorBernsteinTree m n l)

namespace TensorBernsteinTree

/-- Every coefficient at every leaf of the tree is nonnegative. -/
def HasNonnegativeCoefficients {m n l : ℕ} : TensorBernsteinTree m n l → Prop
  | .leaf coeff => ∀ i j k, 0 ≤ coeff i j k
  | .splitFirst left right | .splitSecond left right | .splitThird left right =>
      left.HasNonnegativeCoefficients ∧ right.HasNonnegativeCoefficients

/-- Each leaf is the Bernstein expansion of the function in its dyadic chart. -/
def Represents {m n l : ℕ} :
    TensorBernsteinTree m n l → (I → I → I → ℝ) → Prop
  | .leaf coeff, f => ∀ x y z, f x y z = tensorBernstein coeff x y z
  | .splitFirst left right, f =>
      left.Represents (fun x y z ↦ f (unitIntervalLeftHalf x) y z) ∧
        right.Represents (fun x y z ↦ f (unitIntervalRightHalf x) y z)
  | .splitSecond left right, f =>
      left.Represents (fun x y z ↦ f x (unitIntervalLeftHalf y) z) ∧
        right.Represents (fun x y z ↦ f x (unitIntervalRightHalf y) z)
  | .splitThird left right, f =>
      left.Represents (fun x y z ↦ f x y (unitIntervalLeftHalf z)) ∧
        right.Represents (fun x y z ↦ f x y (unitIntervalRightHalf z))

/-- A represented adaptive tree with nonnegative leaf coefficients certifies nonnegativity. -/
theorem nonneg_of_represents {m n l : ℕ} {tree : TensorBernsteinTree m n l}
    {f : I → I → I → ℝ} (hcoeff : tree.HasNonnegativeCoefficients)
    (hrepresents : tree.Represents f) (x y z : I) : 0 ≤ f x y z := by
  induction tree generalizing f x y z with
  | leaf coeff =>
      rw [hrepresents x y z]
      exact tensorBernstein_nonneg hcoeff x y z
  | splitFirst left right ihLeft ihRight =>
      rcases exists_unitInterval_half_chart x with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact ihLeft hcoeff.1 hrepresents.1 u y z
      · exact ihRight hcoeff.2 hrepresents.2 u y z
  | splitSecond left right ihLeft ihRight =>
      rcases exists_unitInterval_half_chart y with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact ihLeft hcoeff.1 hrepresents.1 x u z
      · exact ihRight hcoeff.2 hrepresents.2 x u z
  | splitThird left right ihLeft ihRight =>
      rcases exists_unitInterval_half_chart z with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact ihLeft hcoeff.1 hrepresents.1 x y u
      · exact ihRight hcoeff.2 hrepresents.2 x y u

end TensorBernsteinTree

end Bescovitch
