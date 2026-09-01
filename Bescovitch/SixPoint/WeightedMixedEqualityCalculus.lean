/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedEqualityLocalCertificate
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Calculus for rational vector expressions

This file contains the small derivative API shared by the transverse and face arguments for
the exceptional weighted mixed chart.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Bescovitch.WeightedMixedEqualityLocal

namespace Expression

/-- A rational expression is regular at a point when every inverted subexpression is nonzero. -/
def RegularAt {n : ℕ} : Expression n → (Fin n → ℝ) → Prop
  | .var _, _ | .constant _, _ => True
  | .add f g, x | .mul f g, x => RegularAt f x ∧ RegularAt g x
  | .neg f, x => RegularAt f x
  | .inv f, x => RegularAt f x ∧ f.eval x ≠ 0

/-- Evaluation along one updated coordinate has the formal partial derivative. -/
theorem hasDerivAt_update {n : ℕ} (f : Expression n) (i : Fin n)
    (x : Fin n → ℝ) (t : ℝ) (hregular : RegularAt f (Function.update x i t)) :
    HasDerivAt (fun s ↦ f.eval (Function.update x i s))
      ((partialDerivative i f).eval (Function.update x i t)) t := by
  induction f with
  | var j =>
      by_cases h : i = j
      · subst j
        convert! hasDerivAt_id t using 1 <;>
          simp [partialDerivative, RationalExpression.eval]
        ext s
        rfl
      · convert! hasDerivAt_const t (x j) using 1 <;>
          simp [partialDerivative, RationalExpression.eval, h, Ne.symm h]
  | constant q =>
      convert! hasDerivAt_const t (q : ℝ) using 1
      simp [RationalExpression.eval]
  | add f g hf hg =>
      exact (hf hregular.1).add (hg hregular.2)
  | neg f hf =>
      exact (hf hregular).neg
  | mul f g hf hg =>
      exact (hf hregular.1).mul (hg hregular.2)
  | inv f hf =>
      convert! (hf hregular.1).inv hregular.2 using 1
      simp [RationalExpression.eval]
      ring

/-- The affine line through `x` in direction `d`. -/
def affineInput {n : ℕ} (x d : Fin n → ℝ) (s : ℝ) : Fin n → ℝ :=
  fun i ↦ x i + s * d i

/-- Evaluation along an affine line has the directional derivative given by its gradient. -/
theorem hasDerivAt_affine {n : ℕ} (f : Expression n)
    (x d : Fin n → ℝ) (t : ℝ) (hregular : RegularAt f (affineInput x d t)) :
    HasDerivAt (fun s ↦ f.eval (affineInput x d s))
      (∑ i, d i * (partialDerivative i f).eval (affineInput x d t)) t := by
  induction f with
  | var j =>
      convert! (hasDerivAt_const t (x j)).add ((hasDerivAt_id t).mul_const (d j)) using 1
      simp [partialDerivative]
      classical
      rw [Finset.sum_eq_single j]
      · simp [RationalExpression.eval]
      · intro i _ hi
        simp [RationalExpression.eval, hi]
      · simp
  | constant q =>
      convert! hasDerivAt_const t (q : ℝ) using 1
      simp [RationalExpression.eval]
  | add f g hf hg =>
      convert! (hf hregular.1).add (hg hregular.2) using 1
      simp [RationalExpression.eval]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
  | neg f hf =>
      convert! (hf hregular).neg using 1
      simp [RationalExpression.eval]
  | mul f g hf hg =>
      convert! (hf hregular.1).mul (hg hregular.2) using 1
      simp [RationalExpression.eval]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · simp_rw [← mul_assoc]
        rw [← Finset.sum_mul]
      · calc
          _ = ∑ i, f.eval (affineInput x d t) *
              (d i * (partialDerivative i g).eval (affineInput x d t)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := (Finset.mul_sum ..).symm
  | inv f hf =>
      convert! (hf hregular.1).inv hregular.2 using 1
      simp [RationalExpression.eval]
      simp_rw [← pow_two]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      field_simp [hregular.2]

/-- Formal partial differentiation preserves regularity. -/
theorem regularAt_partialDerivative {n : ℕ} (f : Expression n) (i : Fin n)
    (x : Fin n → ℝ) (hf : RegularAt f x) : RegularAt (partialDerivative i f) x := by
  induction f with
  | var j => by_cases h : i = j <;> simp [partialDerivative, RegularAt, h]
  | constant q => simp [RegularAt]
  | add f g hf' hg' =>
      simpa only [partialDerivative, RegularAt] using ⟨hf' hf.1, hg' hf.2⟩
  | neg f hf' => simpa only [partialDerivative, RegularAt] using hf' hf
  | mul f g hf' hg' =>
      simpa only [partialDerivative, RegularAt] using
        ⟨⟨hf' hf.1, hf.2⟩, ⟨hf.1, hg' hf.2⟩⟩
  | inv f hf' =>
      simpa only [partialDerivative, RegularAt] using
        ⟨hf' hf.1, ⟨⟨hf.1, hf.2⟩, ⟨hf.1, hf.2⟩⟩⟩

/-- Evaluation commutes with the rational-expression negation helper. -/
@[simp] lemma eval_neg {n : ℕ} (f : Expression n) (x : Fin n → ℝ) :
    (RationalExpression.neg f).eval x = -f.eval x := by
  simp [RationalExpression.eval]

/-- Evaluation commutes with the rational-expression multiplication helper. -/
@[simp] lemma eval_mul {n : ℕ} (f g : Expression n) (x : Fin n → ℝ) :
    (RationalExpression.mul f g).eval x = f.eval x * g.eval x := by
  simp [RationalExpression.eval]

/-- The two formal partial derivatives of a rational expression commute after evaluation. -/
theorem partialDerivative_comm_eval {n : ℕ} (f : Expression n) (i j : Fin n)
    (x : Fin n → ℝ) :
    (partialDerivative i (partialDerivative j f)).eval x =
      (partialDerivative j (partialDerivative i f)).eval x := by
  induction f with
  | var k => by_cases hi : i = k <;> by_cases hj : j = k <;>
      simp [partialDerivative, RationalExpression.eval, hi, hj]
  | constant q => simp [RationalExpression.eval]
  | add f g hf hg => simp [RationalExpression.eval, hf, hg]
  | neg f hf => simp [RationalExpression.eval, hf]
  | mul f g hf hg =>
      simp [RationalExpression.eval, hf, hg]
      ring
  | inv f hf =>
      simp [RationalExpression.eval, hf]
      ring

end Expression

namespace Vector

/-- A rational two-vector is regular when both coordinate expressions are regular. -/
def RegularAt {n : ℕ} (p : Vector n) (x : Fin n → ℝ) : Prop :=
  Expression.RegularAt p.first x ∧ Expression.RegularAt p.second x

/-- Directional derivative of a rational two-vector. -/
def affineDerivative {n : ℕ} (p : Vector n) (x d : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  !₂[∑ i, d i * (Expression.partialDerivative i p.first).eval x,
    ∑ i, d i * (Expression.partialDerivative i p.second).eval x]

/-- Evaluation of a rational two-vector along a regular affine line is differentiable. -/
theorem hasDerivAt_affine {n : ℕ} (p : Vector n)
    (x d : Fin n → ℝ) (t : ℝ) (hregular : RegularAt p (Expression.affineInput x d t)) :
    HasDerivAt (fun s ↦ p.eval (Expression.affineInput x d s))
      (affineDerivative p (Expression.affineInput x d t) d) t := by
  let e₀ : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
  let e₁ : EuclideanSpace ℝ (Fin 2) := !₂[0, 1]
  have hfirst := (Expression.hasDerivAt_affine p.first x d t hregular.1).smul_const e₀
  have hsecond := (Expression.hasDerivAt_affine p.second x d t hregular.2).smul_const e₁
  convert! hfirst.add hsecond using 1
  · funext s
    ext i
    fin_cases i <;> simp [eval, e₀, e₁]
  · ext i
    fin_cases i <;> simp [affineDerivative, e₀, e₁]

/-- Evaluation of a rational two-vector along one coordinate is differentiable. -/
theorem hasDerivAt_update {n : ℕ} (p : Vector n) (i : Fin n)
    (x : Fin n → ℝ) (t : ℝ) (hregular : RegularAt p (Function.update x i t)) :
    HasDerivAt (fun s ↦ p.eval (Function.update x i s))
      ((p.partialDerivative i).eval (Function.update x i t)) t := by
  let e₀ : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
  let e₁ : EuclideanSpace ℝ (Fin 2) := !₂[0, 1]
  have hfirst := (Expression.hasDerivAt_update p.first i x t hregular.1).smul_const e₀
  have hsecond := (Expression.hasDerivAt_update p.second i x t hregular.2).smul_const e₁
  convert! hfirst.add hsecond using 1
  · funext s
    ext j
    fin_cases j <;> simp [eval, e₀, e₁]
  · ext j
    fin_cases j <;> simp [eval, e₀, e₁]

/-- Formal partial differentiation preserves regularity of a rational two-vector. -/
theorem regularAt_partialDerivative {n : ℕ} (p : Vector n) (i : Fin n)
    (x : Fin n → ℝ) (hp : RegularAt p x) : RegularAt (p.partialDerivative i) x :=
  ⟨Expression.regularAt_partialDerivative p.first i x hp.1,
    Expression.regularAt_partialDerivative p.second i x hp.2⟩

/-- The difference of two regular rational vectors is regular. -/
theorem RegularAt.sub {n : ℕ} (p q : Vector n) (x : Fin n → ℝ)
    (hp : RegularAt p x) (hq : RegularAt q x) : RegularAt (p.sub q) x :=
  ⟨⟨hp.1, hq.1⟩, ⟨hp.2, hq.2⟩⟩

end Vector

/-- Derivative of the norm away from zero. -/
theorem HasDerivAt.norm_of_ne_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f : ℝ → E} {f' : E} {x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x ≠ 0) :
    HasDerivAt (fun s ↦ ‖f s‖) (⟪f x, f'⟫_ℝ / ‖f x‖) x := by
  have hnorm : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hsqrt := hf.norm_sq.sqrt (pow_ne_zero 2 hnorm)
  convert! hsqrt using 1
  · ext s
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  · rw [Real.sqrt_sq (norm_nonneg _)]
    field_simp [hnorm]

/-- Derivative of the first norm derivative away from zero. -/
theorem HasDerivAt.norm_first_derivative {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f f' : ℝ → E} {f''x : E} {x : ℝ}
    (hf : HasDerivAt f (f' x) x) (hf' : HasDerivAt f' f''x x) (hne : f x ≠ 0) :
    HasDerivAt (fun s ↦ ⟪f s, f' s⟫_ℝ / ‖f s‖)
      ((⟪f' x, f' x⟫_ℝ + ⟪f x, f''x⟫_ℝ) / ‖f x‖ -
        ⟪f x, f' x⟫_ℝ ^ 2 / ‖f x‖ ^ 3) x := by
  have hnorm : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hn := hf.inner ℝ hf'
  have hd := HasDerivAt.norm_of_ne_zero hf hne
  convert! hn.div hd hnorm using 1
  field_simp [hnorm]
  ring

end Bescovitch.WeightedMixedEqualityLocal
