/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.IntervalBernstein
public import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# Bernstein certificates for normalized bivariate polynomials

The two geometric variables are normalized in `MvPolynomial`, while the coefficients remain
polynomials in exact rational atoms. This removes algebraically zero high-degree terms before
interval arithmetic is applied. The checker uses the `16 × 8` padded Bernstein rectangle needed
by the exceptional weighted-self chart.
-/

@[expose] public section

noncomputable section

open scoped BigOperators unitInterval

namespace Bescovitch

/-- A normalized bivariate polynomial whose coefficients are rational polynomials in atoms. -/
abbrev NormalizedBivariatePolynomial (atomCount : ℕ) :=
  MvPolynomial (Fin 2) (MvPolynomial (Fin atomCount) ℚ)

namespace NormalizedBivariatePolynomial

private abbrev AtomPolynomial (atomCount : ℕ) := MvPolynomial (Fin atomCount) ℚ

private def atomEvaluation {atomCount : ℕ} (input : Fin atomCount → ℝ) :
    AtomPolynomial atomCount →+* ℝ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) input

/-- Evaluate a normalized bivariate polynomial at its atoms and two geometric coordinates. -/
def eval {atomCount : ℕ} (p : NormalizedBivariatePolynomial atomCount)
    (input : Fin atomCount → ℝ) (u v : ℝ) : ℝ :=
  MvPolynomial.eval₂ (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) input)
    (![u, v] : Fin 2 → ℝ) p

private def outerPolynomial {atomCount : ℕ}
    (p : NormalizedBivariatePolynomial atomCount) :
    Polynomial (MvPolynomial (Fin 1) (AtomPolynomial atomCount)) :=
  MvPolynomial.finSuccEquiv (AtomPolynomial atomCount) 1 p

private def innerPolynomial {atomCount : ℕ}
    (p : NormalizedBivariatePolynomial atomCount) (i : ℕ) :
    Polynomial (AtomPolynomial atomCount) :=
  Polynomial.map
    (MvPolynomial.isEmptyRingEquiv (AtomPolynomial atomCount) (Fin 0)).toRingHom
    (MvPolynomial.finSuccEquiv (AtomPolynomial atomCount) 0
      ((outerPolynomial p).coeff i))

private def coefficient {atomCount : ℕ}
    (p : NormalizedBivariatePolynomial atomCount) (i j : ℕ) :
    AtomPolynomial atomCount :=
  (innerPolynomial p i).coeff j

/-- The exact power coefficient after evaluating the rational atom polynomial. -/
def powerCoefficient {atomCount : ℕ}
    (p : NormalizedBivariatePolynomial atomCount) (input : Fin atomCount → ℝ)
    (i : Fin 17) (j : Fin 9) : ℝ :=
  let outer := MvPolynomial.finSuccEquiv (MvPolynomial (Fin atomCount) ℚ) 1 p
  let inner := Polynomial.map
    (MvPolynomial.isEmptyRingEquiv (MvPolynomial (Fin atomCount) ℚ) (Fin 0)).toRingHom
    (MvPolynomial.finSuccEquiv (MvPolynomial (Fin atomCount) ℚ) 0
      (outer.coeff i))
  MvPolynomial.eval₂ (algebraMap ℚ ℝ) input (inner.coeff j)

/-- The normalized polynomial has no powers beyond the padded `16 × 8` rectangle. -/
def FitsCertificateRectangle {atomCount : ℕ}
    (p : NormalizedBivariatePolynomial atomCount) : Prop :=
  let outer := MvPolynomial.finSuccEquiv (MvPolynomial (Fin atomCount) ℚ) 1 p
  outer.natDegree ≤ 16 ∧ ∀ i : Fin 17,
    (Polynomial.map
      (MvPolynomial.isEmptyRingEquiv (MvPolynomial (Fin atomCount) ℚ) (Fin 0)).toRingHom
      (MvPolynomial.finSuccEquiv (MvPolynomial (Fin atomCount) ℚ) 0
        (outer.coeff i))).natDegree ≤ 8

/-- The exact coefficient in the padded bivariate Bernstein basis. -/
def bernsteinCoefficient {atomCount : ℕ}
    (p : NormalizedBivariatePolynomial atomCount) (input : Fin atomCount → ℝ)
    (i : Fin 17) (j : Fin 9) : ℝ :=
  powerToBernstein 8
    (fun j' ↦ powerToBernstein 16 (fun i' ↦ powerCoefficient p input i' j') i) j

private theorem eval_finSucc {R S : Type*} [CommSemiring R] [CommSemiring S]
    {n : ℕ} (f : R →+* S) (x₀ : S) (xs : Fin n → S)
    (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.eval₂ f (Fin.cases x₀ xs) p =
      Polynomial.eval₂ (MvPolynomial.eval₂Hom f xs) x₀
        (MvPolynomial.finSuccEquiv R n p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.finSuccEquiv_apply]
      simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [MvPolynomial.eval₂_mul, map_mul, Polynomial.eval₂_mul, hp]
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rw [MvPolynomial.finSuccEquiv_X_zero]
        simp
      · rw [MvPolynomial.finSuccEquiv_X_succ]
        simp

private theorem eval_eq_nested {atomCount : ℕ}
    (p : NormalizedBivariatePolynomial atomCount)
    (input : Fin atomCount → ℝ) (u v : ℝ) :
    eval p input u v =
      Polynomial.eval₂
        (MvPolynomial.eval₂Hom (atomEvaluation input) (![v] : Fin 1 → ℝ)) u
        (outerPolynomial p) := by
  have hcoordinates : (![u, v] : Fin 2 → ℝ) = Fin.cases u ![v] := by
    funext i
    fin_cases i <;> rfl
  rw [eval, hcoordinates, outerPolynomial]
  exact eval_finSucc (atomEvaluation input) u (![v] : Fin 1 → ℝ) p

private theorem eval_inner {atomCount : ℕ}
    (p : NormalizedBivariatePolynomial atomCount) (i : ℕ)
    (input : Fin atomCount → ℝ) (v : ℝ) :
    MvPolynomial.eval₂ (atomEvaluation input) (![v] : Fin 1 → ℝ)
        ((outerPolynomial p).coeff i) =
      Polynomial.eval₂ (atomEvaluation input) v (innerPolynomial p i) := by
  have h := eval_finSucc (atomEvaluation input) v (fun j : Fin 0 ↦ nomatch j)
    ((outerPolynomial p).coeff i)
  rw [show MvPolynomial.eval₂ (atomEvaluation input) (![v] : Fin 1 → ℝ)
      ((outerPolynomial p).coeff i) =
      MvPolynomial.eval₂ (atomEvaluation input)
        (Fin.cases v (fun j : Fin 0 ↦ nomatch j))
        ((outerPolynomial p).coeff i) by
        congr 2
        funext j
        fin_cases j]
  rw [h, innerPolynomial, Polynomial.eval₂_map]
  congr 2
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change atomEvaluation input a = atomEvaluation input
      (MvPolynomial.isEmptyRingEquiv (AtomPolynomial atomCount) (Fin 0)
        (MvPolynomial.C a))
    rw [MvPolynomial.isEmptyRingEquiv_eq_coeff_zero, MvPolynomial.coeff_zero_C]
  · intro j
    exact Fin.elim0 j

private def powerEval (degreeFirst degreeSecond : ℕ)
    (a : Fin (degreeFirst + 1) → Fin (degreeSecond + 1) → ℝ)
    (u v : ℝ) : ℝ :=
  ∑ i, ∑ j, a i j * u ^ (i : ℕ) * v ^ (j : ℕ)

private theorem eval_eq_powerEval {atomCount : ℕ}
    {p : NormalizedBivariatePolynomial atomCount}
    (hfits : FitsCertificateRectangle p)
    (input : Fin atomCount → ℝ) (u v : ℝ) :
    eval p input u v =
      powerEval 16 8
        (fun i j ↦ atomEvaluation input (coefficient p i j)) u v := by
  change (outerPolynomial p).natDegree ≤ 16 ∧
      ∀ i : Fin 17, (innerPolynomial p i).natDegree ≤ 8 at hfits
  rw [eval_eq_nested]
  rw [Polynomial.eval₂_eq_sum_range'
    (MvPolynomial.eval₂Hom (atomEvaluation input) (![v] : Fin 1 → ℝ))
    (Nat.lt_succ_of_le hfits.1)]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold powerEval
  apply Finset.sum_congr rfl
  intro i hi
  change MvPolynomial.eval₂ (atomEvaluation input) (![v] : Fin 1 → ℝ)
      ((outerPolynomial p).coeff i) * u ^ (i : ℕ) = _
  rw [eval_inner]
  rw [Polynomial.eval₂_eq_sum_range' (atomEvaluation input)
    (Nat.lt_succ_of_le (hfits.2 i))]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold coefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private def powerToBivariateBernstein (degreeFirst degreeSecond : ℕ)
    (a : Fin (degreeFirst + 1) → Fin (degreeSecond + 1) → ℝ)
    (i : Fin (degreeFirst + 1)) (j : Fin (degreeSecond + 1)) : ℝ :=
  powerToBernstein degreeSecond
    (fun j' ↦ powerToBernstein degreeFirst (fun i' ↦ a i' j') i) j

private def bivariateBernstein (degreeFirst degreeSecond : ℕ)
    (a : Fin (degreeFirst + 1) → Fin (degreeSecond + 1) → ℝ)
    (u v : I) : ℝ :=
  ∑ i, ∑ j, a i j * bernstein degreeFirst i u * bernstein degreeSecond j v

private theorem powerToBernstein_finSum (degree N : ℕ)
    (a : Fin N → Fin (degree + 1) → ℝ) (i : Fin (degree + 1)) :
    powerToBernstein degree (fun j ↦ ∑ k, a k j) i =
      ∑ k, powerToBernstein degree (a k) i := by
  unfold powerToBernstein
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · rw [Finset.sum_mul]
  · simp

private theorem powerToBernstein_mul (degree : ℕ)
    (a : Fin (degree + 1) → ℝ) (c : ℝ) (i : Fin (degree + 1)) :
    powerToBernstein degree (fun j ↦ a j * c) i =
      powerToBernstein degree a i * c := by
  unfold powerToBernstein
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

private theorem powerEval_eq_bivariateBernstein (degreeFirst degreeSecond : ℕ)
    (a : Fin (degreeFirst + 1) → Fin (degreeSecond + 1) → ℝ) (u v : I) :
    powerEval degreeFirst degreeSecond a u v =
      bivariateBernstein degreeFirst degreeSecond
        (powerToBivariateBernstein degreeFirst degreeSecond a) u v := by
  unfold powerEval bivariateBernstein powerToBivariateBernstein
  calc
    (∑ i, ∑ j, a i j * (u : ℝ) ^ (i : ℕ) * (v : ℝ) ^ (j : ℕ)) =
        ∑ j, (∑ i, a i j * (u : ℝ) ^ (i : ℕ)) * (v : ℝ) ^ (j : ℕ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ = ∑ j, (∑ i, powerToBernstein degreeFirst (fun i' ↦ a i' j) i *
          bernstein degreeFirst i u) * (v : ℝ) ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show (∑ i, a i j * (u : ℝ) ^ (i : ℕ)) =
          ∑ i, powerToBernstein degreeFirst (fun i' ↦ a i' j) i *
            bernstein degreeFirst i u by
        simpa [paddedPowerEval] using
          paddedPowerEval_eq_bernstein_sum degreeFirst (fun i ↦ a i j) u]
    _ = ∑ j, powerToBernstein degreeSecond
          (fun j' ↦ ∑ i, powerToBernstein degreeFirst (fun i' ↦ a i' j') i *
            bernstein degreeFirst i u) j * bernstein degreeSecond j v := by
      simpa [paddedPowerEval] using
        paddedPowerEval_eq_bernstein_sum degreeSecond
          (fun j ↦ ∑ i, powerToBernstein degreeFirst (fun i' ↦ a i' j) i *
            bernstein degreeFirst i u) v
    _ = ∑ i, ∑ j, powerToBernstein degreeSecond
          (fun j' ↦ powerToBernstein degreeFirst (fun i' ↦ a i' j') i) j *
          bernstein degreeFirst i u * bernstein degreeSecond j v := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [powerToBernstein_finSum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [powerToBernstein_mul]

private theorem bivariateBernstein_nonneg {degreeFirst degreeSecond : ℕ}
    {a : Fin (degreeFirst + 1) → Fin (degreeSecond + 1) → ℝ}
    (ha : ∀ i j, 0 ≤ a i j) (u v : I) :
    0 ≤ bivariateBernstein degreeFirst degreeSecond a u v := by
  unfold bivariateBernstein
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (mul_nonneg (ha i j) bernstein_nonneg) bernstein_nonneg

/-- Interval data representing every coefficient in the padded Bernstein rectangle. -/
structure BernsteinCertificate {atomCount : ℕ}
    (box : Fin atomCount → RationalInterval)
    (p : NormalizedBivariatePolynomial atomCount) where
  /-- Rational intervals containing the exact Bernstein coefficients. -/
  coefficients : Fin 17 → Fin 9 → RationalInterval
  /-- The normalized polynomial fits in the padded rectangle. -/
  fits : FitsCertificateRectangle p
  /-- Every interval uniformly contains its coefficient over the atom box. -/
  contains : ∀ input, (∀ k, (box k).Contains (input k)) → ∀ i j,
    (coefficients i j).Contains (bernsteinCoefficient p input i j)

/-- Check the lower endpoints of a normalized bivariate Bernstein certificate. -/
def BernsteinCertificate.certifiesNonnegative {atomCount : ℕ}
    {box : Fin atomCount → RationalInterval}
    {p : NormalizedBivariatePolynomial atomCount}
    (certificate : BernsteinCertificate box p) : Bool :=
  decide (∀ i j, 0 ≤ (certificate.coefficients i j).lower)

/-- A successful normalized Bernstein certificate proves nonnegativity on the unit square. -/
theorem nonnegative_of_certificate {atomCount : ℕ}
    {box : Fin atomCount → RationalInterval}
    {p : NormalizedBivariatePolynomial atomCount}
    (certificate : BernsteinCertificate box p) {input : Fin atomCount → ℝ}
    (hinput : ∀ i, (box i).Contains (input i))
    (hcertificate : certificate.certifiesNonnegative = true) (u v : I) :
    0 ≤ eval p input u v := by
  have hlower : ∀ i j, 0 ≤ (certificate.coefficients i j).lower :=
    of_decide_eq_true hcertificate
  have hcoeff : ∀ i j, 0 ≤ bernsteinCoefficient p input i j := by
    intro i j
    have hcontains := certificate.contains input hinput i j
    have hlowerReal : (0 : ℝ) ≤ (certificate.coefficients i j).lower := by
      exact_mod_cast hlower i j
    exact hlowerReal.trans hcontains.1
  have hpower : ∀ i j,
      powerCoefficient p input i j = atomEvaluation input (coefficient p i j) := by
    intro i j
    rfl
  have hbernstein : ∀ i j, bernsteinCoefficient p input i j =
      powerToBivariateBernstein 16 8
        (fun i j ↦ atomEvaluation input (coefficient p i j)) i j := by
    intro i j
    simp only [bernsteinCoefficient, powerToBivariateBernstein, hpower]
  rw [eval_eq_powerEval certificate.fits input u v,
    powerEval_eq_bivariateBernstein]
  apply bivariateBernstein_nonneg
  intro i j
  rw [← hbernstein]
  exact hcoeff i j

end NormalizedBivariatePolynomial

end Bescovitch
