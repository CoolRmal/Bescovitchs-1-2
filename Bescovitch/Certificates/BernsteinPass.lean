/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.MultivariateDensePolynomial

/-!
# Coordinatewise Bernstein conversion

This file expresses centered Bernstein conversion as one pass per coordinate.
The six-coordinate theorem lets certificates materialize those passes separately.
-/

@[expose] public section

namespace Bescovitch.MultivariateDensePolynomial

/-- Apply centered Bernstein conversion in one chosen coordinate. -/
def rationalCenteredBernsteinAt : {n : ℕ} → Fin n → BernsteinDegree →
    MultivariateDensePolynomial n → MultivariateDensePolynomial n
  | _ + 1, i, degree, .ofCoefficients coefficients =>
      Fin.cases
        (.ofCoefficients (centeredBernsteinCoefficients degree coefficients))
        (fun j => .ofCoefficients
          (Coefficients.map (rationalCenteredBernsteinAt j degree) coefficients)) i

private theorem Coefficients.map_map {n : ℕ}
    (f g : MultivariateDensePolynomial n → MultivariateDensePolynomial n)
    (coefficients : Coefficients n) :
    Coefficients.map f (Coefficients.map g coefficients) =
      Coefficients.map (fun p => f (g p)) coefficients := by
  induction coefficients using Coefficients.recList with
  | nil => rfl
  | cons p ps ih =>
      simp only [Coefficients.map]
      rw [ih]

private theorem Coefficients.map_id {n : ℕ} (coefficients : Coefficients n) :
    Coefficients.map id coefficients = coefficients := by
  induction coefficients using Coefficients.recList with
  | nil => rfl
  | cons p ps ih =>
      simp only [Coefficients.map, id_eq]
      rw [ih]

private theorem Coefficients.map_congr {n : ℕ}
    {f g : MultivariateDensePolynomial n → MultivariateDensePolynomial n}
    (h : ∀ p, f p = g p) (coefficients : Coefficients n) :
    Coefficients.map f coefficients = Coefficients.map g coefficients := by
  induction coefficients using Coefficients.recList with
  | nil => rfl
  | cons p ps ih =>
      simp only [Coefficients.map]
      rw [h p, ih]

/-- Apply a polynomial transformation below the outermost coordinate. -/
private def lift {n : ℕ}
    (f : MultivariateDensePolynomial n → MultivariateDensePolynomial n) :
    MultivariateDensePolynomial (n + 1) → MultivariateDensePolynomial (n + 1)
  | .ofCoefficients coefficients => .ofCoefficients (Coefficients.map f coefficients)

private theorem lift_id {n : ℕ} (p : MultivariateDensePolynomial (n + 1)) :
    lift id p = p := by
  cases p with
  | ofCoefficients coefficients =>
      rw [lift]
      congr 1
      exact Coefficients.map_id coefficients

private theorem lift_comp {n : ℕ}
    (f g : MultivariateDensePolynomial n → MultivariateDensePolynomial n)
    (p : MultivariateDensePolynomial (n + 1)) :
    lift f (lift g p) = lift (fun q => f (g q)) p := by
  cases p with
  | ofCoefficients coefficients =>
      simp only [lift]
      rw [Coefficients.map_map]

private theorem lift_congr {n : ℕ}
    {f g : MultivariateDensePolynomial n → MultivariateDensePolynomial n}
    (h : ∀ p, f p = g p) (p : MultivariateDensePolynomial (n + 1)) :
    lift f p = lift g p := by
  cases p with
  | ofCoefficients coefficients =>
      simp only [lift]
      congr 1
      exact Coefficients.map_congr h coefficients

private theorem rationalCenteredBernsteinAt_succ {n : ℕ} (i : Fin n)
    (degree : BernsteinDegree) (p : MultivariateDensePolynomial (n + 1)) :
    rationalCenteredBernsteinAt i.succ degree p =
      lift (rationalCenteredBernsteinAt i degree) p := by
  cases p
  rfl

private theorem centeredBernstein_eq_at_zero_lift {n : ℕ}
    (degrees : Fin (n + 1) → BernsteinDegree)
    (p : MultivariateDensePolynomial (n + 1)) :
    centeredBernstein degrees p =
      rationalCenteredBernsteinAt 0 (degrees 0)
        (lift (centeredBernstein (Fin.tail degrees)) p) := by
  cases p
  rfl

private theorem rationalCenteredBernsteinAt_one (d₀ : BernsteinDegree)
    (p : MultivariateDensePolynomial 1) :
    rationalCenteredBernsteinAt 0 d₀ p =
      centeredBernstein (fun _ => d₀) p := by
  rw [centeredBernstein_eq_at_zero_lift]
  congr 1
  symm
  calc
    lift (centeredBernstein (Fin.tail fun _ => d₀)) p = lift id p := by
      apply lift_congr
      intro q
      cases q
      rfl
    _ = p := lift_id p

private theorem rationalCenteredBernsteinAt_two (d₀ d₁ : BernsteinDegree)
    (p : MultivariateDensePolynomial 2) :
    rationalCenteredBernsteinAt 0 d₀
      (rationalCenteredBernsteinAt 1 d₁ p) =
      centeredBernstein (fun i => Fin.cases d₀ (fun _ => d₁) i) p := by
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by rfl,
    rationalCenteredBernsteinAt_succ, centeredBernstein_eq_at_zero_lift]
  congr 1
  apply lift_congr
  intro q
  convert rationalCenteredBernsteinAt_one d₁ q using 1
  congr 1

private theorem rationalCenteredBernsteinAt_three (d₀ d₁ d₂ : BernsteinDegree)
    (p : MultivariateDensePolynomial 3) :
    rationalCenteredBernsteinAt 0 d₀
      (rationalCenteredBernsteinAt 1 d₁
        (rationalCenteredBernsteinAt 2 d₂ p)) =
      centeredBernstein
        (fun i => Fin.cases d₀ (fun j => Fin.cases d₁ (fun _ => d₂) j) i) p := by
  rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) by rfl,
    rationalCenteredBernsteinAt_succ,
    show (1 : Fin 3) = Fin.succ (0 : Fin 2) by rfl,
    rationalCenteredBernsteinAt_succ, lift_comp,
    centeredBernstein_eq_at_zero_lift]
  congr 1
  apply lift_congr
  intro q
  convert rationalCenteredBernsteinAt_two d₁ d₂ q using 1
  congr 1

private theorem rationalCenteredBernsteinAt_four (d₀ d₁ d₂ d₃ : BernsteinDegree)
    (p : MultivariateDensePolynomial 4) :
    rationalCenteredBernsteinAt 0 d₀
      (rationalCenteredBernsteinAt 1 d₁
        (rationalCenteredBernsteinAt 2 d₂
          (rationalCenteredBernsteinAt 3 d₃ p))) =
      centeredBernstein
        (fun i => Fin.cases d₀ (fun i => Fin.cases d₁
          (fun i => Fin.cases d₂ (fun _ => d₃) i) i) i) p := by
  rw [show (3 : Fin 4) = Fin.succ (2 : Fin 3) by rfl,
    rationalCenteredBernsteinAt_succ,
    show (2 : Fin 4) = Fin.succ (1 : Fin 3) by rfl,
    rationalCenteredBernsteinAt_succ, lift_comp,
    show (1 : Fin 4) = Fin.succ (0 : Fin 3) by rfl,
    rationalCenteredBernsteinAt_succ, lift_comp,
    centeredBernstein_eq_at_zero_lift]
  congr 1
  apply lift_congr
  intro q
  convert rationalCenteredBernsteinAt_three d₁ d₂ d₃ q using 1
  congr 1

private theorem rationalCenteredBernsteinAt_five
    (d₀ d₁ d₂ d₃ d₄ : BernsteinDegree)
    (p : MultivariateDensePolynomial 5) :
    rationalCenteredBernsteinAt 0 d₀
      (rationalCenteredBernsteinAt 1 d₁
        (rationalCenteredBernsteinAt 2 d₂
          (rationalCenteredBernsteinAt 3 d₃
            (rationalCenteredBernsteinAt 4 d₄ p)))) =
      centeredBernstein
        (fun i => Fin.cases d₀ (fun i => Fin.cases d₁
          (fun i => Fin.cases d₂
            (fun i => Fin.cases d₃ (fun _ => d₄) i) i) i) i) p := by
  rw [show (4 : Fin 5) = Fin.succ (3 : Fin 4) by rfl,
    rationalCenteredBernsteinAt_succ,
    show (3 : Fin 5) = Fin.succ (2 : Fin 4) by rfl,
    rationalCenteredBernsteinAt_succ, lift_comp,
    show (2 : Fin 5) = Fin.succ (1 : Fin 4) by rfl,
    rationalCenteredBernsteinAt_succ, lift_comp,
    show (1 : Fin 5) = Fin.succ (0 : Fin 4) by rfl,
    rationalCenteredBernsteinAt_succ, lift_comp,
    centeredBernstein_eq_at_zero_lift]
  congr 1
  apply lift_congr
  intro q
  convert rationalCenteredBernsteinAt_four d₁ d₂ d₃ d₄ q using 1
  congr 1

/-- Six coordinate passes equal the recursive six-dimensional conversion. -/
theorem rationalCenteredBernsteinAt_six
    (d₀ d₁ d₂ d₃ d₄ d₅ : BernsteinDegree)
    (p : MultivariateDensePolynomial 6) :
    rationalCenteredBernsteinAt 0 d₀
      (rationalCenteredBernsteinAt 1 d₁
        (rationalCenteredBernsteinAt 2 d₂
          (rationalCenteredBernsteinAt 3 d₃
            (rationalCenteredBernsteinAt 4 d₄
              (rationalCenteredBernsteinAt 5 d₅ p))))) =
      centeredBernstein
        (fun i => Fin.cases d₀ (fun i => Fin.cases d₁
          (fun i => Fin.cases d₂ (fun i => Fin.cases d₃
            (fun i => Fin.cases d₄ (fun _ => d₅) i) i) i) i) i) p := by
  rw [show (5 : Fin 6) = Fin.succ (4 : Fin 5) by rfl,
    rationalCenteredBernsteinAt_succ,
    show (4 : Fin 6) = Fin.succ (3 : Fin 5) by rfl,
    rationalCenteredBernsteinAt_succ, lift_comp,
    show (3 : Fin 6) = Fin.succ (2 : Fin 5) by rfl,
    rationalCenteredBernsteinAt_succ, lift_comp,
    show (2 : Fin 6) = Fin.succ (1 : Fin 5) by rfl,
    rationalCenteredBernsteinAt_succ, lift_comp,
    show (1 : Fin 6) = Fin.succ (0 : Fin 5) by rfl,
    rationalCenteredBernsteinAt_succ, lift_comp,
    centeredBernstein_eq_at_zero_lift]
  congr 1
  apply lift_congr
  intro q
  convert rationalCenteredBernsteinAt_five d₁ d₂ d₃ d₄ d₅ q using 1
  congr 1

end Bescovitch.MultivariateDensePolynomial
