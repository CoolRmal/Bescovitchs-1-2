/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.BernsteinPass
public import Bescovitch.Certificates.RawDensePolynomial

/-!
# Bernstein conversion for raw dense polynomials

The raw conversion performs the same coordinate pass as its rational counterpart without
normalizing rational coefficients. Its interpretation theorem is the semantic bridge used by
materialized certificates.
-/

@[expose] public section

namespace Bescovitch.RawDensePolynomial

private theorem Coefficients.interpret_get {n : ℕ} (coefficients : Coefficients n) (k : ℕ) :
    RawDensePolynomial.interpret (coefficients.get (zero n) k) =
      (Coefficients.interpret RawDensePolynomial.interpret coefficients).get
        (MultivariateDensePolynomial.zero n) k := by
  induction coefficients using Coefficients.recList generalizing k with
  | nil =>
      rw [Coefficients.get]
      rw [Coefficients.interpret.eq_1,
        MultivariateDensePolynomial.Coefficients.get]
      exact interpret_zero n
  | cons p ps ih =>
      cases k with
      | zero => rfl
      | succ k =>
          rw [Coefficients.get, Coefficients.interpret.eq_2,
            MultivariateDensePolynomial.Coefficients.get, ih]

/-- Convert raw coefficients of degree at most two to centered Bernstein coefficients. -/
private def centeredBernsteinQuadratic {n : ℕ} (p : Coefficients n) : Coefficients n :=
  let p₀ := p.get (zero n) 0
  let p₁ := p.get (zero n) 1
  let p₂ := p.get (zero n) 2
  .cons (add n (add n p₀ (neg n p₁)) p₂)
    (.cons (add n p₀ (neg n p₂))
      (.cons (add n (add n p₀ p₁) p₂) .nil))

/-- Convert raw coefficients of degree at most four to centered Bernstein coefficients. -/
private def centeredBernsteinQuartic {n : ℕ} (p : Coefficients n) : Coefficients n :=
  let p₀ := p.get (zero n) 0
  let p₁ := p.get (zero n) 1
  let p₂ := p.get (zero n) 2
  let p₃ := p.get (zero n) 3
  let p₄ := p.get (zero n) 4
  .cons (add n (add n (add n (add n p₀ (neg n p₁)) p₂) (neg n p₃)) p₄)
    (.cons (add n (add n (add n p₀ (scale (RawRat.ofRat (-1 / 2)) n p₁))
        (scale (RawRat.ofRat (1 / 2)) n p₃)) (neg n p₄))
      (.cons (add n (add n p₀ (scale (RawRat.ofRat (-1 / 3)) n p₂)) p₄)
        (.cons (add n (add n (add n p₀ (scale (RawRat.ofRat (1 / 2)) n p₁))
            (scale (RawRat.ofRat (-1 / 2)) n p₃)) (neg n p₄))
          (.cons (add n (add n (add n (add n p₀ p₁) p₂) p₃) p₄) .nil))))

/-- Convert one raw coefficient list using the specified supported degree. -/
private def centeredBernsteinCoefficients {n : ℕ} :
    MultivariateDensePolynomial.BernsteinDegree → Coefficients n → Coefficients n
  | .quadratic => centeredBernsteinQuadratic
  | .quartic => centeredBernsteinQuartic

private theorem interpret_centeredBernsteinQuadratic {n : ℕ} (p : Coefficients n) :
    Coefficients.interpret interpret (centeredBernsteinQuadratic p) =
      MultivariateDensePolynomial.centeredBernsteinQuadratic
        (Coefficients.interpret interpret p) := by
  unfold centeredBernsteinQuadratic
    MultivariateDensePolynomial.centeredBernsteinQuadratic
  simp only [Coefficients.interpret.eq_2, Coefficients.interpret.eq_1,
    interpret_add, interpret_neg, Coefficients.interpret_get]

private theorem interpret_centeredBernsteinQuartic {n : ℕ} (p : Coefficients n) :
    Coefficients.interpret interpret (centeredBernsteinQuartic p) =
      MultivariateDensePolynomial.centeredBernsteinQuartic
        (Coefficients.interpret interpret p) := by
  unfold centeredBernsteinQuartic
    MultivariateDensePolynomial.centeredBernsteinQuartic
  simp only [Coefficients.interpret.eq_2, Coefficients.interpret.eq_1,
    interpret_add, interpret_neg, interpret_scale, Coefficients.interpret_get,
    RawRat.interpret_ofRat]

private theorem interpret_centeredBernsteinCoefficients {n : ℕ}
    (degree : MultivariateDensePolynomial.BernsteinDegree) (p : Coefficients n) :
    Coefficients.interpret interpret (centeredBernsteinCoefficients degree p) =
      MultivariateDensePolynomial.centeredBernsteinCoefficients degree
        (Coefficients.interpret interpret p) := by
  cases degree with
  | quadratic => exact interpret_centeredBernsteinQuadratic p
  | quartic => exact interpret_centeredBernsteinQuartic p

/-- Apply raw centered Bernstein conversion in one coordinate. -/
def centeredBernsteinAt : {n : ℕ} → Fin n →
    MultivariateDensePolynomial.BernsteinDegree →
    RawDensePolynomial n → RawDensePolynomial n
  | _ + 1, i, degree, .ofCoefficients coefficients =>
      let converted := match degree with
        | .quadratic =>
            let p₀ := Coefficients.get (zero _) coefficients 0
            let p₁ := Coefficients.get (zero _) coefficients 1
            let p₂ := Coefficients.get (zero _) coefficients 2
            .cons (add _ (add _ p₀ (neg _ p₁)) p₂)
              (.cons (add _ p₀ (neg _ p₂))
                (.cons (add _ (add _ p₀ p₁) p₂) .nil))
        | .quartic =>
            let p₀ := Coefficients.get (zero _) coefficients 0
            let p₁ := Coefficients.get (zero _) coefficients 1
            let p₂ := Coefficients.get (zero _) coefficients 2
            let p₃ := Coefficients.get (zero _) coefficients 3
            let p₄ := Coefficients.get (zero _) coefficients 4
            .cons (add _ (add _ (add _ (add _ p₀ (neg _ p₁)) p₂) (neg _ p₃)) p₄)
              (.cons (add _ (add _ (add _ p₀ (scale (RawRat.ofRat (-1 / 2)) _ p₁))
                  (scale (RawRat.ofRat (1 / 2)) _ p₃)) (neg _ p₄))
                (.cons (add _ (add _ p₀ (scale (RawRat.ofRat (-1 / 3)) _ p₂)) p₄)
                  (.cons (add _ (add _ (add _ p₀
                      (scale (RawRat.ofRat (1 / 2)) _ p₁))
                    (scale (RawRat.ofRat (-1 / 2)) _ p₃)) (neg _ p₄))
                    (.cons (add _ (add _ (add _ (add _ p₀ p₁) p₂) p₃) p₄) .nil))))
      Fin.cases
        (.ofCoefficients converted)
        (fun j => .ofCoefficients
          (Coefficients.map (centeredBernsteinAt j degree) coefficients)) i

private theorem Coefficients.interpret_map {n : ℕ}
    (raw : RawDensePolynomial n → RawDensePolynomial n)
    (rational : MultivariateDensePolynomial n → MultivariateDensePolynomial n)
    (h : ∀ p, RawDensePolynomial.interpret (raw p) =
      rational (RawDensePolynomial.interpret p))
    (coefficients : Coefficients n) :
    Coefficients.interpret RawDensePolynomial.interpret
        (Coefficients.map raw coefficients) =
      MultivariateDensePolynomial.Coefficients.map rational
        (Coefficients.interpret RawDensePolynomial.interpret coefficients) := by
  induction coefficients using Coefficients.recList with
  | nil => rfl
  | cons p ps ih =>
      rw [Coefficients.map.eq_2, Coefficients.interpret.eq_2]
      simp only [Coefficients.interpret.eq_2]
      rw [MultivariateDensePolynomial.Coefficients.map.eq_2, h p, ih]

/-- Interpreting a raw coordinate pass gives the rational coordinate pass. -/
theorem interpret_centeredBernsteinAt {n : ℕ} (i : Fin n)
    (degree : MultivariateDensePolynomial.BernsteinDegree) (p : RawDensePolynomial n) :
    interpret (centeredBernsteinAt i degree p) =
      MultivariateDensePolynomial.rationalCenteredBernsteinAt i degree (interpret p) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases p with
      | ofCoefficients coefficients =>
        cases degree with
        | quadratic =>
            refine Fin.cases ?_ (fun j => ?_) i
            · simp only [centeredBernsteinAt, interpret,
                MultivariateDensePolynomial.rationalCenteredBernsteinAt, Fin.cases_zero]
              exact congrArg MultivariateDensePolynomial.ofCoefficients
                (interpret_centeredBernsteinQuadratic coefficients)
            · simp only [centeredBernsteinAt, interpret,
                MultivariateDensePolynomial.rationalCenteredBernsteinAt, Fin.cases_succ]
              exact congrArg MultivariateDensePolynomial.ofCoefficients
                (Coefficients.interpret_map _ _ (fun p => ih j p) coefficients)
        | quartic =>
            refine Fin.cases ?_ (fun j => ?_) i
            · simp only [centeredBernsteinAt, interpret,
                MultivariateDensePolynomial.rationalCenteredBernsteinAt, Fin.cases_zero]
              exact congrArg MultivariateDensePolynomial.ofCoefficients
                (interpret_centeredBernsteinQuartic coefficients)
            · simp only [centeredBernsteinAt, interpret,
                MultivariateDensePolynomial.rationalCenteredBernsteinAt, Fin.cases_succ]
              exact congrArg MultivariateDensePolynomial.ofCoefficients
                (Coefficients.interpret_map _ _ (fun p => ih j p) coefficients)

end Bescovitch.RawDensePolynomial
