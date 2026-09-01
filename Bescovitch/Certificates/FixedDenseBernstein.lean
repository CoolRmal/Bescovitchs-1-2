/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.BernsteinPass
public import Bescovitch.Certificates.FixedDensePolynomial

/-!
# Fixed-width centered Bernstein conversion

This module evaluates the quadratic and quartic centered Bernstein passes with guarded
fixed-width dyadic intervals.  It also provides Boolean checks for separately materialized
coordinate passes and relates every successful computation to the exact rational pass.
-/

@[expose] public section

namespace Bescovitch.FixedDensePolynomial

variable {width precision : ℕ}

/-- Convert a quadratic centered-power coefficient sequence to Bernstein coefficients. -/
def centeredBernsteinQuadratic {n : ℕ}
    (coefficients : Coefficients width precision n) : Coefficients width precision n :=
  let p₀ := coefficients.get (zero width precision n) 0
  let p₁ := coefficients.get (zero width precision n) 1
  let p₂ := coefficients.get (zero width precision n) 2
  .cons (add n (add n p₀ (neg n p₁)) p₂)
    (.cons (add n p₀ (neg n p₂))
      (.cons (add n (add n p₀ p₁) p₂) .nil))

/-- Convert a quartic centered-power coefficient sequence to Bernstein coefficients. -/
def centeredBernsteinQuartic {n : ℕ}
    (coefficients : Coefficients width precision n) : Coefficients width precision n :=
  let p₀ := coefficients.get (zero width precision n) 0
  let p₁ := coefficients.get (zero width precision n) 1
  let p₂ := coefficients.get (zero width precision n) 2
  let p₃ := coefficients.get (zero width precision n) 3
  let p₄ := coefficients.get (zero width precision n) 4
  .cons (add n (add n (add n (add n p₀ (neg n p₁)) p₂) (neg n p₃)) p₄)
    (.cons (add n (add n (add n p₀ (scale (-1 / 2) n p₁))
        (scale (1 / 2) n p₃)) (neg n p₄))
      (.cons (add n (add n p₀ (scale (-1 / 3) n p₂)) p₄)
        (.cons (add n (add n (add n p₀ (scale (1 / 2) n p₁))
            (scale (-1 / 2) n p₃)) (neg n p₄))
          (.cons (add n (add n (add n (add n p₀ p₁) p₂) p₃) p₄) .nil))))

/-- Convert one outer coefficient sequence at its prescribed Bernstein degree. -/
def centeredBernsteinCoefficients {n : ℕ} :
    MultivariateDensePolynomial.BernsteinDegree →
      Coefficients width precision n → Coefficients width precision n
  | .quadratic => centeredBernsteinQuadratic
  | .quartic => centeredBernsteinQuartic

/-- Apply centered Bernstein conversion in one chosen coordinate. -/
def centeredBernsteinAt : {n : ℕ} → Fin n →
    MultivariateDensePolynomial.BernsteinDegree →
      FixedDensePolynomial width precision n → FixedDensePolynomial width precision n
  | _ + 1, index, degree, .ofCoefficients coefficients =>
      Fin.cases
        (.ofCoefficients (centeredBernsteinCoefficients degree coefficients))
        (fun inner ↦ .ofCoefficients
          (Coefficients.map (centeredBernsteinAt inner degree) coefficients)) index

/-- Convert every coordinate of a fixed dense polynomial to the centered Bernstein basis. -/
def centeredBernstein : {n : ℕ} →
    (Fin n → MultivariateDensePolynomial.BernsteinDegree) →
      FixedDensePolynomial width precision n → FixedDensePolynomial width precision n
  | 0, _, .base value => .base value
  | _ + 1, degrees, .ofCoefficients coefficients =>
      .ofCoefficients (centeredBernsteinCoefficients (degrees 0)
        (Coefficients.map (centeredBernstein (Fin.tail degrees)) coefficients))

mutual

/-- Boolean structural equality for fixed dense polynomials. -/
def equal : {n : ℕ} → FixedDensePolynomial width precision n →
    FixedDensePolynomial width precision n → Bool
  | 0, .base left, .base right =>
      (left.lower == right.lower) && (left.upper == right.upper) && (left.ok == right.ok)
  | _ + 1, .ofCoefficients left, .ofCoefficients right => Coefficients.equal left right

/-- Boolean structural equality for fixed coefficient sequences. -/
def Coefficients.equal : {n : ℕ} → Coefficients width precision n →
    Coefficients width precision n → Bool
  | _, .nil, .nil => true
  | _, .nil, .cons _ _ => false
  | _, .cons _ _, .nil => false
  | _, .cons left lefts, .cons right rights =>
      equal left right && Coefficients.equal lefts rights

end

mutual

/-- Successful structural equality identifies the two fixed polynomials. -/
theorem equal_sound {n : ℕ} {left right : FixedDensePolynomial width precision n}
    (h : equal left right = true) : left = right := by
  cases n with
  | zero =>
      cases left with
      | base left =>
          cases right with
          | base right =>
              cases left with
              | mk leftLower leftUpper leftOk leftOrdered =>
                  cases right with
                  | mk rightLower rightUpper rightOk rightOrdered =>
                      simp only [equal, Bool.and_eq_true, beq_iff_eq] at h
                      cases h.1.1
                      cases h.1.2
                      cases h.2
                      rfl
  | succ n =>
      cases left with
      | ofCoefficients left =>
          cases right with
          | ofCoefficients right =>
              simp only [equal] at h
              rw [Coefficients.equal_sound h]

/-- Successful structural equality identifies the two fixed coefficient sequences. -/
theorem Coefficients.equal_sound {n : ℕ}
    {left right : Coefficients width precision n}
    (h : Coefficients.equal left right = true) : left = right := by
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons => simp [Coefficients.equal] at h
  | cons left lefts =>
      cases right with
      | nil => simp [Coefficients.equal] at h
      | cons right rights =>
          simp only [Coefficients.equal, Bool.and_eq_true] at h
          rw [equal_sound h.1, Coefficients.equal_sound h.2]

end


mutual

/-- Check a separately materialized coordinate pass without recomputing its whole output. -/
def centeredBernsteinCheck : {n : ℕ} → Fin n →
    MultivariateDensePolynomial.BernsteinDegree → FixedDensePolynomial width precision n →
      FixedDensePolynomial width precision n → Bool
  | _ + 1, index, degree, .ofCoefficients input, .ofCoefficients output =>
      Fin.cases
        (Coefficients.equal (centeredBernsteinCoefficients degree input) output)
        (fun inner ↦ Coefficients.centeredBernsteinCheck inner degree input output) index

/-- Check a materialized coordinate pass coefficient by coefficient. -/
def Coefficients.centeredBernsteinCheck {n : ℕ} (index : Fin n)
    (degree : MultivariateDensePolynomial.BernsteinDegree) :
    Coefficients width precision n → Coefficients width precision n → Bool
  | .nil, .nil => true
  | .nil, .cons _ _ => false
  | .cons _ _, .nil => false
  | .cons input inputTail, .cons output outputTail =>
      centeredBernsteinCheck index degree input output &&
        Coefficients.centeredBernsteinCheck index degree inputTail outputTail

end

mutual

/-- A successful materialized check reconstructs the computed coordinate pass. -/
theorem centeredBernsteinCheck_sound {n : ℕ} {index : Fin n}
    {degree : MultivariateDensePolynomial.BernsteinDegree}
    {input output : FixedDensePolynomial width precision n}
    (h : centeredBernsteinCheck index degree input output = true) :
    centeredBernsteinAt index degree input = output := by
  cases n with
  | zero => exact Fin.elim0 index
  | succ n =>
      cases input with
      | ofCoefficients input =>
          cases output with
          | ofCoefficients output =>
              cases index using Fin.cases with
              | zero =>
                  simp only [centeredBernsteinCheck, centeredBernsteinAt,
                    Fin.cases_zero] at h ⊢
                  rw [Coefficients.equal_sound h]
              | succ inner =>
                  simp only [centeredBernsteinCheck, centeredBernsteinAt,
                    Fin.cases_succ] at h ⊢
                  rw [Coefficients.centeredBernsteinCheck_sound h]

/-- A successful coefficient check reconstructs the mapped coordinate pass. -/
theorem Coefficients.centeredBernsteinCheck_sound {n : ℕ} {index : Fin n}
    {degree : MultivariateDensePolynomial.BernsteinDegree}
    {input output : Coefficients width precision n}
    (h : Coefficients.centeredBernsteinCheck index degree input output = true) :
    Coefficients.map (centeredBernsteinAt index degree) input = output := by
  cases input with
  | nil =>
      cases output with
      | nil => rfl
      | cons => simp [Coefficients.centeredBernsteinCheck] at h
  | cons input inputTail =>
      cases output with
      | nil => simp [Coefficients.centeredBernsteinCheck] at h
      | cons output outputTail =>
          simp only [Coefficients.centeredBernsteinCheck, Bool.and_eq_true] at h
          simp only [Coefficients.map]
          rw [centeredBernsteinCheck_sound h.1,
            Coefficients.centeredBernsteinCheck_sound h.2]

end

private theorem all_ok_of_neg {n : ℕ} {p : FixedDensePolynomial width precision n}
    (h : allOk (neg n p) = true) : allOk p = true := by
  induction n with
  | zero =>
      cases p with
      | base p =>
          simp only [neg, allOk, FixedDyadicInterval.neg,
            FixedDyadicInterval.negationSafe, Bool.and_eq_true] at h ⊢
          exact h.1.1.1
  | succ n ih =>
      cases p with
      | ofCoefficients coefficients =>
          induction coefficients using Coefficients.recList with
          | nil => rfl
          | cons head tail tailIH =>
              simp only [neg, allOk, Coefficients.map, Coefficients.all,
                Bool.and_eq_true] at h ⊢
              exact ⟨ih h.1, tailIH h.2⟩

/-- Corresponding coefficients of represented sequences remain represented after padding. -/
theorem Coefficients.get_represents {n : ℕ}
    {fixed : Coefficients width precision n}
    {exact : MultivariateDensePolynomial.Coefficients n}
    (h : FixedDenseCoefficients.Represents fixed exact) (index : ℕ)
    (hok : allOk (fixed.get (zero width precision n) index) = true) :
    Represents (fixed.get (zero width precision n) index)
      (exact.get (MultivariateDensePolynomial.zero n) index) := by
  induction fixed using Coefficients.recList generalizing exact index with
  | nil =>
      cases exact with
      | nil => exact zero_represents width precision n hok
      | cons => contradiction
  | cons fixed fixeds ih =>
      cases exact with
      | nil => contradiction
      | cons exact exacts =>
          rcases h with ⟨hfixed, hfixeds⟩
          cases index with
          | zero => exact hfixed
          | succ index => exact ih hfixeds index hok

private theorem centeredBernsteinQuadratic_represents_of_get {n : ℕ}
    {fixed : Coefficients width precision n}
    {exact : MultivariateDensePolynomial.Coefficients n}
    (h : ∀ index, allOk (fixed.get (zero width precision n) index) = true →
      Represents (fixed.get (zero width precision n) index)
        (exact.get (MultivariateDensePolynomial.zero n) index))
    (hok : Coefficients.all allOk (centeredBernsteinQuadratic fixed) = true) :
    FixedDenseCoefficients.Represents (centeredBernsteinQuadratic fixed)
      (MultivariateDensePolynomial.centeredBernsteinQuadratic exact) := by
  simp only [centeredBernsteinQuadratic, Coefficients.all, Bool.and_eq_true,
    Bool.and_true] at hok
  let p₀ := fixed.get (zero width precision n) 0
  let p₁ := fixed.get (zero width precision n) 1
  let p₂ := fixed.get (zero width precision n) 2
  let q₀ := exact.get (MultivariateDensePolynomial.zero n) 0
  let q₁ := exact.get (MultivariateDensePolynomial.zero n) 1
  let q₂ := exact.get (MultivariateDensePolynomial.zero n) 2
  have hinner₀ : allOk (add n p₀ (neg n p₁)) = true :=
    all_ok_left_of_add hok.1
  have hneg₁ : allOk (neg n p₁) = true := all_ok_right_of_add hinner₀
  have hp₀ : Represents p₀ q₀ :=
    h 0 (all_ok_left_of_add hinner₀)
  have hp₁ : Represents p₁ q₁ :=
    h 1 (all_ok_of_neg hneg₁)
  have hp₂ : Represents p₂ q₂ :=
    h 2 (all_ok_right_of_add hok.1)
  have hb₀ : Represents (add n (add n p₀ (neg n p₁)) p₂)
      (MultivariateDensePolynomial.add n
        (MultivariateDensePolynomial.add n q₀ (MultivariateDensePolynomial.neg n q₁)) q₂) :=
    add_represents (add_represents hp₀ (neg_represents hp₁ hneg₁) hinner₀) hp₂ hok.1
  have hneg₂ : allOk (neg n p₂) = true := all_ok_right_of_add hok.2.1
  have hb₁ : Represents (add n p₀ (neg n p₂))
      (MultivariateDensePolynomial.add n q₀ (MultivariateDensePolynomial.neg n q₂)) :=
    add_represents hp₀ (neg_represents hp₂ hneg₂) hok.2.1
  have hinner₂ : allOk (add n p₀ p₁) = true := all_ok_left_of_add hok.2.2
  have hb₂ : Represents (add n (add n p₀ p₁) p₂)
      (MultivariateDensePolynomial.add n (MultivariateDensePolynomial.add n q₀ q₁) q₂) :=
    add_represents (add_represents hp₀ hp₁ hinner₂) hp₂ hok.2.2
  exact ⟨hb₀, hb₁, hb₂, trivial⟩

/-- A successful fixed quadratic coefficient pass contains the exact rational pass. -/
theorem centeredBernsteinQuadratic_represents {n : ℕ}
    {fixed : Coefficients width precision n}
    {exact : MultivariateDensePolynomial.Coefficients n}
    (h : FixedDenseCoefficients.Represents fixed exact)
    (hok : Coefficients.all allOk (centeredBernsteinQuadratic fixed) = true) :
    FixedDenseCoefficients.Represents (centeredBernsteinQuadratic fixed)
      (MultivariateDensePolynomial.centeredBernsteinQuadratic exact) :=
  centeredBernsteinQuadratic_represents_of_get
    (fun index ↦ Coefficients.get_represents h index) hok

private theorem quartic_coefficient_zero_represents {n : ℕ}
    {p₀ p₁ p₂ p₃ p₄ : FixedDensePolynomial width precision n}
    {q₀ q₁ q₂ q₃ q₄ : MultivariateDensePolynomial n}
    (hp₀ : Represents p₀ q₀) (hp₁ : Represents p₁ q₁) (hp₂ : Represents p₂ q₂)
    (hp₃ : Represents p₃ q₃) (hp₄ : Represents p₄ q₄)
    (hok : allOk (add n (add n (add n (add n p₀ (neg n p₁)) p₂) (neg n p₃)) p₄) =
      true) : Represents
      (add n (add n (add n (add n p₀ (neg n p₁)) p₂) (neg n p₃)) p₄)
      (MultivariateDensePolynomial.add n
        (MultivariateDensePolynomial.add n
          (MultivariateDensePolynomial.add n
            (MultivariateDensePolynomial.add n q₀
              (MultivariateDensePolynomial.neg n q₁)) q₂)
            (MultivariateDensePolynomial.neg n q₃)) q₄) := by
  have h₃ := all_ok_left_of_add hok
  have h₂ := all_ok_left_of_add h₃
  have h₁ := all_ok_left_of_add h₂
  exact add_represents
    (add_represents
      (add_represents
        (add_represents hp₀ (neg_represents hp₁ (all_ok_right_of_add h₁)) h₁)
        hp₂ h₂)
      (neg_represents hp₃ (all_ok_right_of_add h₃)) h₃)
    hp₄ hok

private theorem quartic_coefficient_one_represents {n : ℕ}
    {p₀ p₁ p₃ p₄ : FixedDensePolynomial width precision n}
    {q₀ q₁ q₃ q₄ : MultivariateDensePolynomial n}
    (hp₀ : Represents p₀ q₀) (hp₁ : Represents p₁ q₁)
    (hp₃ : Represents p₃ q₃) (hp₄ : Represents p₄ q₄)
    (hok : allOk (add n (add n (add n p₀ (scale (-1 / 2) n p₁))
      (scale (1 / 2) n p₃)) (neg n p₄)) = true) : Represents
      (add n (add n (add n p₀ (scale (-1 / 2) n p₁))
        (scale (1 / 2) n p₃)) (neg n p₄))
      (MultivariateDensePolynomial.add n
        (MultivariateDensePolynomial.add n
          (MultivariateDensePolynomial.add n q₀
            (MultivariateDensePolynomial.scale (-1 / 2) n q₁))
          (MultivariateDensePolynomial.scale (1 / 2) n q₃))
        (MultivariateDensePolynomial.neg n q₄)) := by
  have h₂ := all_ok_left_of_add hok
  have h₁ := all_ok_left_of_add h₂
  exact add_represents
    (add_represents
      (add_represents hp₀ (scale_represents (-1 / 2) hp₁ (all_ok_right_of_add h₁)) h₁)
      (scale_represents (1 / 2) hp₃ (all_ok_right_of_add h₂)) h₂)
    (neg_represents hp₄ (all_ok_right_of_add hok)) hok

private theorem quartic_coefficient_two_represents {n : ℕ}
    {p₀ p₂ p₄ : FixedDensePolynomial width precision n}
    {q₀ q₂ q₄ : MultivariateDensePolynomial n}
    (hp₀ : Represents p₀ q₀) (hp₂ : Represents p₂ q₂)
    (hp₄ : Represents p₄ q₄)
    (hok : allOk (add n (add n p₀ (scale (-1 / 3) n p₂)) p₄) = true) :
    Represents (add n (add n p₀ (scale (-1 / 3) n p₂)) p₄)
      (MultivariateDensePolynomial.add n
        (MultivariateDensePolynomial.add n q₀
          (MultivariateDensePolynomial.scale (-1 / 3) n q₂)) q₄) := by
  have h₁ := all_ok_left_of_add hok
  exact add_represents
    (add_represents hp₀ (scale_represents (-1 / 3) hp₂ (all_ok_right_of_add h₁)) h₁)
    hp₄ hok

private theorem quartic_coefficient_three_represents {n : ℕ}
    {p₀ p₁ p₃ p₄ : FixedDensePolynomial width precision n}
    {q₀ q₁ q₃ q₄ : MultivariateDensePolynomial n}
    (hp₀ : Represents p₀ q₀) (hp₁ : Represents p₁ q₁)
    (hp₃ : Represents p₃ q₃) (hp₄ : Represents p₄ q₄)
    (hok : allOk (add n (add n (add n p₀ (scale (1 / 2) n p₁))
      (scale (-1 / 2) n p₃)) (neg n p₄)) = true) : Represents
      (add n (add n (add n p₀ (scale (1 / 2) n p₁))
        (scale (-1 / 2) n p₃)) (neg n p₄))
      (MultivariateDensePolynomial.add n
        (MultivariateDensePolynomial.add n
          (MultivariateDensePolynomial.add n q₀
            (MultivariateDensePolynomial.scale (1 / 2) n q₁))
          (MultivariateDensePolynomial.scale (-1 / 2) n q₃))
        (MultivariateDensePolynomial.neg n q₄)) := by
  have h₂ := all_ok_left_of_add hok
  have h₁ := all_ok_left_of_add h₂
  exact add_represents
    (add_represents
      (add_represents hp₀ (scale_represents (1 / 2) hp₁ (all_ok_right_of_add h₁)) h₁)
      (scale_represents (-1 / 2) hp₃ (all_ok_right_of_add h₂)) h₂)
    (neg_represents hp₄ (all_ok_right_of_add hok)) hok

private theorem quartic_coefficient_four_represents {n : ℕ}
    {p₀ p₁ p₂ p₃ p₄ : FixedDensePolynomial width precision n}
    {q₀ q₁ q₂ q₃ q₄ : MultivariateDensePolynomial n}
    (hp₀ : Represents p₀ q₀) (hp₁ : Represents p₁ q₁) (hp₂ : Represents p₂ q₂)
    (hp₃ : Represents p₃ q₃) (hp₄ : Represents p₄ q₄)
    (hok : allOk (add n (add n (add n (add n p₀ p₁) p₂) p₃) p₄) = true) :
    Represents (add n (add n (add n (add n p₀ p₁) p₂) p₃) p₄)
      (MultivariateDensePolynomial.add n
        (MultivariateDensePolynomial.add n
          (MultivariateDensePolynomial.add n
            (MultivariateDensePolynomial.add n q₀ q₁) q₂) q₃) q₄) := by
  have h₃ := all_ok_left_of_add hok
  have h₂ := all_ok_left_of_add h₃
  have h₁ := all_ok_left_of_add h₂
  exact add_represents
    (add_represents
      (add_represents (add_represents hp₀ hp₁ h₁) hp₂ h₂) hp₃ h₃)
    hp₄ hok

private theorem centeredBernsteinQuartic_represents_of_get {n : ℕ}
    {fixed : Coefficients width precision n}
    {exact : MultivariateDensePolynomial.Coefficients n}
    (h : ∀ index, allOk (fixed.get (zero width precision n) index) = true →
      Represents (fixed.get (zero width precision n) index)
        (exact.get (MultivariateDensePolynomial.zero n) index))
    (hok : Coefficients.all allOk (centeredBernsteinQuartic fixed) = true) :
    FixedDenseCoefficients.Represents (centeredBernsteinQuartic fixed)
      (MultivariateDensePolynomial.centeredBernsteinQuartic exact) := by
  simp only [centeredBernsteinQuartic, Coefficients.all, Bool.and_eq_true,
    Bool.and_true] at hok
  let p₀ := fixed.get (zero width precision n) 0
  let p₁ := fixed.get (zero width precision n) 1
  let p₂ := fixed.get (zero width precision n) 2
  let p₃ := fixed.get (zero width precision n) 3
  let p₄ := fixed.get (zero width precision n) 4
  let q₀ := exact.get (MultivariateDensePolynomial.zero n) 0
  let q₁ := exact.get (MultivariateDensePolynomial.zero n) 1
  let q₂ := exact.get (MultivariateDensePolynomial.zero n) 2
  let q₃ := exact.get (MultivariateDensePolynomial.zero n) 3
  let q₄ := exact.get (MultivariateDensePolynomial.zero n) 4
  have hbefore₄ :
      allOk (add n (add n (add n p₀ (neg n p₁)) p₂) (neg n p₃)) = true :=
    all_ok_left_of_add hok.1
  have hbefore₃ : allOk (add n (add n p₀ (neg n p₁)) p₂) = true :=
    all_ok_left_of_add hbefore₄
  have hbefore₂ : allOk (add n p₀ (neg n p₁)) = true :=
    all_ok_left_of_add hbefore₃
  have hneg₁ : allOk (neg n p₁) = true := all_ok_right_of_add hbefore₂
  have hneg₃ : allOk (neg n p₃) = true := all_ok_right_of_add hbefore₄
  have hp₀ : Represents p₀ q₀ :=
    h 0 (all_ok_left_of_add hbefore₂)
  have hp₁ : Represents p₁ q₁ :=
    h 1 (all_ok_of_neg hneg₁)
  have hp₂ : Represents p₂ q₂ :=
    h 2 (all_ok_right_of_add hbefore₃)
  have hp₃ : Represents p₃ q₃ :=
    h 3 (all_ok_of_neg hneg₃)
  have hp₄ : Represents p₄ q₄ :=
    h 4 (all_ok_right_of_add hok.1)
  have hb₀ := quartic_coefficient_zero_represents hp₀ hp₁ hp₂ hp₃ hp₄ hok.1
  have hb₁ := quartic_coefficient_one_represents hp₀ hp₁ hp₃ hp₄ hok.2.1
  have hb₂ := quartic_coefficient_two_represents hp₀ hp₂ hp₄ hok.2.2.1
  have hb₃ := quartic_coefficient_three_represents hp₀ hp₁ hp₃ hp₄ hok.2.2.2.1
  have hb₄ := quartic_coefficient_four_represents hp₀ hp₁ hp₂ hp₃ hp₄ hok.2.2.2.2
  exact ⟨hb₀, hb₁, hb₂, hb₃, hb₄, trivial⟩

/-- A successful fixed quartic coefficient pass contains the exact rational pass. -/
theorem centeredBernsteinQuartic_represents {n : ℕ}
    {fixed : Coefficients width precision n}
    {exact : MultivariateDensePolynomial.Coefficients n}
    (h : FixedDenseCoefficients.Represents fixed exact)
    (hok : Coefficients.all allOk (centeredBernsteinQuartic fixed) = true) :
    FixedDenseCoefficients.Represents (centeredBernsteinQuartic fixed)
      (MultivariateDensePolynomial.centeredBernsteinQuartic exact) :=
  centeredBernsteinQuartic_represents_of_get
    (fun index ↦ Coefficients.get_represents h index) hok

/-- A successful fixed coefficient pass contains the exact pass of the same degree. -/
theorem centeredBernsteinCoefficients_represents
    (degree : MultivariateDensePolynomial.BernsteinDegree) {n : ℕ}
    {fixed : Coefficients width precision n}
    {exact : MultivariateDensePolynomial.Coefficients n}
    (h : FixedDenseCoefficients.Represents fixed exact)
    (hok : Coefficients.all allOk (centeredBernsteinCoefficients degree fixed) = true) :
    FixedDenseCoefficients.Represents (centeredBernsteinCoefficients degree fixed)
      (MultivariateDensePolynomial.centeredBernsteinCoefficients degree exact) := by
  cases degree with
  | quadratic => exact centeredBernsteinQuadratic_represents h hok
  | quartic => exact centeredBernsteinQuartic_represents h hok

private theorem Coefficients.map_represents {n : ℕ}
    {fixedOperation : FixedDensePolynomial width precision n →
      FixedDensePolynomial width precision n}
    {exactOperation : MultivariateDensePolynomial n → MultivariateDensePolynomial n}
    (hop : ∀ {fixed exact}, Represents fixed exact → allOk (fixedOperation fixed) = true →
      Represents (fixedOperation fixed) (exactOperation exact))
    {fixed : Coefficients width precision n}
    {exact : MultivariateDensePolynomial.Coefficients n}
    (h : FixedDenseCoefficients.Represents fixed exact)
    (hok : Coefficients.all allOk (Coefficients.map fixedOperation fixed) = true) :
    FixedDenseCoefficients.Represents (Coefficients.map fixedOperation fixed)
      (MultivariateDensePolynomial.Coefficients.map exactOperation exact) := by
  induction fixed using Coefficients.recList generalizing exact with
  | nil =>
      cases exact with
      | nil => trivial
      | cons => contradiction
  | cons fixed fixeds ih =>
      cases exact with
      | nil => contradiction
      | cons exact exacts =>
          rcases h with ⟨hfixed, hfixeds⟩
          simp only [Coefficients.map, Coefficients.all, Bool.and_eq_true] at hok
          exact ⟨hop hfixed hok.1, ih hfixeds hok.2⟩

private theorem Coefficients.get_map_represents {n : ℕ}
    {fixedOperation : FixedDensePolynomial width precision n →
      FixedDensePolynomial width precision n}
    {exactOperation : MultivariateDensePolynomial n → MultivariateDensePolynomial n}
    (hop : ∀ {fixed exact}, Represents fixed exact → allOk (fixedOperation fixed) = true →
      Represents (fixedOperation fixed) (exactOperation exact))
    {fixed : Coefficients width precision n}
    {exact : MultivariateDensePolynomial.Coefficients n}
    (h : FixedDenseCoefficients.Represents fixed exact) (index : ℕ)
    (hok : allOk ((Coefficients.map fixedOperation fixed).get
      (zero width precision n) index) = true) :
    Represents ((Coefficients.map fixedOperation fixed).get
        (zero width precision n) index)
      ((MultivariateDensePolynomial.Coefficients.map exactOperation exact).get
        (MultivariateDensePolynomial.zero n) index) := by
  induction fixed using Coefficients.recList generalizing exact index with
  | nil =>
      cases exact with
      | nil => exact zero_represents width precision n hok
      | cons => contradiction
  | cons fixed fixeds ih =>
      cases exact with
      | nil => contradiction
      | cons exact exacts =>
          rcases h with ⟨hfixed, hfixeds⟩
          cases index with
          | zero => exact hop hfixed hok
          | succ index => exact ih hfixeds index hok

/-- A successful fixed coordinate pass contains the exact rational coordinate pass. -/
theorem centeredBernsteinAt_represents {n : ℕ} (index : Fin n)
    (degree : MultivariateDensePolynomial.BernsteinDegree)
    {fixed : FixedDensePolynomial width precision n}
    {exact : MultivariateDensePolynomial n} (h : Represents fixed exact)
    (hok : allOk (centeredBernsteinAt index degree fixed) = true) :
    Represents (centeredBernsteinAt index degree fixed)
      (MultivariateDensePolynomial.rationalCenteredBernsteinAt index degree exact) := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
      cases fixed with
      | ofCoefficients fixed =>
          cases exact with
          | ofCoefficients exact =>
              cases index using Fin.cases with
              | zero => exact centeredBernsteinCoefficients_represents degree h hok
              | succ index =>
                  exact Coefficients.map_represents
                    (fun hfixed hpass ↦ ih index hfixed hpass) h hok

private theorem centeredBernsteinCoefficients_represents_of_get
    (degree : MultivariateDensePolynomial.BernsteinDegree) {n : ℕ}
    {fixed : Coefficients width precision n}
    {exact : MultivariateDensePolynomial.Coefficients n}
    (h : ∀ index, allOk (fixed.get (zero width precision n) index) = true →
      Represents (fixed.get (zero width precision n) index)
        (exact.get (MultivariateDensePolynomial.zero n) index))
    (hok : Coefficients.all allOk (centeredBernsteinCoefficients degree fixed) = true) :
    FixedDenseCoefficients.Represents (centeredBernsteinCoefficients degree fixed)
      (MultivariateDensePolynomial.centeredBernsteinCoefficients degree exact) := by
  cases degree with
  | quadratic => exact centeredBernsteinQuadratic_represents_of_get h hok
  | quartic => exact centeredBernsteinQuartic_represents_of_get h hok

/-- A successful recursive fixed pass contains the exact centered Bernstein conversion. -/
theorem centeredBernstein_represents {n : ℕ}
    (degrees : Fin n → MultivariateDensePolynomial.BernsteinDegree)
    {fixed : FixedDensePolynomial width precision n}
    {exact : MultivariateDensePolynomial n} (h : Represents fixed exact)
    (hok : allOk (centeredBernstein degrees fixed) = true) :
    Represents (centeredBernstein degrees fixed)
      (MultivariateDensePolynomial.centeredBernstein degrees exact) := by
  induction n with
  | zero =>
      cases fixed with
      | base fixed =>
          cases exact with
          | base exact => exact h
  | succ n ih =>
      cases fixed with
      | ofCoefficients fixed =>
          cases exact with
          | ofCoefficients exact =>
              apply centeredBernsteinCoefficients_represents_of_get (degrees 0) ?_ hok
              intro index hindex
              exact Coefficients.get_map_represents
                (fun hfixed hpass ↦ ih (Fin.tail degrees) hfixed hpass) h index hindex

/-- Check that every stored fixed coefficient has nonpositive upper endpoint. -/
def allNonpositive : {n : ℕ} → FixedDensePolynomial width precision n → Bool
  | 0, .base value => value.upperNonpositive
  | _ + 1, .ofCoefficients coefficients => Coefficients.all allNonpositive coefficients

/-- A successful fixed sign check proves every represented exact coefficient nonpositive. -/
theorem allNonpositive_sound {n : ℕ}
    {fixed : FixedDensePolynomial width precision n}
    {exact : MultivariateDensePolynomial n} (h : Represents fixed exact)
    (hcheck : allNonpositive fixed = true) :
    MultivariateDensePolynomial.AllNonpositive exact := by
  induction n with
  | zero =>
      cases fixed with
      | base fixed =>
          cases exact with
          | base exact =>
              rcases h with ⟨dyadic, hfixed, hexact⟩
              exact FixedDyadicInterval.nonpositive_of_upperNonpositive
                hfixed hcheck hexact
  | succ n ih =>
      cases fixed with
      | ofCoefficients fixed =>
          cases exact with
          | ofCoefficients exact =>
              induction fixed using Coefficients.recList generalizing exact with
              | nil =>
                  cases exact with
                  | nil => trivial
                  | cons => contradiction
              | cons fixed fixeds tailIH =>
                  cases exact with
                  | nil => contradiction
                  | cons exact exacts =>
                      rcases h with ⟨hfixed, hfixeds⟩
                      simp only [allNonpositive, Coefficients.all,
                        Bool.and_eq_true] at hcheck
                      exact ⟨ih hfixed hcheck.1, tailIH hcheck.2 exacts hfixeds⟩

end Bescovitch.FixedDensePolynomial
