/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.MultivariateDensePolynomial
public import Bescovitch.Certificates.RawRat

/-!
# Dense polynomials over unreduced rationals

These tensors mirror `MultivariateDensePolynomial`, but their scalar arithmetic remains transparent
to the kernel. Interpretation commutes with every polynomial operation used by certificates.
-/

@[expose] public section

namespace Bescovitch

mutual

/-- Dense multivariable polynomials with unreduced rational coefficients. -/
inductive RawDensePolynomial : ℕ → Type
  | base (value : RawRat) : RawDensePolynomial 0
  | ofCoefficients {n : ℕ} (coefficients : RawDenseCoefficients n) :
      RawDensePolynomial (n + 1)

/-- A raw polynomial's outer coefficient sequence. -/
inductive RawDenseCoefficients : ℕ → Type
  | nil {n : ℕ} : RawDenseCoefficients n
  | cons {n : ℕ} (head : RawDensePolynomial n) (tail : RawDenseCoefficients n) :
      RawDenseCoefficients n

end


namespace RawDensePolynomial

/-- Raw coefficient sequences. -/
abbrev Coefficients := RawDenseCoefficients

namespace Coefficients

/-- Recursion on the coefficient tail, treating coefficient polynomials as atoms. -/
def recList {n : ℕ} {motive : Coefficients n → Sort*}
    (nil : motive .nil)
    (cons : ∀ head tail, motive tail → motive (.cons head tail)) :
    ∀ coefficients, motive coefficients
  | .nil => nil
  | .cons head tail => cons head tail (recList nil cons tail)

/-- Add two raw coefficient sequences, padding by zero. -/
def add {n : ℕ} (addPolynomial : RawDensePolynomial n → RawDensePolynomial n →
    RawDensePolynomial n) : Coefficients n → Coefficients n → Coefficients n
  | .nil, q => q
  | p, .nil => p
  | .cons p ps, .cons q qs => .cons (addPolynomial p q) (add addPolynomial ps qs)

/-- Map a polynomial operation over a raw coefficient sequence. -/
def map {n : ℕ} (f : RawDensePolynomial n → RawDensePolynomial n) :
    Coefficients n → Coefficients n
  | .nil => .nil
  | .cons p ps => .cons (f p) (map f ps)

/-- Exact coefficient convolution. -/
def mul {n : ℕ} (zero : RawDensePolynomial n)
    (addPolynomial mulPolynomial : RawDensePolynomial n → RawDensePolynomial n →
      RawDensePolynomial n) : Coefficients n → Coefficients n → Coefficients n
  | .nil, _ => .nil
  | .cons p ps, q =>
      add addPolynomial (map (mulPolynomial p) q)
        (.cons zero (mul zero addPolynomial mulPolynomial ps q))

/-- Read a coefficient, returning zero past the stored support. -/
def get {n : ℕ} (zero : RawDensePolynomial n) :
    Coefficients n → ℕ → RawDensePolynomial n
  | .nil, _ => zero
  | .cons p _, 0 => p
  | .cons _ ps, k + 1 => get zero ps k

/-- Interpret every coefficient as an ordinary rational polynomial. -/
def interpret {n : ℕ} (f : RawDensePolynomial n → MultivariateDensePolynomial n) :
    Coefficients n → MultivariateDensePolynomial.Coefficients n
  | .nil => .nil
  | .cons p ps => .cons (f p) (interpret f ps)

/-- Convert every ordinary rational coefficient to its canonical raw representative. -/
def ofPolynomial {n : ℕ}
    (f : MultivariateDensePolynomial n → RawDensePolynomial n) :
    MultivariateDensePolynomial.Coefficients n → Coefficients n
  | .nil => .nil
  | .cons p ps => .cons (f p) (ofPolynomial f ps)

/-- Compare two coefficient sequences using a supplied scalar-polynomial comparison. -/
def equivalentBool {n : ℕ}
    (equal : RawDensePolynomial n → RawDensePolynomial n → Bool) :
    Coefficients n → Coefficients n → Bool
  | .nil, .nil => true
  | .cons p ps, .cons q qs => equal p q && equivalentBool equal ps qs
  | _, _ => false

end Coefficients

/-- The zero raw polynomial. -/
def zero : (n : ℕ) → RawDensePolynomial n
  | 0 => .base RawRat.zero
  | _ + 1 => .ofCoefficients .nil

/-- Raw polynomial addition. -/
def add : (n : ℕ) → RawDensePolynomial n → RawDensePolynomial n →
    RawDensePolynomial n
  | 0, .base p, .base q => .base (p.add q)
  | n + 1, .ofCoefficients p, .ofCoefficients q =>
      .ofCoefficients (Coefficients.add (add n) p q)

/-- Raw polynomial additive inverse. -/
def neg : (n : ℕ) → RawDensePolynomial n → RawDensePolynomial n
  | 0, .base p => .base p.neg
  | n + 1, .ofCoefficients p => .ofCoefficients (Coefficients.map (neg n) p)

/-- Multiply every coefficient by an unreduced rational. -/
def scale (a : RawRat) : (n : ℕ) → RawDensePolynomial n → RawDensePolynomial n
  | 0, .base p => .base (a.mul p)
  | n + 1, .ofCoefficients p => .ofCoefficients (Coefficients.map (scale a n) p)

/-- Exact raw polynomial multiplication. -/
def mul : (n : ℕ) → RawDensePolynomial n → RawDensePolynomial n →
    RawDensePolynomial n
  | 0, .base p, .base q => .base (p.mul q)
  | n + 1, .ofCoefficients p, .ofCoefficients q =>
      .ofCoefficients (Coefficients.mul (zero n) (add n) (mul n) p q)

/-- A constant raw polynomial. -/
def constant : (n : ℕ) → RawRat → RawDensePolynomial n
  | 0, a => .base a
  | n + 1, a => .ofCoefficients (.cons (constant n a) .nil)

/-- A raw coordinate variable. -/
def coordinate : {n : ℕ} → Fin n → RawDensePolynomial n
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases
      (.ofCoefficients (.cons (zero n) (.cons (constant n RawRat.one) .nil)))
      (fun j => .ofCoefficients (.cons (coordinate j) .nil)) i

/-- Natural powers of a raw polynomial. -/
def pow {n : ℕ} (p : RawDensePolynomial n) : ℕ → RawDensePolynomial n
  | 0 => constant n RawRat.one
  | k + 1 => mul n (pow p k) p

/-- Interpret a raw polynomial coefficientwise. -/
def interpret : {n : ℕ} → RawDensePolynomial n → MultivariateDensePolynomial n
  | 0, .base value => .base value.interpret
  | _ + 1, .ofCoefficients coefficients => .ofCoefficients
      (Coefficients.interpret interpret coefficients)

/-- Convert an ordinary rational polynomial coefficientwise. -/
def ofPolynomial : {n : ℕ} → MultivariateDensePolynomial n → RawDensePolynomial n
  | 0, .base value => .base (RawRat.ofRat value)
  | _ + 1, .ofCoefficients coefficients =>
      .ofCoefficients (Coefficients.ofPolynomial ofPolynomial coefficients)

/-- Compare raw polynomials coefficientwise by rational equivalence. -/
def equivalentBool : (n : ℕ) → RawDensePolynomial n → RawDensePolynomial n → Bool
  | 0, .base left, .base right => left.equivalent right
  | n + 1, .ofCoefficients left, .ofCoefficients right =>
      Coefficients.equivalentBool (equivalentBool n) left right

/-- A successful raw-polynomial comparison gives equal rational interpretations. -/
theorem equivalentBool_sound {n : ℕ} {left right : RawDensePolynomial n}
    (h : equivalentBool n left right = true) : interpret left = interpret right := by
  induction n with
  | zero =>
      cases left with
      | base left => cases right with
        | base right =>
            exact congrArg MultivariateDensePolynomial.base (RawRat.equivalent_sound h)
  | succ n ih =>
      cases left with
      | ofCoefficients left => cases right with
        | ofCoefficients right =>
          rw [equivalentBool.eq_2] at h
          simp only [interpret.eq_2]
          congr 1
          induction left using Coefficients.recList generalizing right with
          | nil =>
              cases right with
              | nil => rfl
              | cons q qs => exact Bool.noConfusion h
          | cons p ps ihps =>
              cases right with
              | nil => exact Bool.noConfusion h
              | cons q qs =>
                  rw [Coefficients.equivalentBool] at h
                  rw [Bool.and_eq_true] at h
                  rw [Coefficients.interpret.eq_2, Coefficients.interpret.eq_2,
                    ih h.1, ihps qs h.2]

/-- Canonical conversion is a right inverse to interpretation. -/
theorem interpret_ofPolynomial {n : ℕ} (p : MultivariateDensePolynomial n) :
    interpret (ofPolynomial p) = p := by
  induction n with
  | zero =>
      cases p with
      | base value =>
          exact congrArg MultivariateDensePolynomial.base (RawRat.interpret_ofRat value)
  | succ n ih =>
      cases p with
      | ofCoefficients coefficients =>
        rw [ofPolynomial, interpret.eq_2]
        congr 1
        induction coefficients using MultivariateDensePolynomial.Coefficients.recList with
        | nil => rfl
        | cons p ps ihps =>
            rw [Coefficients.ofPolynomial, Coefficients.interpret.eq_2, ih p, ihps]

theorem interpret_zero (n : ℕ) : interpret (zero n) = MultivariateDensePolynomial.zero n := by
  cases n with
  | zero => exact congrArg MultivariateDensePolynomial.base RawRat.interpret_zero
  | succ n => rw [zero.eq_2, interpret.eq_2, Coefficients.interpret.eq_1,
      MultivariateDensePolynomial.zero.eq_2]

theorem interpret_constant (n : ℕ) (a : RawRat) :
    interpret (constant n a) = MultivariateDensePolynomial.constant n a.interpret := by
  induction n with
  | zero => rfl
  | succ n ih => rw [constant.eq_2, interpret.eq_2,
      MultivariateDensePolynomial.constant.eq_2, Coefficients.interpret.eq_2,
      Coefficients.interpret.eq_1, ih]

theorem interpret_coordinate {n : ℕ} (i : Fin n) :
    interpret (coordinate i) = MultivariateDensePolynomial.coordinate i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [coordinate.eq_2, Fin.cases_zero, interpret.eq_2,
          MultivariateDensePolynomial.coordinate.eq_2, Fin.cases_zero,
          Coefficients.interpret.eq_2, Coefficients.interpret.eq_2,
          Coefficients.interpret.eq_1, interpret_zero, interpret_constant,
          RawRat.interpret_one]
      · rw [coordinate.eq_2, Fin.cases_succ, interpret.eq_2,
          MultivariateDensePolynomial.coordinate.eq_2, Fin.cases_succ,
          Coefficients.interpret.eq_2, Coefficients.interpret.eq_1, ih j]

theorem interpret_neg {n : ℕ} (p : RawDensePolynomial n) :
    interpret (neg n p) = MultivariateDensePolynomial.neg n (interpret p) := by
  induction n with
  | zero => cases p with
    | base p => exact congrArg MultivariateDensePolynomial.base (RawRat.interpret_neg p)
  | succ n ih =>
      cases p with
      | ofCoefficients ps =>
        rw [neg.eq_2]
        simp only [interpret.eq_2]
        rw [MultivariateDensePolynomial.neg.eq_2]
        congr 1
        induction ps using Coefficients.recList with
        | nil => rfl
        | cons p ps ihps =>
          rw [Coefficients.map.eq_2]
          simp only [Coefficients.interpret.eq_2]
          rw [MultivariateDensePolynomial.Coefficients.map.eq_2, ih p, ihps]

theorem interpret_add {n : ℕ} (p q : RawDensePolynomial n) :
    interpret (add n p q) = MultivariateDensePolynomial.add n (interpret p) (interpret q) := by
  induction n with
  | zero => cases p with
    | base p => cases q with
      | base q => exact congrArg MultivariateDensePolynomial.base (RawRat.interpret_add p q)
  | succ n ih =>
      cases p with
      | ofCoefficients ps => cases q with
        | ofCoefficients qs =>
          rw [add.eq_2]
          simp only [interpret.eq_2]
          rw [MultivariateDensePolynomial.add.eq_2]
          congr 1
          induction ps using Coefficients.recList generalizing qs with
          | nil => rfl
          | cons p ps ihps =>
            cases qs with
            | nil => rfl
            | cons q qs =>
              rw [Coefficients.add.eq_3]
              simp only [Coefficients.interpret.eq_2]
              rw [MultivariateDensePolynomial.Coefficients.add.eq_3, ih p q, ihps qs]

theorem interpret_scale {n : ℕ} (a : RawRat) (p : RawDensePolynomial n) :
    interpret (scale a n p) =
      MultivariateDensePolynomial.scale a.interpret n (interpret p) := by
  induction n with
  | zero => cases p with
    | base p => exact congrArg MultivariateDensePolynomial.base (RawRat.interpret_mul a p)
  | succ n ih =>
      cases p with
      | ofCoefficients ps =>
        rw [scale.eq_2]
        simp only [interpret.eq_2]
        rw [MultivariateDensePolynomial.scale.eq_2]
        congr 1
        induction ps using Coefficients.recList with
        | nil => rfl
        | cons p ps ihps =>
          rw [Coefficients.map.eq_2]
          simp only [Coefficients.interpret.eq_2]
          rw [MultivariateDensePolynomial.Coefficients.map.eq_2, ih p, ihps]

theorem interpret_mul {n : ℕ} (p q : RawDensePolynomial n) :
    interpret (mul n p q) = MultivariateDensePolynomial.mul n (interpret p) (interpret q) := by
  induction n with
  | zero => cases p with
    | base p => cases q with
      | base q => exact congrArg MultivariateDensePolynomial.base (RawRat.interpret_mul p q)
  | succ n ih =>
      cases p with
      | ofCoefficients ps => cases q with
        | ofCoefficients qs =>
          have hadd (as bs : Coefficients n) :
              Coefficients.interpret interpret (Coefficients.add (add n) as bs) =
                MultivariateDensePolynomial.Coefficients.add
                  (MultivariateDensePolynomial.add n)
                  (Coefficients.interpret interpret as)
                  (Coefficients.interpret interpret bs) := by
            induction as using Coefficients.recList generalizing bs with
            | nil => rfl
            | cons a as ihas =>
                cases bs with
                | nil => rfl
                | cons b bs =>
                    rw [Coefficients.add.eq_3]
                    simp only [Coefficients.interpret.eq_2]
                    rw [MultivariateDensePolynomial.Coefficients.add.eq_3,
                      interpret_add, ihas]
          have hmap (a : RawDensePolynomial n) (bs : Coefficients n) :
              Coefficients.interpret interpret (Coefficients.map (mul n a) bs) =
                MultivariateDensePolynomial.Coefficients.map
                  (MultivariateDensePolynomial.mul n (interpret a))
                  (Coefficients.interpret interpret bs) := by
            induction bs using Coefficients.recList with
            | nil => rfl
            | cons b bs ihbs =>
                rw [Coefficients.map.eq_2]
                simp only [Coefficients.interpret.eq_2]
                rw [MultivariateDensePolynomial.Coefficients.map.eq_2, ih a b, ihbs]
          have hcoeff (as bs : Coefficients n) :
              Coefficients.interpret interpret
                  (Coefficients.mul (zero n) (add n) (mul n) as bs) =
                MultivariateDensePolynomial.Coefficients.mul
                  (MultivariateDensePolynomial.zero n)
                  (MultivariateDensePolynomial.add n)
                  (MultivariateDensePolynomial.mul n)
                  (Coefficients.interpret interpret as)
                  (Coefficients.interpret interpret bs) := by
            induction as using Coefficients.recList with
            | nil => rfl
            | cons a as ihas =>
                rw [Coefficients.mul.eq_2]
                simp only [Coefficients.interpret.eq_2]
                rw [MultivariateDensePolynomial.Coefficients.mul.eq_2, hadd, hmap]
                rw [Coefficients.interpret.eq_2, interpret_zero, ihas]
          rw [mul.eq_2]
          simp only [interpret.eq_2]
          rw [MultivariateDensePolynomial.mul.eq_2]
          exact congrArg MultivariateDensePolynomial.ofCoefficients (hcoeff ps qs)

theorem interpret_pow {n : ℕ} (p : RawDensePolynomial n) (k : ℕ) :
    interpret (pow p k) = MultivariateDensePolynomial.pow (interpret p) k := by
  induction k with
  | zero => rw [pow.eq_1, MultivariateDensePolynomial.pow.eq_1,
      interpret_constant, RawRat.interpret_one]
  | succ k ih => rw [pow.eq_2, MultivariateDensePolynomial.pow.eq_2, interpret_mul, ih]

end RawDensePolynomial

end Bescovitch
