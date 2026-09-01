/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.RadicalPolynomial

/-!
# Dense polynomials with interval coefficients

This file mirrors the dense radical-polynomial operations with rational interval arithmetic.
Nested `List.Forall₂` relations record that every interval coefficient contains the value of
the corresponding exact coefficient. The relation is preserved by all polynomial constructors.
-/

@[expose] public section

namespace Bescovitch

private theorem forall₂_getD {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} {defaultX : α} {defaultY : β}
    (h : List.Forall₂ R xs ys) (hdefault : R defaultX defaultY) (i : ℕ) :
    R (xs.getD i defaultX) (ys.getD i defaultY) := by
  induction h generalizing i with
  | nil => simpa using hdefault
  | cons hhead htail ih =>
      cases i with
      | zero => simpa using hhead
      | succ i => simpa using ih i

/-- Dense univariate polynomials evaluated directly by rational interval arithmetic. -/
abbrev IntervalUnivariate := List RationalInterval

namespace IntervalUnivariate

/-- Add dense interval coefficient lists, padding the shorter list by zero. -/
def add : IntervalUnivariate → IntervalUnivariate → IntervalUnivariate
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => a.add b :: add p q

/-- Negate every interval coefficient. -/
def neg (p : IntervalUnivariate) : IntervalUnivariate := p.map RationalInterval.neg

/-- Multiply every coefficient by one interval. -/
def scale (a : RationalInterval) (p : IntervalUnivariate) : IntervalUnivariate :=
  p.map (a.mul ·)

/-- Multiply dense interval polynomials by coefficient convolution. -/
def mul : IntervalUnivariate → IntervalUnivariate → IntervalUnivariate
  | [], _ => []
  | a :: p, q => add (scale a q) (RationalInterval.singleton 0 :: mul p q)

/-- A constant univariate interval polynomial. -/
def constant (a : RationalInterval) : IntervalUnivariate := [a]

/-- The univariate indeterminate with singleton interval coefficients. -/
def indeterminate : IntervalUnivariate :=
  [RationalInterval.singleton 0, RationalInterval.singleton 1]

/-- Natural powers of a univariate interval polynomial. -/
def pow (p : IntervalUnivariate) : ℕ → IntervalUnivariate
  | 0 => constant (RationalInterval.singleton 1)
  | k + 1 => mul (pow p k) p

end IntervalUnivariate

/-- An interval coefficient list contains the values of an exact coefficient list. -/
def IntervalUnivariate.Contains {n : ℕ} (input : Fin n → ℝ)
    (P : IntervalUnivariate) (p : RadicalUnivariate n) : Prop :=
  List.Forall₂ (fun I a => I.Contains (a.eval input)) P p

namespace IntervalUnivariate

/-- Coefficientwise containment is preserved by addition. -/
theorem contains_add {n : ℕ} {input : Fin n → ℝ}
    {P Q : IntervalUnivariate} {p q : RadicalUnivariate n}
    (hp : P.Contains input p) (hq : Q.Contains input q) :
    (add P Q).Contains input (RadicalUnivariate.add p q) := by
  induction hp generalizing Q q with
  | nil => simpa [add, RadicalUnivariate.add] using hq
  | cons hhead htail ih =>
      cases hq with
      | nil => exact List.Forall₂.cons hhead htail
      | cons hhead' htail' =>
          exact List.Forall₂.cons (RationalInterval.add_contains hhead hhead')
            (ih htail')

/-- Coefficientwise containment is preserved by negation. -/
theorem contains_neg {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalUnivariate} {p : RadicalUnivariate n} (hp : P.Contains input p) :
    (neg P).Contains input (RadicalUnivariate.neg p) := by
  induction hp with
  | nil => simp [neg, RadicalUnivariate.neg, Contains]
  | cons hhead htail ih =>
      exact List.Forall₂.cons (RationalInterval.neg_contains hhead) ih

/-- Coefficientwise containment is preserved by scalar multiplication. -/
theorem contains_scale {n : ℕ} {input : Fin n → ℝ}
    {A : RationalInterval} {a : RadicalExpression n}
    (ha : A.Contains (a.eval input)) {P : IntervalUnivariate} {p : RadicalUnivariate n}
    (hp : P.Contains input p) :
    (scale A P).Contains input (RadicalUnivariate.scale a p) := by
  induction hp with
  | nil => simp [scale, RadicalUnivariate.scale, Contains]
  | cons hhead htail ih =>
      exact List.Forall₂.cons (RationalInterval.mul_contains ha hhead) ih

/-- Coefficientwise containment is preserved by multiplication. -/
theorem contains_mul {n : ℕ} {input : Fin n → ℝ}
    {P Q : IntervalUnivariate} {p q : RadicalUnivariate n}
    (hp : P.Contains input p) (hq : Q.Contains input q) :
    (mul P Q).Contains input (RadicalUnivariate.mul p q) := by
  induction hp with
  | nil => simp [mul, RadicalUnivariate.mul, Contains]
  | @cons A P a p ha hp ih =>
      apply contains_add (contains_scale ha hq)
      exact List.Forall₂.cons (RationalInterval.singleton_contains 0) ih

/-- A containing interval gives containing constant polynomials. -/
theorem contains_constant {n : ℕ} {input : Fin n → ℝ}
    {A : RationalInterval} {a : RadicalExpression n} (ha : A.Contains (a.eval input)) :
    (constant A).Contains input (RadicalUnivariate.constant a) := by
  exact List.Forall₂.cons ha List.Forall₂.nil

/-- Singleton coefficients enclose the exact univariate indeterminate. -/
theorem contains_indeterminate {n : ℕ} (input : Fin n → ℝ) :
    indeterminate.Contains input (RadicalUnivariate.indeterminate : RadicalUnivariate n) := by
  exact List.Forall₂.cons (RationalInterval.singleton_contains 0) <|
    List.Forall₂.cons (RationalInterval.singleton_contains 1) List.Forall₂.nil

/-- Coefficientwise containment is preserved by natural powers. -/
theorem contains_pow {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalUnivariate} {p : RadicalUnivariate n} (hp : P.Contains input p) :
    ∀ k, (pow P k).Contains input (RadicalUnivariate.pow p k)
  | 0 => contains_constant (RationalInterval.singleton_contains 1)
  | k + 1 => contains_mul (contains_pow hp k) hp

end IntervalUnivariate

/-- Dense bivariate polynomials evaluated directly by rational interval arithmetic. -/
abbrev IntervalBivariate := List IntervalUnivariate

namespace IntervalBivariate

/-- Add dense bivariate interval coefficient lists. -/
def add : IntervalBivariate → IntervalBivariate → IntervalBivariate
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => IntervalUnivariate.add a b :: add p q

/-- Negate every bivariate interval coefficient. -/
def neg (p : IntervalBivariate) : IntervalBivariate := p.map IntervalUnivariate.neg

/-- Multiply every outer coefficient by one interval row. -/
def scaleRow (a : IntervalUnivariate) (p : IntervalBivariate) : IntervalBivariate :=
  p.map (IntervalUnivariate.mul a)

/-- Multiply dense bivariate interval polynomials by convolution. -/
def mul : IntervalBivariate → IntervalBivariate → IntervalBivariate
  | [], _ => []
  | a :: p, q => add (scaleRow a q) ([] :: mul p q)

/-- A constant bivariate interval polynomial. -/
def constant (a : RationalInterval) : IntervalBivariate := [[a]]

/-- The first bivariate indeterminate. -/
def first : IntervalBivariate := [[], [RationalInterval.singleton 1]]

/-- The second bivariate indeterminate. -/
def second : IntervalBivariate :=
  [[RationalInterval.singleton 0, RationalInterval.singleton 1]]

/-- Natural powers of a bivariate interval polynomial. -/
def pow (p : IntervalBivariate) : ℕ → IntervalBivariate
  | 0 => constant (RationalInterval.singleton 1)
  | k + 1 => mul (pow p k) p

end IntervalBivariate

/-- A bivariate interval coefficient list contains an exact coefficient list. -/
def IntervalBivariate.Contains {n : ℕ} (input : Fin n → ℝ)
    (P : IntervalBivariate) (p : RadicalBivariate n) : Prop :=
  List.Forall₂ (IntervalUnivariate.Contains input) P p

namespace IntervalBivariate

/-- Bivariate coefficientwise containment is preserved by addition. -/
theorem contains_add {n : ℕ} {input : Fin n → ℝ}
    {P Q : IntervalBivariate} {p q : RadicalBivariate n}
    (hp : P.Contains input p) (hq : Q.Contains input q) :
    (add P Q).Contains input (RadicalBivariate.add p q) := by
  induction hp generalizing Q q with
  | nil => simpa [add, RadicalBivariate.add] using hq
  | cons hhead htail ih =>
      cases hq with
      | nil => exact List.Forall₂.cons hhead htail
      | cons hhead' htail' =>
          exact List.Forall₂.cons (IntervalUnivariate.contains_add hhead hhead')
            (ih htail')

/-- Bivariate coefficientwise containment is preserved by negation. -/
theorem contains_neg {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalBivariate} {p : RadicalBivariate n} (hp : P.Contains input p) :
    (neg P).Contains input (RadicalBivariate.neg p) := by
  induction hp with
  | nil => simp [neg, RadicalBivariate.neg, Contains]
  | cons hhead htail ih =>
      exact List.Forall₂.cons (IntervalUnivariate.contains_neg hhead) ih

/-- Bivariate coefficientwise containment is preserved by row scaling. -/
theorem contains_scaleRow {n : ℕ} {input : Fin n → ℝ}
    {A : IntervalUnivariate} {a : RadicalUnivariate n}
    (ha : A.Contains input a) {P : IntervalBivariate} {p : RadicalBivariate n}
    (hp : P.Contains input p) :
    (scaleRow A P).Contains input (RadicalBivariate.scaleRow a p) := by
  induction hp with
  | nil => simp [scaleRow, RadicalBivariate.scaleRow, Contains]
  | cons hhead htail ih =>
      exact List.Forall₂.cons (IntervalUnivariate.contains_mul ha hhead) ih

/-- Bivariate coefficientwise containment is preserved by multiplication. -/
theorem contains_mul {n : ℕ} {input : Fin n → ℝ}
    {P Q : IntervalBivariate} {p q : RadicalBivariate n}
    (hp : P.Contains input p) (hq : Q.Contains input q) :
    (mul P Q).Contains input (RadicalBivariate.mul p q) := by
  induction hp with
  | nil => simp [mul, RadicalBivariate.mul, Contains]
  | @cons A P a p ha hp ih =>
      apply contains_add (contains_scaleRow ha hq)
      exact List.Forall₂.cons List.Forall₂.nil ih

/-- A containing interval gives containing bivariate constants. -/
theorem contains_constant {n : ℕ} {input : Fin n → ℝ}
    {A : RationalInterval} {a : RadicalExpression n} (ha : A.Contains (a.eval input)) :
    (constant A).Contains input (RadicalBivariate.constant a) := by
  exact List.Forall₂.cons (IntervalUnivariate.contains_constant ha) List.Forall₂.nil

/-- Singleton coefficients enclose the exact first bivariate indeterminate. -/
theorem contains_first {n : ℕ} (input : Fin n → ℝ) :
    first.Contains input (RadicalBivariate.first : RadicalBivariate n) := by
  exact List.Forall₂.cons List.Forall₂.nil <|
    List.Forall₂.cons
      (IntervalUnivariate.contains_constant (RationalInterval.singleton_contains 1))
      List.Forall₂.nil

/-- Singleton coefficients enclose the exact second bivariate indeterminate. -/
theorem contains_second {n : ℕ} (input : Fin n → ℝ) :
    second.Contains input (RadicalBivariate.second : RadicalBivariate n) := by
  exact List.Forall₂.cons (IntervalUnivariate.contains_indeterminate input)
    List.Forall₂.nil

/-- Bivariate coefficientwise containment is preserved by natural powers. -/
theorem contains_pow {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalBivariate} {p : RadicalBivariate n} (hp : P.Contains input p) :
    ∀ k, (pow P k).Contains input (RadicalBivariate.pow p k)
  | 0 => contains_constant (RationalInterval.singleton_contains 1)
  | k + 1 => contains_mul (contains_pow hp k) hp

end IntervalBivariate

/-- Dense trivariate polynomials evaluated directly by rational interval arithmetic. -/
abbrev IntervalTrivariate := List IntervalBivariate

namespace IntervalTrivariate

/-- Add dense trivariate interval coefficient lists. -/
def add : IntervalTrivariate → IntervalTrivariate → IntervalTrivariate
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => IntervalBivariate.add a b :: add p q

/-- Negate every trivariate interval coefficient. -/
def neg (p : IntervalTrivariate) : IntervalTrivariate := p.map IntervalBivariate.neg

/-- Multiply every outer coefficient by one interval slice. -/
def scaleSlice (a : IntervalBivariate) (p : IntervalTrivariate) : IntervalTrivariate :=
  p.map (IntervalBivariate.mul a)

/-- Multiply dense trivariate interval polynomials by convolution. -/
def mul : IntervalTrivariate → IntervalTrivariate → IntervalTrivariate
  | [], _ => []
  | a :: p, q => add (scaleSlice a q) ([] :: mul p q)

/-- A constant trivariate interval polynomial. -/
def constant (a : RationalInterval) : IntervalTrivariate := [[[a]]]

/-- The first trivariate indeterminate. -/
def first : IntervalTrivariate := [[], [[RationalInterval.singleton 1]]]

/-- The second trivariate indeterminate. -/
def second : IntervalTrivariate := [[[], [RationalInterval.singleton 1]]]

/-- The third trivariate indeterminate. -/
def third : IntervalTrivariate :=
  [[[RationalInterval.singleton 0, RationalInterval.singleton 1]]]

/-- Natural powers of a trivariate interval polynomial. -/
def pow (p : IntervalTrivariate) : ℕ → IntervalTrivariate
  | 0 => constant (RationalInterval.singleton 1)
  | k + 1 => mul (pow p k) p

/-- Read an interval coefficient, returning singleton zero outside the stored lists. -/
def coefficient (p : IntervalTrivariate) (i j k : ℕ) : RationalInterval :=
  ((p.getD i []).getD j []).getD k (RationalInterval.singleton 0)

end IntervalTrivariate

/-- A trivariate interval coefficient list contains an exact coefficient list. -/
def IntervalTrivariate.Contains {n : ℕ} (input : Fin n → ℝ)
    (P : IntervalTrivariate) (p : RadicalTrivariate n) : Prop :=
  List.Forall₂ (IntervalBivariate.Contains input) P p

namespace IntervalTrivariate

/-- Trivariate coefficientwise containment is preserved by addition. -/
theorem contains_add {n : ℕ} {input : Fin n → ℝ}
    {P Q : IntervalTrivariate} {p q : RadicalTrivariate n}
    (hp : P.Contains input p) (hq : Q.Contains input q) :
    (add P Q).Contains input (RadicalTrivariate.add p q) := by
  induction hp generalizing Q q with
  | nil => simpa [add, RadicalTrivariate.add] using hq
  | cons hhead htail ih =>
      cases hq with
      | nil => exact List.Forall₂.cons hhead htail
      | cons hhead' htail' =>
          exact List.Forall₂.cons (IntervalBivariate.contains_add hhead hhead')
            (ih htail')

/-- Trivariate coefficientwise containment is preserved by negation. -/
theorem contains_neg {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalTrivariate} {p : RadicalTrivariate n} (hp : P.Contains input p) :
    (neg P).Contains input (RadicalTrivariate.neg p) := by
  induction hp with
  | nil => simp [neg, RadicalTrivariate.neg, Contains]
  | cons hhead htail ih =>
      exact List.Forall₂.cons (IntervalBivariate.contains_neg hhead) ih

/-- Trivariate coefficientwise containment is preserved by slice scaling. -/
theorem contains_scaleSlice {n : ℕ} {input : Fin n → ℝ}
    {A : IntervalBivariate} {a : RadicalBivariate n}
    (ha : A.Contains input a) {P : IntervalTrivariate} {p : RadicalTrivariate n}
    (hp : P.Contains input p) :
    (scaleSlice A P).Contains input (RadicalTrivariate.scaleSlice a p) := by
  induction hp with
  | nil => simp [scaleSlice, RadicalTrivariate.scaleSlice, Contains]
  | cons hhead htail ih =>
      exact List.Forall₂.cons (IntervalBivariate.contains_mul ha hhead) ih

/-- Trivariate coefficientwise containment is preserved by multiplication. -/
theorem contains_mul {n : ℕ} {input : Fin n → ℝ}
    {P Q : IntervalTrivariate} {p q : RadicalTrivariate n}
    (hp : P.Contains input p) (hq : Q.Contains input q) :
    (mul P Q).Contains input (RadicalTrivariate.mul p q) := by
  induction hp with
  | nil => simp [mul, RadicalTrivariate.mul, Contains]
  | @cons A P a p ha hp ih =>
      apply contains_add (contains_scaleSlice ha hq)
      exact List.Forall₂.cons List.Forall₂.nil ih

/-- A containing interval gives containing trivariate constants. -/
theorem contains_constant {n : ℕ} {input : Fin n → ℝ}
    {A : RationalInterval} {a : RadicalExpression n} (ha : A.Contains (a.eval input)) :
    (constant A).Contains input (RadicalTrivariate.constant a) := by
  exact List.Forall₂.cons (IntervalBivariate.contains_constant ha) List.Forall₂.nil

/-- Singleton coefficients enclose the exact first trivariate indeterminate. -/
theorem contains_first {n : ℕ} (input : Fin n → ℝ) :
    first.Contains input (RadicalTrivariate.first : RadicalTrivariate n) := by
  exact List.Forall₂.cons List.Forall₂.nil <|
    List.Forall₂.cons (IntervalBivariate.contains_constant
      (RationalInterval.singleton_contains 1)) List.Forall₂.nil

/-- Singleton coefficients enclose the exact second trivariate indeterminate. -/
theorem contains_second {n : ℕ} (input : Fin n → ℝ) :
    second.Contains input (RadicalTrivariate.second : RadicalTrivariate n) := by
  exact List.Forall₂.cons (IntervalBivariate.contains_first input) List.Forall₂.nil

/-- Singleton coefficients enclose the exact third trivariate indeterminate. -/
theorem contains_third {n : ℕ} (input : Fin n → ℝ) :
    third.Contains input (RadicalTrivariate.third : RadicalTrivariate n) := by
  exact List.Forall₂.cons (IntervalBivariate.contains_second input) List.Forall₂.nil

/-- Trivariate coefficientwise containment is preserved by natural powers. -/
theorem contains_pow {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalTrivariate} {p : RadicalTrivariate n} (hp : P.Contains input p) :
    ∀ k, (pow P k).Contains input (RadicalTrivariate.pow p k)
  | 0 => contains_constant (RationalInterval.singleton_contains 1)
  | k + 1 => contains_mul (contains_pow hp k) hp

/-- Every padded interval coefficient contains its exact evaluated coefficient. -/
theorem coefficient_contains {n : ℕ} {input : Fin n → ℝ}
    {P : IntervalTrivariate} {p : RadicalTrivariate n} (hp : P.Contains input p)
    (i j k : ℕ) : (P.coefficient i j k).Contains ((p.coefficient i j k).eval input) := by
  have hi : IntervalBivariate.Contains input (P.getD i []) (p.getD i []) :=
    forall₂_getD hp List.Forall₂.nil i
  have hj : IntervalUnivariate.Contains input ((P.getD i []).getD j [])
      ((p.getD i []).getD j []) := forall₂_getD hi List.Forall₂.nil j
  exact forall₂_getD hj (RationalInterval.singleton_contains 0) k

end IntervalTrivariate

end Bescovitch
