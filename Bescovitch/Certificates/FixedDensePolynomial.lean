/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.FixedDyadicInterval
public import Bescovitch.Certificates.MultivariateDensePolynomial

/-!
# Dense polynomials over guarded fixed-width intervals

This module lifts guarded fixed-width dyadic arithmetic coefficientwise to recursive dense
polynomials.  Its representation relation states that every fixed coefficient contains the
corresponding exact rational coefficient.
-/

@[expose] public section

namespace Bescovitch

mutual

/-- Dense multivariable polynomials with guarded fixed-width dyadic coefficients. -/
inductive FixedDensePolynomial (width precision : ℕ) : ℕ → Type
  | base (value : FixedDyadicInterval width precision) : FixedDensePolynomial width precision 0
  | ofCoefficients {n : ℕ} (coefficients : FixedDenseCoefficients width precision n) :
      FixedDensePolynomial width precision (n + 1)

/-- Coefficient sequences for fixed-width dense polynomials. -/
inductive FixedDenseCoefficients (width precision : ℕ) : ℕ → Type
  | nil {n : ℕ} : FixedDenseCoefficients width precision n
  | cons {n : ℕ} (head : FixedDensePolynomial width precision n)
      (tail : FixedDenseCoefficients width precision n) :
      FixedDenseCoefficients width precision n

end

namespace FixedDensePolynomial

variable {width precision : ℕ}

/-- Fixed-width coefficient sequences. -/
abbrev Coefficients := FixedDenseCoefficients

namespace Coefficients

/-- Recursion over the coefficient tail, treating coefficient polynomials as atoms. -/
def recList {n : ℕ} {motive : Coefficients width precision n → Sort*}
    (nil : motive .nil)
    (cons : ∀ head tail, motive tail → motive (.cons head tail)) :
    ∀ coefficients, motive coefficients
  | .nil => nil
  | .cons head tail => cons head tail (recList nil cons tail)

/-- Add two fixed coefficient sequences, padding the shorter sequence by zero. -/
def add {n : ℕ} (operation : FixedDensePolynomial width precision n →
    FixedDensePolynomial width precision n → FixedDensePolynomial width precision n) :
    Coefficients width precision n → Coefficients width precision n →
      Coefficients width precision n
  | .nil, right => right
  | left, .nil => left
  | .cons left lefts, .cons right rights =>
      .cons (operation left right) (add operation lefts rights)

/-- Map an operation over a fixed coefficient sequence. -/
def map {n : ℕ} (operation : FixedDensePolynomial width precision n →
    FixedDensePolynomial width precision n) :
    Coefficients width precision n → Coefficients width precision n
  | .nil => .nil
  | .cons head tail => .cons (operation head) (map operation tail)

/-- Convolve two fixed coefficient sequences. -/
def mul {n : ℕ} (zero : FixedDensePolynomial width precision n)
    (addPolynomial mulPolynomial : FixedDensePolynomial width precision n →
      FixedDensePolynomial width precision n → FixedDensePolynomial width precision n) :
    Coefficients width precision n → Coefficients width precision n →
      Coefficients width precision n
  | .nil, _ => .nil
  | .cons head tail, right =>
      add addPolynomial (map (mulPolynomial head) right)
        (.cons zero (mul zero addPolynomial mulPolynomial tail right))

/-- Read a fixed coefficient, returning zero past the stored support. -/
def get {n : ℕ} (zero : FixedDensePolynomial width precision n) :
    Coefficients width precision n → ℕ → FixedDensePolynomial width precision n
  | .nil, _ => zero
  | .cons head _, 0 => head
  | .cons _ tail, k + 1 => get zero tail k

/-- Check a Boolean predicate on every stored fixed coefficient. -/
def all {n : ℕ} (predicate : FixedDensePolynomial width precision n → Bool) :
    Coefficients width precision n → Bool
  | .nil => true
  | .cons head tail => predicate head && all predicate tail

end Coefficients

/-- The fixed-width zero polynomial. -/
def zero (width precision : ℕ) : (n : ℕ) → FixedDensePolynomial width precision n
  | 0 => .base (FixedDyadicInterval.ofRat width precision 0)
  | _ + 1 => .ofCoefficients .nil

/-- Fixed-width polynomial addition. -/
def add : (n : ℕ) → FixedDensePolynomial width precision n →
    FixedDensePolynomial width precision n → FixedDensePolynomial width precision n
  | 0, .base left, .base right => .base (left.add right)
  | n + 1, .ofCoefficients left, .ofCoefficients right =>
      .ofCoefficients (Coefficients.add (add n) left right)

/-- Fixed-width polynomial negation. -/
def neg : (n : ℕ) → FixedDensePolynomial width precision n →
    FixedDensePolynomial width precision n
  | 0, .base value => .base value.neg
  | n + 1, .ofCoefficients coefficients =>
      .ofCoefficients (Coefficients.map (neg n) coefficients)

/-- Fixed-width polynomial multiplication. -/
def mul : (n : ℕ) → FixedDensePolynomial width precision n →
    FixedDensePolynomial width precision n → FixedDensePolynomial width precision n
  | 0, .base left, .base right => .base (left.mul right)
  | n + 1, .ofCoefficients left, .ofCoefficients right =>
      .ofCoefficients (Coefficients.mul (zero width precision n) (add n) (mul n) left right)

/-- A fixed-width constant polynomial. -/
def constant (width precision : ℕ) : (n : ℕ) → ℚ → FixedDensePolynomial width precision n
  | 0, value => .base (FixedDyadicInterval.ofRat width precision value)
  | n + 1, value => .ofCoefficients (.cons (constant width precision n value) .nil)

/-- Fixed-width scalar multiplication. -/
def scale (value : ℚ) : (n : ℕ) → FixedDensePolynomial width precision n →
    FixedDensePolynomial width precision n
  | 0, .base p => .base ((FixedDyadicInterval.ofRat width precision value).mul p)
  | n + 1, .ofCoefficients coefficients =>
      .ofCoefficients (Coefficients.map (scale value n) coefficients)

/-- A fixed-width coordinate variable. -/
def coordinate (width precision : ℕ) : {n : ℕ} → Fin n →
    FixedDensePolynomial width precision n
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases
      (.ofCoefficients (.cons (zero width precision n)
        (.cons (constant width precision n 1) .nil)))
      (fun j ↦ .ofCoefficients (.cons (coordinate width precision j) .nil)) i

/-- Natural powers of a fixed-width dense polynomial. -/
def pow {n : ℕ} (p : FixedDensePolynomial width precision n) :
    ℕ → FixedDensePolynomial width precision n
  | 0 => constant width precision n 1
  | k + 1 => mul n (pow p k) p

/-- Check that every stored fixed coefficient was computed without overflow. -/
def allOk : {n : ℕ} → FixedDensePolynomial width precision n → Bool
  | 0, .base value => value.ok
  | _ + 1, .ofCoefficients coefficients => Coefficients.all allOk coefficients

mutual

/-- Coefficientwise containment of an exact rational dense polynomial. -/
def Represents : {n : ℕ} → FixedDensePolynomial width precision n →
    MultivariateDensePolynomial n → Prop
  | 0, .base fixed, .base exact =>
      ∃ dyadic : DyadicInterval precision,
        fixed.Represents dyadic ∧ dyadic.Contains exact
  | _ + 1, .ofCoefficients fixed, .ofCoefficients exact =>
      FixedDenseCoefficients.Represents fixed exact

/-- Coefficientwise containment for fixed and exact coefficient sequences. -/
def FixedDenseCoefficients.Represents : {n : ℕ} →
    FixedDenseCoefficients width precision n →
    MultivariateDensePolynomial.Coefficients n → Prop
  | _, .nil, .nil => True
  | _, .cons fixedHead fixedTail, .cons exactHead exactTail =>
      Represents fixedHead exactHead ∧ FixedDenseCoefficients.Represents fixedTail exactTail
  | _, _, _ => False

end

private theorem coefficients_map_represents {n : ℕ}
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
  | cons fixedHead fixedTail tailIH =>
      cases exact with
      | nil => contradiction
      | cons exactHead exactTail =>
          rcases h with ⟨hhead, htail⟩
          simp only [Coefficients.map, Coefficients.all, Bool.and_eq_true] at hok
          exact ⟨hop hhead hok.1, tailIH htail hok.2⟩

private theorem coefficients_all_left_of_all_add {n : ℕ}
    {predicate : FixedDensePolynomial width precision n → Bool}
    {operation : FixedDensePolynomial width precision n →
      FixedDensePolynomial width precision n → FixedDensePolynomial width precision n}
    (hop : ∀ left right, predicate (operation left right) = true → predicate left = true)
    {left right : Coefficients width precision n}
    (h : Coefficients.all predicate (Coefficients.add operation left right) = true) :
    Coefficients.all predicate left = true := by
  induction left using Coefficients.recList generalizing right with
  | nil => rfl
  | cons left lefts ih =>
      cases right with
      | nil => exact h
      | cons right rights =>
          simp only [Coefficients.add, Coefficients.all, Bool.and_eq_true] at h ⊢
          exact ⟨hop left right h.1, ih h.2⟩

private theorem coefficients_all_right_of_all_add {n : ℕ}
    {predicate : FixedDensePolynomial width precision n → Bool}
    {operation : FixedDensePolynomial width precision n →
      FixedDensePolynomial width precision n → FixedDensePolynomial width precision n}
    (hop : ∀ left right, predicate (operation left right) = true → predicate right = true)
    {left right : Coefficients width precision n}
    (h : Coefficients.all predicate (Coefficients.add operation left right) = true) :
    Coefficients.all predicate right = true := by
  induction left using Coefficients.recList generalizing right with
  | nil => exact h
  | cons left lefts ih =>
      cases right with
      | nil => rfl
      | cons right rights =>
          simp only [Coefficients.add, Coefficients.all, Bool.and_eq_true] at h ⊢
          exact ⟨hop left right h.1, ih h.2⟩

private theorem fixed_add_ok_left {left right : FixedDyadicInterval width precision}
    (h : (left.add right).ok = true) : left.ok = true := by
  simp only [FixedDyadicInterval.add, FixedDyadicInterval.additionSafe,
    Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1

private theorem fixed_add_ok_right {left right : FixedDyadicInterval width precision}
    (h : (left.add right).ok = true) : right.ok = true := by
  simp only [FixedDyadicInterval.add, FixedDyadicInterval.additionSafe,
    Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

private theorem fixed_mul_ok_left {left right : FixedDyadicInterval width precision}
    (h : (left.mul right).ok = true) : left.ok = true := by
  simp only [FixedDyadicInterval.mul, FixedDyadicInterval.multiplicationSafe,
    Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

/-- A successful polynomial sum has a successful left input. -/
theorem all_ok_left_of_add {n : ℕ} {left right : FixedDensePolynomial width precision n}
    (h : allOk (add n left right) = true) : allOk left = true := by
  induction n with
  | zero =>
      cases left with
      | base left =>
          cases right with
          | base right => exact fixed_add_ok_left h
  | succ n ih =>
      cases left with
      | ofCoefficients left =>
          cases right with
          | ofCoefficients right =>
              exact coefficients_all_left_of_all_add (fun p q ↦ ih) h

/-- A successful polynomial sum has a successful right input. -/
theorem all_ok_right_of_add {n : ℕ} {left right : FixedDensePolynomial width precision n}
    (h : allOk (add n left right) = true) : allOk right = true := by
  induction n with
  | zero =>
      cases left with
      | base left =>
          cases right with
          | base right => exact fixed_add_ok_right h
  | succ n ih =>
      cases left with
      | ofCoefficients left =>
          cases right with
          | ofCoefficients right =>
              exact coefficients_all_right_of_all_add (fun p q ↦ ih) h

/-- Successful fixed-width addition preserves coefficientwise containment. -/
theorem add_represents {n : ℕ} {left right : FixedDensePolynomial width precision n}
    {exactLeft exactRight : MultivariateDensePolynomial n}
    (hleft : Represents left exactLeft) (hright : Represents right exactRight)
    (hok : allOk (add n left right) = true) :
    Represents (add n left right) (MultivariateDensePolynomial.add n exactLeft exactRight) := by
  induction n with
  | zero =>
      cases left with
      | base left =>
          cases right with
          | base right =>
              cases exactLeft with
              | base exactLeft =>
                  cases exactRight with
                  | base exactRight =>
                      rcases hleft with ⟨leftDyadic, hleft, hleftContains⟩
                      rcases hright with ⟨rightDyadic, hright, hrightContains⟩
                      exact ⟨leftDyadic.add rightDyadic,
                        FixedDyadicInterval.add_represents hleft hright hok,
                        DyadicInterval.add_contains hleftContains hrightContains⟩
  | succ n ih =>
      cases left with
      | ofCoefficients left =>
          cases right with
          | ofCoefficients right =>
              cases exactLeft with
              | ofCoefficients exactLeft =>
                  cases exactRight with
                  | ofCoefficients exactRight =>
                      change FixedDenseCoefficients.Represents
                        (Coefficients.add (add n) left right)
                        (MultivariateDensePolynomial.Coefficients.add
                          (MultivariateDensePolynomial.add n) exactLeft exactRight)
                      induction left using Coefficients.recList generalizing
                          exactLeft right exactRight with
                      | nil =>
                          cases exactLeft with
                          | nil =>
                              simpa only [Represents, Coefficients.add,
                                MultivariateDensePolynomial.Coefficients.add] using hright
                          | cons => contradiction
                      | cons leftHead leftTail tailIH =>
                          cases exactLeft with
                          | nil => contradiction
                          | cons exactLeftHead exactLeftTail =>
                              rcases hleft with ⟨hleftHead, hleftTail⟩
                              cases right with
                              | nil =>
                                  cases exactRight with
                                  | nil => exact ⟨hleftHead, hleftTail⟩
                                  | cons => contradiction
                              | cons rightHead rightTail =>
                                  cases exactRight with
                                  | nil => contradiction
                                  | cons exactRightHead exactRightTail =>
                                      rcases hright with ⟨hrightHead, hrightTail⟩
                                      simp only [add, allOk, Coefficients.add,
                                        Coefficients.all, Bool.and_eq_true] at hok
                                      exact ⟨ih hleftHead hrightHead hok.1,
                                        tailIH rightTail hok.2 exactLeftTail
                                          (by simpa only [Represents] using hleftTail)
                                          exactRightTail
                                          (by simpa only [Represents] using hrightTail)⟩

/-- Successful fixed-width negation preserves coefficientwise containment. -/
theorem neg_represents {n : ℕ} {fixed : FixedDensePolynomial width precision n}
    {exact : MultivariateDensePolynomial n} (hfixed : Represents fixed exact)
    (hok : allOk (neg n fixed) = true) :
    Represents (neg n fixed) (MultivariateDensePolynomial.neg n exact) := by
  induction n with
  | zero =>
      cases fixed with
      | base fixed =>
          cases exact with
          | base exact =>
              rcases hfixed with ⟨dyadic, hfixed, hexact⟩
              exact ⟨dyadic.neg, FixedDyadicInterval.neg_represents hfixed hok,
                DyadicInterval.neg_contains hexact⟩
  | succ n ih =>
      cases fixed with
      | ofCoefficients fixed =>
          cases exact with
          | ofCoefficients exact =>
              change FixedDenseCoefficients.Represents
                (Coefficients.map (neg n) fixed)
                (MultivariateDensePolynomial.Coefficients.map
                  (MultivariateDensePolynomial.neg n) exact)
              induction fixed using Coefficients.recList generalizing exact with
              | nil =>
                  cases exact with
                  | nil => trivial
                  | cons => contradiction
              | cons fixedHead fixedTail tailIH =>
                  cases exact with
                  | nil => contradiction
                  | cons exactHead exactTail =>
                      rcases hfixed with ⟨hfixedHead, hfixedTail⟩
                      simp only [neg, allOk, Coefficients.map, Coefficients.all,
                        Bool.and_eq_true] at hok
                      exact ⟨ih hfixedHead hok.1,
                        tailIH hok.2 exactTail
                          (by simpa only [Represents] using hfixedTail)⟩

/-- Coefficientwise containment entails successful fixed-width arithmetic. -/
theorem all_ok_of_represents {n : ℕ} {fixed : FixedDensePolynomial width precision n}
    {exact : MultivariateDensePolynomial n} (h : Represents fixed exact) :
    allOk fixed = true := by
  induction n with
  | zero =>
      cases fixed with
      | base fixed =>
          cases exact with
          | base exact =>
              rcases h with ⟨dyadic, hfixed, _⟩
              exact hfixed.1
  | succ n ih =>
      cases fixed with
      | ofCoefficients fixed =>
          cases exact with
          | ofCoefficients exact =>
              induction fixed using Coefficients.recList generalizing exact with
              | nil => rfl
              | cons fixedHead fixedTail tailIH =>
                  cases exact with
                  | nil => contradiction
                  | cons exactHead exactTail =>
                      rcases h with ⟨hfixedHead, hfixedTail⟩
                      simp only [allOk, Coefficients.all, Bool.and_eq_true]
                      exact ⟨ih hfixedHead,
                        tailIH exactTail (by simpa only [Represents] using hfixedTail)⟩

/-- A successful fixed zero polynomial contains the exact zero polynomial. -/
theorem zero_represents (width precision n : ℕ)
    (hok : allOk (zero width precision n) = true) :
    Represents (zero width precision n) (MultivariateDensePolynomial.zero n) := by
  cases n with
  | zero =>
      exact ⟨DyadicInterval.ofRat precision 0,
        FixedDyadicInterval.ofRat_represents width precision 0 hok,
        DyadicInterval.ofRat_contains precision 0⟩
  | succ n => trivial

/-- A successful fixed constant contains the exact constant polynomial. -/
theorem constant_represents (width precision n : ℕ) (value : ℚ)
    (hok : allOk (constant width precision n value) = true) :
    Represents (constant width precision n value)
      (MultivariateDensePolynomial.constant n value) := by
  induction n with
  | zero =>
      exact ⟨DyadicInterval.ofRat precision value,
        FixedDyadicInterval.ofRat_represents width precision value hok,
        DyadicInterval.ofRat_contains precision value⟩
  | succ n ih =>
      simp only [constant, allOk, Coefficients.all, Bool.and_true] at hok
      exact ⟨ih hok, trivial⟩

/-- Successful fixed-width multiplication preserves coefficientwise containment. -/
theorem mul_represents {n : ℕ} {left right : FixedDensePolynomial width precision n}
    {exactLeft exactRight : MultivariateDensePolynomial n}
    (hleft : Represents left exactLeft) (hright : Represents right exactRight)
    (hok : allOk (mul n left right) = true) :
    Represents (mul n left right) (MultivariateDensePolynomial.mul n exactLeft exactRight) := by
  induction n with
  | zero =>
      cases left with
      | base left =>
          cases right with
          | base right =>
              cases exactLeft with
              | base exactLeft =>
                  cases exactRight with
                  | base exactRight =>
                      rcases hleft with ⟨leftDyadic, hleft, hleftContains⟩
                      rcases hright with ⟨rightDyadic, hright, hrightContains⟩
                      exact ⟨leftDyadic.mul rightDyadic,
                        FixedDyadicInterval.mul_represents hleft hright hok,
                        DyadicInterval.mul_contains hleftContains hrightContains⟩
  | succ n ih =>
      cases left with
      | ofCoefficients left =>
          cases right with
          | ofCoefficients right =>
              cases exactLeft with
              | ofCoefficients exactLeft =>
                  cases exactRight with
                  | ofCoefficients exactRight =>
                      change FixedDenseCoefficients.Represents
                        (Coefficients.mul (zero width precision n) (add n) (mul n) left right)
                        (MultivariateDensePolynomial.Coefficients.mul
                          (MultivariateDensePolynomial.zero n)
                          (MultivariateDensePolynomial.add n)
                          (MultivariateDensePolynomial.mul n) exactLeft exactRight)
                      induction left using Coefficients.recList generalizing exactLeft with
                      | nil =>
                          cases exactLeft with
                          | nil => trivial
                          | cons => contradiction
                      | cons leftHead leftTail tailIH =>
                          cases exactLeft with
                          | nil => contradiction
                          | cons exactLeftHead exactLeftTail =>
                              rcases hleft with ⟨hleftHead, hleftTail⟩
                              let fixedFirst : FixedDensePolynomial width precision (n + 1) :=
                                .ofCoefficients (Coefficients.map (mul n leftHead) right)
                              let exactFirst : MultivariateDensePolynomial (n + 1) :=
                                .ofCoefficients
                                  (MultivariateDensePolynomial.Coefficients.map
                                    (MultivariateDensePolynomial.mul n exactLeftHead) exactRight)
                              let fixedSecond : FixedDensePolynomial width precision (n + 1) :=
                                .ofCoefficients (.cons (zero width precision n)
                                  (Coefficients.mul (zero width precision n) (add n) (mul n)
                                    leftTail right))
                              let exactSecond : MultivariateDensePolynomial (n + 1) :=
                                .ofCoefficients (.cons (MultivariateDensePolynomial.zero n)
                                  (MultivariateDensePolynomial.Coefficients.mul
                                    (MultivariateDensePolynomial.zero n)
                                    (MultivariateDensePolynomial.add n)
                                    (MultivariateDensePolynomial.mul n) exactLeftTail exactRight))
                              have hok' : allOk (add (n + 1) fixedFirst fixedSecond) = true := by
                                simpa only [fixedFirst, fixedSecond, add, mul,
                                  Coefficients.mul] using hok
                              have hfirstOk : allOk fixedFirst = true := by
                                exact all_ok_left_of_add hok'
                              have hsecondOk : allOk fixedSecond = true := by
                                exact all_ok_right_of_add hok'
                              have hfirst : Represents fixedFirst exactFirst := by
                                change FixedDenseCoefficients.Represents
                                  (Coefficients.map (mul n leftHead) right)
                                  (MultivariateDensePolynomial.Coefficients.map
                                    (MultivariateDensePolynomial.mul n exactLeftHead) exactRight)
                                apply coefficients_map_represents
                                  (fun hright hmulOk ↦ ih hleftHead hright hmulOk) hright
                                simpa only [fixedFirst, allOk] using hfirstOk
                              have hsecond : Represents fixedSecond exactSecond := by
                                simp only [fixedSecond, exactSecond, Represents]
                                simp only [fixedSecond, allOk, Coefficients.all,
                                  Bool.and_eq_true] at hsecondOk
                                exact ⟨zero_represents width precision n hsecondOk.1,
                                  tailIH hsecondOk.2 exactLeftTail
                                    (by simpa only [Represents] using hleftTail)⟩
                              exact add_represents hfirst hsecond hok'

/-- Successful fixed-width scaling preserves coefficientwise containment. -/
theorem scale_represents (value : ℚ) {n : ℕ}
    {fixed : FixedDensePolynomial width precision n}
    {exact : MultivariateDensePolynomial n} (hfixed : Represents fixed exact)
    (hok : allOk (scale value n fixed) = true) :
    Represents (scale value n fixed) (MultivariateDensePolynomial.scale value n exact) := by
  induction n with
  | zero =>
      cases fixed with
      | base fixed =>
          cases exact with
          | base exact =>
              rcases hfixed with ⟨dyadic, hfixed, hexact⟩
              let scalar := DyadicInterval.ofRat precision value
              have hscalar : (FixedDyadicInterval.ofRat width precision value).Represents scalar :=
                FixedDyadicInterval.ofRat_represents width precision value
                  (fixed_mul_ok_left hok)
              exact ⟨scalar.mul dyadic,
                FixedDyadicInterval.mul_represents hscalar hfixed hok,
                DyadicInterval.mul_contains (DyadicInterval.ofRat_contains precision value)
                  hexact⟩
  | succ n ih =>
      cases fixed with
      | ofCoefficients fixed =>
          cases exact with
          | ofCoefficients exact =>
              change FixedDenseCoefficients.Represents
                (Coefficients.map (scale value n) fixed)
                (MultivariateDensePolynomial.Coefficients.map
                  (MultivariateDensePolynomial.scale value n) exact)
              apply coefficients_map_represents (fun h hscaleOk ↦ ih h hscaleOk) hfixed
              exact hok

/-- A successful fixed coordinate polynomial contains the exact coordinate polynomial. -/
theorem coordinate_represents (width precision : ℕ) {n : ℕ} (i : Fin n)
    (hok : allOk (coordinate width precision i) = true) :
    Represents (coordinate width precision i) (MultivariateDensePolynomial.coordinate i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      revert hok
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · intro hok
        simp only [coordinate, Fin.cases_zero, allOk, Coefficients.all,
          Bool.and_eq_true, Bool.and_true] at hok
        exact ⟨zero_represents width precision n hok.1,
          constant_represents width precision n 1 hok.2, trivial⟩
      · intro hok
        simp only [coordinate, Fin.cases_succ, allOk, Coefficients.all,
          Bool.and_true] at hok
        exact ⟨ih j hok, trivial⟩

/-- Fixed powers contain exact powers when every intermediate product succeeds. -/
theorem pow_represents {n k : ℕ} {fixed : FixedDensePolynomial width precision n}
    {exact : MultivariateDensePolynomial n} (hfixed : Represents fixed exact)
    (hok : ∀ j, j ≤ k → allOk (pow fixed j) = true) :
    Represents (pow fixed k) (MultivariateDensePolynomial.pow exact k) := by
  induction k with
  | zero => exact constant_represents width precision n 1 (hok 0 le_rfl)
  | succ k ih =>
      exact mul_represents (ih fun j hj ↦ hok j (hj.trans (Nat.le_succ k))) hfixed
        (hok (k + 1) le_rfl)

end FixedDensePolynomial

end Bescovitch
