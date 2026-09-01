/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.DyadicInterval
public import Bescovitch.Certificates.IntervalPolynomial

/-!
# Dense polynomials over fixed-precision dyadic intervals

The arithmetic in this module rounds every scalar operation outwards.  The accompanying
coefficientwise relation proves that each result contains the corresponding exact rational
interval polynomial.
-/

@[expose] public section

namespace Bescovitch

variable {precision : ℕ}

namespace DyadicInterval

/-- A dyadic interval contains both endpoints of an ordinary rational interval. -/
def Widens (D : DyadicInterval precision) (I : RationalInterval) : Prop :=
  D.Contains I.lower ∧ D.Contains I.upper

/-- Outward rounding widens the original rational interval. -/
theorem ofInterval_widens (precision : ℕ) (I : RationalInterval) :
    (ofInterval precision I).Widens I :=
  ⟨ofInterval_contains ⟨le_rfl, I.lower_le_upper⟩,
    ofInterval_contains ⟨I.lower_le_upper, le_rfl⟩⟩

/-- Dyadic addition preserves interval widening. -/
theorem add_widens {D E : DyadicInterval precision} {I J : RationalInterval}
    (hD : D.Widens I) (hE : E.Widens J) : (D.add E).Widens (I.add J) :=
  ⟨add_contains hD.1 hE.1, add_contains hD.2 hE.2⟩

/-- Dyadic negation preserves interval widening. -/
theorem neg_widens {D : DyadicInterval precision} {I : RationalInterval}
    (hD : D.Widens I) : D.neg.Widens I.neg :=
  ⟨neg_contains hD.2, neg_contains hD.1⟩

/-- Dyadic multiplication preserves interval widening. -/
theorem mul_widens {D E : DyadicInterval precision} {I J : RationalInterval}
    (hD : D.Widens I) (hE : E.Widens J) : (D.mul E).Widens (I.mul J) := by
  have hll := mul_contains hD.1 hE.1
  have hlu := mul_contains hD.1 hE.2
  have hul := mul_contains hD.2 hE.1
  have huu := mul_contains hD.2 hE.2
  constructor
  · constructor
    · exact le_min (le_min hll.1 hlu.1) (le_min hul.1 huu.1)
    · exact (min_le_left _ _).trans <| (min_le_left _ _).trans hll.2
  · constructor
    · exact hll.1.trans <| (le_max_left _ _).trans (le_max_left _ _)
    · exact max_le (max_le hll.2 hlu.2) (max_le hul.2 huu.2)

end DyadicInterval

/-- Dense univariate polynomials with dyadic interval coefficients. -/
abbrev DyadicIntervalUnivariate (precision : ℕ) := List (DyadicInterval precision)

namespace DyadicIntervalUnivariate

/-- Coefficientwise outward widening of an exact interval polynomial. -/
def Widens : DyadicIntervalUnivariate precision → IntervalUnivariate → Prop
  | [], [] => True
  | D :: Ds, I :: Is => D.Widens I ∧ Widens Ds Is
  | _, _ => False

/-- Polynomial addition with dyadic interval coefficients. -/
def add : DyadicIntervalUnivariate precision → DyadicIntervalUnivariate precision →
    DyadicIntervalUnivariate precision
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => a.add b :: add p q

/-- Polynomial negation with dyadic interval coefficients. -/
def neg (p : DyadicIntervalUnivariate precision) : DyadicIntervalUnivariate precision :=
  p.map DyadicInterval.neg

/-- Scalar multiplication of a dyadic interval polynomial. -/
def scale (a : DyadicInterval precision) (p : DyadicIntervalUnivariate precision) :
    DyadicIntervalUnivariate precision := p.map (a.mul ·)

/-- Polynomial multiplication with dyadic interval coefficients. -/
def mul : DyadicIntervalUnivariate precision → DyadicIntervalUnivariate precision →
    DyadicIntervalUnivariate precision
  | [], _ => []
  | a :: p, q => add (scale a q) (DyadicInterval.ofRat precision 0 :: mul p q)

/-- A constant dyadic interval polynomial. -/
def constant (a : DyadicInterval precision) : DyadicIntervalUnivariate precision := [a]

/-- Natural powers of a dyadic interval polynomial. -/
def pow (p : DyadicIntervalUnivariate precision) : ℕ → DyadicIntervalUnivariate precision
  | 0 => constant (DyadicInterval.ofRat precision 1)
  | n + 1 => mul (pow p n) p

/-- Corresponding coefficients widen each other, including the zero padding. -/
theorem getD_widens {P : DyadicIntervalUnivariate precision} {p : IntervalUnivariate}
    (hP : Widens P p) (i : ℕ) :
    (P.getD i (DyadicInterval.ofRat precision 0)).Widens
      (p.getD i (.singleton 0)) := by
  induction P generalizing p i with
  | nil =>
      cases p
      · exact DyadicInterval.ofInterval_widens precision (.singleton 0)
      · contradiction
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          cases i with
          | zero => exact hP.1
          | succ i => exact ih hP.2 i

/-- Dyadic polynomial addition preserves coefficientwise widening. -/
theorem add_widens {P Q : DyadicIntervalUnivariate precision}
    {p q : IntervalUnivariate} (hP : Widens P p) (hQ : Widens Q q) :
    Widens (add P Q) (IntervalUnivariate.add p q) := by
  induction P generalizing Q p q with
  | nil => cases p <;> cases Q <;> cases q <;> simp_all [Widens, add,
      IntervalUnivariate.add]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          cases Q with
          | nil => cases q <;> simp_all [Widens, add, IntervalUnivariate.add]
          | cons B Q =>
              cases q with
              | nil => contradiction
              | cons b q =>
                  exact ⟨DyadicInterval.add_widens hP.1 hQ.1,
                    ih hP.2 hQ.2⟩

/-- Dyadic polynomial negation preserves coefficientwise widening. -/
theorem neg_widens {P : DyadicIntervalUnivariate precision} {p : IntervalUnivariate}
    (hP : Widens P p) : Widens (neg P) (IntervalUnivariate.neg p) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, neg, IntervalUnivariate.neg]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p => exact ⟨DyadicInterval.neg_widens hP.1, ih hP.2⟩

/-- Dyadic scalar multiplication preserves coefficientwise widening. -/
theorem scale_widens {A : DyadicInterval precision} {P : DyadicIntervalUnivariate precision}
    {a : RationalInterval} {p : IntervalUnivariate}
    (hA : A.Widens a) (hP : Widens P p) :
    Widens (scale A P) (IntervalUnivariate.scale a p) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, scale, IntervalUnivariate.scale]
  | cons B P ih =>
      cases p with
      | nil => contradiction
      | cons b p => exact ⟨DyadicInterval.mul_widens hA hP.1, ih hP.2⟩

/-- Dyadic polynomial multiplication preserves coefficientwise widening. -/
theorem mul_widens {P Q : DyadicIntervalUnivariate precision}
    {p q : IntervalUnivariate} (hP : Widens P p) (hQ : Widens Q q) :
    Widens (mul P Q) (IntervalUnivariate.mul p q) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, mul, IntervalUnivariate.mul]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          apply add_widens (scale_widens hP.1 hQ)
          exact ⟨DyadicInterval.ofInterval_widens precision (.singleton 0), ih hP.2⟩

/-- Dyadic constants widen exact interval constants. -/
theorem constant_widens {A : DyadicInterval precision} {a : RationalInterval}
    (hA : A.Widens a) : Widens (constant A) (IntervalUnivariate.constant a) :=
  ⟨hA, trivial⟩

/-- Dyadic natural powers preserve coefficientwise widening. -/
theorem pow_widens {P : DyadicIntervalUnivariate precision} {p : IntervalUnivariate}
    (hP : Widens P p) (n : ℕ) :
    Widens (pow P n) (IntervalUnivariate.pow p n) := by
  induction n with
  | zero => exact constant_widens (DyadicInterval.ofInterval_widens precision (.singleton 1))
  | succ n ih => exact mul_widens ih hP

end DyadicIntervalUnivariate

/-- Dense bivariate polynomials with dyadic interval coefficients. -/
abbrev DyadicIntervalBivariate (precision : ℕ) :=
  List (DyadicIntervalUnivariate precision)

namespace DyadicIntervalBivariate

/-- Coefficientwise outward widening of an exact bivariate interval polynomial. -/
def Widens : DyadicIntervalBivariate precision → IntervalBivariate → Prop
  | [], [] => True
  | D :: Ds, I :: Is => D.Widens I ∧ Widens Ds Is
  | _, _ => False

/-- Bivariate polynomial addition with dyadic interval coefficients. -/
def add : DyadicIntervalBivariate precision → DyadicIntervalBivariate precision →
    DyadicIntervalBivariate precision
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => DyadicIntervalUnivariate.add a b :: add p q

/-- Bivariate polynomial negation with dyadic interval coefficients. -/
def neg (p : DyadicIntervalBivariate precision) : DyadicIntervalBivariate precision :=
  p.map DyadicIntervalUnivariate.neg

/-- Multiply each outer coefficient row by one dyadic polynomial. -/
def scaleRow (a : DyadicIntervalUnivariate precision)
    (p : DyadicIntervalBivariate precision) : DyadicIntervalBivariate precision :=
  p.map (DyadicIntervalUnivariate.mul a)

/-- Bivariate polynomial multiplication with dyadic interval coefficients. -/
def mul : DyadicIntervalBivariate precision → DyadicIntervalBivariate precision →
    DyadicIntervalBivariate precision
  | [], _ => []
  | a :: p, q => add (scaleRow a q) ([] :: mul p q)

/-- A constant bivariate dyadic interval polynomial. -/
def constant (a : DyadicInterval precision) : DyadicIntervalBivariate precision := [[a]]

/-- Natural powers of a bivariate dyadic interval polynomial. -/
def pow (p : DyadicIntervalBivariate precision) : ℕ → DyadicIntervalBivariate precision
  | 0 => constant (DyadicInterval.ofRat precision 1)
  | n + 1 => mul (pow p n) p

/-- Corresponding outer rows widen each other, including zero padding. -/
theorem getD_widens {P : DyadicIntervalBivariate precision} {p : IntervalBivariate}
    (hP : Widens P p) (i : ℕ) : (P.getD i []).Widens (p.getD i []) := by
  induction P generalizing p i with
  | nil =>
      cases p with
      | nil => trivial
      | cons a p => contradiction
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          cases i with
          | zero => exact hP.1
          | succ i => exact ih hP.2 i

/-- Dyadic bivariate addition preserves coefficientwise widening. -/
theorem add_widens {P Q : DyadicIntervalBivariate precision}
    {p q : IntervalBivariate} (hP : Widens P p) (hQ : Widens Q q) :
    Widens (add P Q) (IntervalBivariate.add p q) := by
  induction P generalizing Q p q with
  | nil => cases p <;> cases Q <;> cases q <;> simp_all [Widens, add,
      IntervalBivariate.add]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          cases Q with
          | nil => cases q <;> simp_all [Widens, add, IntervalBivariate.add]
          | cons B Q =>
              cases q with
              | nil => contradiction
              | cons b q =>
                  exact ⟨DyadicIntervalUnivariate.add_widens hP.1 hQ.1,
                    ih hP.2 hQ.2⟩

/-- Dyadic bivariate negation preserves coefficientwise widening. -/
theorem neg_widens {P : DyadicIntervalBivariate precision} {p : IntervalBivariate}
    (hP : Widens P p) : Widens (neg P) (IntervalBivariate.neg p) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, neg, IntervalBivariate.neg]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p => exact ⟨DyadicIntervalUnivariate.neg_widens hP.1, ih hP.2⟩

/-- Dyadic row scaling preserves coefficientwise widening. -/
theorem scaleRow_widens
    {A : DyadicIntervalUnivariate precision} {P : DyadicIntervalBivariate precision}
    {a : IntervalUnivariate} {p : IntervalBivariate}
    (hA : A.Widens a) (hP : Widens P p) :
    Widens (scaleRow A P) (IntervalBivariate.scaleRow a p) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, scaleRow, IntervalBivariate.scaleRow]
  | cons B P ih =>
      cases p with
      | nil => contradiction
      | cons b p => exact ⟨DyadicIntervalUnivariate.mul_widens hA hP.1, ih hP.2⟩

/-- Dyadic bivariate multiplication preserves coefficientwise widening. -/
theorem mul_widens {P Q : DyadicIntervalBivariate precision}
    {p q : IntervalBivariate} (hP : Widens P p) (hQ : Widens Q q) :
    Widens (mul P Q) (IntervalBivariate.mul p q) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, mul, IntervalBivariate.mul]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          apply add_widens (scaleRow_widens hP.1 hQ)
          exact ⟨trivial, ih hP.2⟩

/-- Dyadic bivariate constants widen exact interval constants. -/
theorem constant_widens {A : DyadicInterval precision} {a : RationalInterval}
    (hA : A.Widens a) : Widens (constant A) (IntervalBivariate.constant a) :=
  ⟨⟨hA, trivial⟩, trivial⟩

/-- Dyadic bivariate natural powers preserve coefficientwise widening. -/
theorem pow_widens {P : DyadicIntervalBivariate precision} {p : IntervalBivariate}
    (hP : Widens P p) (n : ℕ) : Widens (pow P n) (IntervalBivariate.pow p n) := by
  induction n with
  | zero => exact constant_widens (DyadicInterval.ofInterval_widens precision (.singleton 1))
  | succ n ih => exact mul_widens ih hP

end DyadicIntervalBivariate

/-- Dense trivariate polynomials with dyadic interval coefficients. -/
abbrev DyadicIntervalTrivariate (precision : ℕ) :=
  List (DyadicIntervalBivariate precision)

namespace DyadicIntervalTrivariate

/-- Coefficientwise outward widening of an exact trivariate interval polynomial. -/
def Widens : DyadicIntervalTrivariate precision → IntervalTrivariate → Prop
  | [], [] => True
  | D :: Ds, I :: Is => D.Widens I ∧ Widens Ds Is
  | _, _ => False

/-- Trivariate polynomial addition with dyadic interval coefficients. -/
def add : DyadicIntervalTrivariate precision → DyadicIntervalTrivariate precision →
    DyadicIntervalTrivariate precision
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => DyadicIntervalBivariate.add a b :: add p q

/-- Trivariate polynomial negation with dyadic interval coefficients. -/
def neg (p : DyadicIntervalTrivariate precision) : DyadicIntervalTrivariate precision :=
  p.map DyadicIntervalBivariate.neg

/-- Multiply each outer coefficient slice by one dyadic bivariate polynomial. -/
def scaleSlice (a : DyadicIntervalBivariate precision)
    (p : DyadicIntervalTrivariate precision) : DyadicIntervalTrivariate precision :=
  p.map (DyadicIntervalBivariate.mul a)

/-- Trivariate polynomial multiplication with dyadic interval coefficients. -/
def mul : DyadicIntervalTrivariate precision → DyadicIntervalTrivariate precision →
    DyadicIntervalTrivariate precision
  | [], _ => []
  | a :: p, q => add (scaleSlice a q) ([] :: mul p q)

/-- A constant trivariate dyadic interval polynomial. -/
def constant (a : DyadicInterval precision) : DyadicIntervalTrivariate precision := [[[a]]]

/-- The first trivariate coordinate polynomial. -/
def first (precision : ℕ) : DyadicIntervalTrivariate precision :=
  [[], [[DyadicInterval.ofRat precision 1]]]

/-- The second trivariate coordinate polynomial. -/
def second (precision : ℕ) : DyadicIntervalTrivariate precision :=
  [[[], [DyadicInterval.ofRat precision 1]]]

/-- The third trivariate coordinate polynomial. -/
def third (precision : ℕ) : DyadicIntervalTrivariate precision :=
  [[[DyadicInterval.ofRat precision 0, DyadicInterval.ofRat precision 1]]]

/-- Natural powers of a trivariate dyadic interval polynomial. -/
def pow (p : DyadicIntervalTrivariate precision) : ℕ → DyadicIntervalTrivariate precision
  | 0 => constant (DyadicInterval.ofRat precision 1)
  | n + 1 => mul (pow p n) p

/-- Read one coefficient, returning dyadic zero beyond the support. -/
def coefficient (p : DyadicIntervalTrivariate precision) (i j k : ℕ) :
    DyadicInterval precision :=
  ((p.getD i []).getD j []).getD k (DyadicInterval.ofRat precision 0)

/-- Corresponding outer slices widen each other, including zero padding. -/
theorem getD_widens {P : DyadicIntervalTrivariate precision} {p : IntervalTrivariate}
    (hP : Widens P p) (i : ℕ) : (P.getD i []).Widens (p.getD i []) := by
  induction P generalizing p i with
  | nil =>
      cases p with
      | nil => trivial
      | cons a p => contradiction
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          cases i with
          | zero => exact hP.1
          | succ i => exact ih hP.2 i

/-- Corresponding padded trivariate coefficients widen each other. -/
theorem coefficient_widens {P : DyadicIntervalTrivariate precision}
    {p : IntervalTrivariate} (hP : Widens P p) (i j k : ℕ) :
    (coefficient P i j k).Widens (p.coefficient i j k) :=
  DyadicIntervalUnivariate.getD_widens
    (DyadicIntervalBivariate.getD_widens
      (getD_widens hP i) j) k

/-- Dyadic trivariate addition preserves coefficientwise widening. -/
theorem add_widens {P Q : DyadicIntervalTrivariate precision}
    {p q : IntervalTrivariate} (hP : Widens P p) (hQ : Widens Q q) :
    Widens (add P Q) (IntervalTrivariate.add p q) := by
  induction P generalizing Q p q with
  | nil => cases p <;> cases Q <;> cases q <;> simp_all [Widens, add,
      IntervalTrivariate.add]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          cases Q with
          | nil => cases q <;> simp_all [Widens, add, IntervalTrivariate.add]
          | cons B Q =>
              cases q with
              | nil => contradiction
              | cons b q =>
                  exact ⟨DyadicIntervalBivariate.add_widens hP.1 hQ.1,
                    ih hP.2 hQ.2⟩

/-- Dyadic trivariate negation preserves coefficientwise widening. -/
theorem neg_widens {P : DyadicIntervalTrivariate precision} {p : IntervalTrivariate}
    (hP : Widens P p) : Widens (neg P) (IntervalTrivariate.neg p) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, neg, IntervalTrivariate.neg]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p => exact ⟨DyadicIntervalBivariate.neg_widens hP.1, ih hP.2⟩

/-- Dyadic slice scaling preserves coefficientwise widening. -/
theorem scaleSlice_widens
    {A : DyadicIntervalBivariate precision} {P : DyadicIntervalTrivariate precision}
    {a : IntervalBivariate} {p : IntervalTrivariate}
    (hA : A.Widens a) (hP : Widens P p) :
    Widens (scaleSlice A P) (IntervalTrivariate.scaleSlice a p) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, scaleSlice, IntervalTrivariate.scaleSlice]
  | cons B P ih =>
      cases p with
      | nil => contradiction
      | cons b p => exact ⟨DyadicIntervalBivariate.mul_widens hA hP.1, ih hP.2⟩

/-- Dyadic trivariate multiplication preserves coefficientwise widening. -/
theorem mul_widens {P Q : DyadicIntervalTrivariate precision}
    {p q : IntervalTrivariate} (hP : Widens P p) (hQ : Widens Q q) :
    Widens (mul P Q) (IntervalTrivariate.mul p q) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, mul, IntervalTrivariate.mul]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          apply add_widens (scaleSlice_widens hP.1 hQ)
          exact ⟨trivial, ih hP.2⟩

/-- Dyadic trivariate constants widen exact interval constants. -/
theorem constant_widens {A : DyadicInterval precision} {a : RationalInterval}
    (hA : A.Widens a) : Widens (constant A) (IntervalTrivariate.constant a) :=
  ⟨⟨⟨hA, trivial⟩, trivial⟩, trivial⟩

/-- The first dyadic trivariate coordinate widens its exact counterpart. -/
theorem first_widens (precision : ℕ) : Widens (first precision) IntervalTrivariate.first :=
  ⟨trivial, ⟨⟨⟨DyadicInterval.ofInterval_widens precision (.singleton 1), trivial⟩,
    trivial⟩, trivial⟩⟩

/-- The second dyadic trivariate coordinate widens its exact counterpart. -/
theorem second_widens (precision : ℕ) :
    Widens (second precision) IntervalTrivariate.second :=
  ⟨⟨trivial, ⟨DyadicInterval.ofInterval_widens precision (.singleton 1), trivial⟩,
    trivial⟩, trivial⟩

/-- The third dyadic trivariate coordinate widens its exact counterpart. -/
theorem third_widens (precision : ℕ) : Widens (third precision) IntervalTrivariate.third :=
  ⟨⟨⟨DyadicInterval.ofInterval_widens precision (.singleton 0),
    DyadicInterval.ofInterval_widens precision (.singleton 1), trivial⟩, trivial⟩, trivial⟩

/-- Dyadic trivariate natural powers preserve coefficientwise widening. -/
theorem pow_widens {P : DyadicIntervalTrivariate precision} {p : IntervalTrivariate}
    (hP : Widens P p) (n : ℕ) : Widens (pow P n) (IntervalTrivariate.pow p n) := by
  induction n with
  | zero => exact constant_widens (DyadicInterval.ofInterval_widens precision (.singleton 1))
  | succ n ih => exact mul_widens ih hP

end DyadicIntervalTrivariate

end Bescovitch
