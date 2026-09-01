/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.DyadicIntervalBernstein
public import Bescovitch.SixPoint.WeightedSelfCertificateData.Boxes
public import Bescovitch.SixPoint.WeightedSelfExceptionalBernstein

/-!
# Interval coefficients for the exceptional weighted-self face

The physical interval polynomials are affinely substituted into the unit-square face chart.
Every scalar operation is outward-rounded at 96 dyadic bits before the two power-to-Bernstein
passes.  The resulting compact exact checks certify the `bb` margin and Hessian determinant.
-/

@[expose] public section

noncomputable section

open scoped BigOperators unitInterval

namespace Bescovitch

set_option Elab.async false

private abbrev FaceIntervalPolynomial := IntervalBivariate
private abbrev facePrecision : ℕ := 96
private abbrev FaceDyadicPolynomial := DyadicIntervalBivariate facePrecision

private def IntervalUnivariate.substituteFace
    (p : IntervalUnivariate) (z : FaceIntervalPolynomial) : FaceIntervalPolynomial :=
  match p with
  | [] => []
  | a :: q => IntervalBivariate.add (IntervalBivariate.constant a)
      (IntervalBivariate.mul z (IntervalUnivariate.substituteFace q z))

private def IntervalBivariate.substituteFace
    (p : IntervalBivariate) (y z : FaceIntervalPolynomial) : FaceIntervalPolynomial :=
  match p with
  | [] => []
  | a :: q => IntervalBivariate.add (a.substituteFace z)
      (IntervalBivariate.mul y (IntervalBivariate.substituteFace q y z))

private def IntervalTrivariate.substituteFace
    (p : IntervalTrivariate) (x y z : FaceIntervalPolynomial) : FaceIntervalPolynomial :=
  match p with
  | [] => []
  | a :: q => IntervalBivariate.add (a.substituteFace y z)
      (IntervalBivariate.mul x (IntervalTrivariate.substituteFace q x y z))

private def RadicalUnivariate.substituteFace {n : ℕ}
    (p : RadicalUnivariate n) (z : RadicalBivariate n) : RadicalBivariate n :=
  match p with
  | [] => []
  | a :: q => RadicalBivariate.add (RadicalBivariate.constant a)
      (RadicalBivariate.mul z (RadicalUnivariate.substituteFace q z))

private def RadicalBivariate.substituteFace {n : ℕ}
    (p : RadicalBivariate n) (y z : RadicalBivariate n) : RadicalBivariate n :=
  match p with
  | [] => []
  | a :: q => RadicalBivariate.add (a.substituteFace z)
      (RadicalBivariate.mul y (RadicalBivariate.substituteFace q y z))

private def RadicalTrivariate.substituteFace {n : ℕ}
    (p : RadicalTrivariate n) (x y z : RadicalBivariate n) : RadicalBivariate n :=
  match p with
  | [] => []
  | a :: q => RadicalBivariate.add (a.substituteFace y z)
      (RadicalBivariate.mul x (RadicalTrivariate.substituteFace q x y z))

private theorem IntervalUnivariate.substituteFace_contains {n : ℕ}
    {P : IntervalUnivariate} {p : RadicalUnivariate n} {input : Fin n → ℝ}
    (hp : P.Contains input p) {Z : FaceIntervalPolynomial} {z : RadicalBivariate n}
    (hz : Z.Contains input z) :
    (P.substituteFace Z).Contains input (p.substituteFace z) := by
  induction hp with
  | nil => simp [IntervalUnivariate.substituteFace,
      RadicalUnivariate.substituteFace, IntervalBivariate.Contains]
  | cons hhead htail ih =>
      exact IntervalBivariate.contains_add
        (IntervalBivariate.contains_constant hhead)
        (IntervalBivariate.contains_mul hz ih)

private theorem IntervalBivariate.substituteFace_contains {n : ℕ}
    {P : IntervalBivariate} {p : RadicalBivariate n} {input : Fin n → ℝ}
    (hp : P.Contains input p)
    {Y Z : FaceIntervalPolynomial} {y z : RadicalBivariate n}
    (hy : Y.Contains input y) (hz : Z.Contains input z) :
    (P.substituteFace Y Z).Contains input (p.substituteFace y z) := by
  induction hp with
  | nil => simp [IntervalBivariate.substituteFace, RadicalBivariate.substituteFace,
      IntervalBivariate.Contains]
  | cons hhead htail ih =>
      exact IntervalBivariate.contains_add
        (IntervalUnivariate.substituteFace_contains hhead hz)
        (IntervalBivariate.contains_mul hy ih)

private theorem IntervalTrivariate.substituteFace_contains {n : ℕ}
    {P : IntervalTrivariate} {p : RadicalTrivariate n} {input : Fin n → ℝ}
    (hp : P.Contains input p)
    {X Y Z : FaceIntervalPolynomial} {x y z : RadicalBivariate n}
    (hx : X.Contains input x) (hy : Y.Contains input y) (hz : Z.Contains input z) :
    (P.substituteFace X Y Z).Contains input (p.substituteFace x y z) := by
  induction hp with
  | nil => simp [IntervalTrivariate.substituteFace, RadicalTrivariate.substituteFace,
      IntervalBivariate.Contains]
  | cons hhead htail ih =>
      exact IntervalBivariate.contains_add
        (IntervalBivariate.substituteFace_contains hhead hy hz)
        (IntervalBivariate.contains_mul hx ih)

private theorem RadicalUnivariate.eval_substituteFace {n : ℕ}
    (p : RadicalUnivariate n) (z : RadicalBivariate n)
    (input : Fin n → ℝ) (u v : ℝ) :
    (p.substituteFace z).eval input u v =
      p.eval input (z.eval input u v) := by
  induction p with
  | nil => simp [substituteFace, RadicalBivariate.eval, RadicalUnivariate.eval]
  | cons a p ih =>
      simp [substituteFace, RadicalBivariate.eval_add,
        RadicalBivariate.eval_mul, RadicalBivariate.eval_constant,
        RadicalUnivariate.eval, ih]

private theorem RadicalBivariate.eval_substituteFace {n : ℕ}
    (p : RadicalBivariate n) (y z : RadicalBivariate n)
    (input : Fin n → ℝ) (u v : ℝ) :
    (p.substituteFace y z).eval input u v =
      p.eval input (y.eval input u v) (z.eval input u v) := by
  induction p with
  | nil => simp [substituteFace, RadicalBivariate.eval]
  | cons a p ih =>
      simp [substituteFace, RadicalBivariate.eval_add,
        RadicalBivariate.eval_mul, RadicalBivariate.eval,
        RadicalUnivariate.eval_substituteFace, ih]

private theorem RadicalTrivariate.eval_substituteFace {n : ℕ}
    (p : RadicalTrivariate n) (x y z : RadicalBivariate n)
    (input : Fin n → ℝ) (u v : ℝ) :
    (p.substituteFace x y z).eval input u v =
      p.eval input (x.eval input u v) (y.eval input u v) (z.eval input u v) := by
  induction p with
  | nil => simp [substituteFace, RadicalTrivariate.eval, RadicalBivariate.eval]
  | cons a p ih =>
      simp [substituteFace, RadicalBivariate.eval_add,
        RadicalBivariate.eval_mul, RadicalTrivariate.eval,
        RadicalBivariate.eval_substituteFace, ih]

/-- Outward-round every coefficient of an interval univariate polynomial. -/
def roundUnivariate (precision : ℕ) (p : IntervalUnivariate) :
    DyadicIntervalUnivariate precision :=
  p.map (DyadicInterval.ofInterval precision)

/-- Outward-round every coefficient of an interval bivariate polynomial. -/
def roundBivariate (precision : ℕ) (p : IntervalBivariate) :
    DyadicIntervalBivariate precision :=
  p.map (roundUnivariate precision)

/-- Outward-round every coefficient of an interval trivariate polynomial. -/
def roundTrivariate (precision : ℕ) (p : IntervalTrivariate) :
    DyadicIntervalTrivariate precision :=
  p.map (roundBivariate precision)

private theorem roundUnivariate_widens (precision : ℕ) (p : IntervalUnivariate) :
    (roundUnivariate precision p).Widens p := by
  induction p with
  | nil => trivial
  | cons a p ih => exact ⟨DyadicInterval.ofInterval_widens precision a, ih⟩

private theorem roundBivariate_widens (precision : ℕ) (p : IntervalBivariate) :
    (roundBivariate precision p).Widens p := by
  induction p with
  | nil => trivial
  | cons a p ih => exact ⟨roundUnivariate_widens precision a, ih⟩

private theorem roundTrivariate_widens (precision : ℕ) (p : IntervalTrivariate) :
    (roundTrivariate precision p).Widens p := by
  induction p with
  | nil => trivial
  | cons a p ih => exact ⟨roundBivariate_widens precision a, ih⟩

/-- Substitute a bivariate face polynomial into a dyadic univariate polynomial. -/
def DyadicIntervalUnivariate.substituteFace {precision : ℕ}
    (p : DyadicIntervalUnivariate precision)
    (z : DyadicIntervalBivariate precision) : DyadicIntervalBivariate precision :=
  match p with
  | [] => []
  | a :: q => DyadicIntervalBivariate.add (DyadicIntervalBivariate.constant a)
      (DyadicIntervalBivariate.mul z (DyadicIntervalUnivariate.substituteFace q z))

/-- Substitute two bivariate face polynomials into a dyadic bivariate polynomial. -/
def DyadicIntervalBivariate.substituteFace {precision : ℕ}
    (p y z : DyadicIntervalBivariate precision) : DyadicIntervalBivariate precision :=
  match p with
  | [] => []
  | a :: q => DyadicIntervalBivariate.add (a.substituteFace z)
      (DyadicIntervalBivariate.mul y (DyadicIntervalBivariate.substituteFace q y z))

/-- Substitute the three face charts into a dyadic trivariate polynomial. -/
def DyadicIntervalTrivariate.substituteFace {precision : ℕ}
    (p : DyadicIntervalTrivariate precision)
    (x y z : DyadicIntervalBivariate precision) : DyadicIntervalBivariate precision :=
  match p with
  | [] => []
  | a :: q => DyadicIntervalBivariate.add (a.substituteFace y z)
      (DyadicIntervalBivariate.mul x (DyadicIntervalTrivariate.substituteFace q x y z))

private theorem DyadicIntervalUnivariate.substituteFace_widens {precision : ℕ}
    {P : DyadicIntervalUnivariate precision} {p : IntervalUnivariate}
    (hp : P.Widens p)
    {Z : DyadicIntervalBivariate precision} {z : IntervalBivariate}
    (hz : Z.Widens z) :
    (P.substituteFace Z).Widens (p.substituteFace z) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, DyadicIntervalUnivariate.substituteFace,
      IntervalUnivariate.substituteFace, DyadicIntervalBivariate.Widens]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          exact DyadicIntervalBivariate.add_widens
            (DyadicIntervalBivariate.constant_widens hp.1)
            (DyadicIntervalBivariate.mul_widens hz (ih hp.2))

private theorem DyadicIntervalBivariate.substituteFace_widens {precision : ℕ}
    {P : DyadicIntervalBivariate precision} {p : IntervalBivariate}
    (hp : P.Widens p)
    {Y Z : DyadicIntervalBivariate precision} {y z : IntervalBivariate}
    (hy : Y.Widens y) (hz : Z.Widens z) :
    (P.substituteFace Y Z).Widens (p.substituteFace y z) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, DyadicIntervalBivariate.substituteFace,
      IntervalBivariate.substituteFace]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          exact DyadicIntervalBivariate.add_widens
            (DyadicIntervalUnivariate.substituteFace_widens hp.1 hz)
            (DyadicIntervalBivariate.mul_widens hy (ih hp.2))

private theorem DyadicIntervalTrivariate.substituteFace_widens {precision : ℕ}
    {P : DyadicIntervalTrivariate precision} {p : IntervalTrivariate}
    (hp : P.Widens p)
    {X Y Z : DyadicIntervalBivariate precision} {x y z : IntervalBivariate}
    (hx : X.Widens x) (hy : Y.Widens y) (hz : Z.Widens z) :
    (P.substituteFace X Y Z).Widens (p.substituteFace x y z) := by
  induction P generalizing p with
  | nil => cases p <;> simp_all [Widens, DyadicIntervalTrivariate.substituteFace,
      IntervalTrivariate.substituteFace, DyadicIntervalBivariate.Widens]
  | cons A P ih =>
      cases p with
      | nil => contradiction
      | cons a p =>
          exact DyadicIntervalBivariate.add_widens
            (DyadicIntervalBivariate.substituteFace_widens hp.1 hy hz)
            (DyadicIntervalBivariate.mul_widens hx (ih hp.2))

/-- The constant radial coordinate on the exceptional face. -/
def intervalFaceOne : IntervalBivariate :=
  IntervalBivariate.constant (.singleton 1)

/-- The interval polynomial for `b = 29 / 40 + u / 40`. -/
def intervalFaceSecondRadius : IntervalBivariate :=
  IntervalBivariate.add (IntervalBivariate.constant (.singleton (29 / 40)))
    (IntervalBivariate.mul (IntervalBivariate.constant (.singleton (1 / 40)))
      IntervalBivariate.first)

/-- The interval polynomial for `t = -209 / 256 + v / 256`. -/
def intervalFaceProjection : IntervalBivariate :=
  IntervalBivariate.add (IntervalBivariate.constant (.singleton (-209 / 256)))
    (IntervalBivariate.mul (IntervalBivariate.constant (.singleton (1 / 256)))
      IntervalBivariate.second)

private def exactFaceOne : RadicalBivariate 18 :=
  RadicalBivariate.constant (.constant 1)

private def exactFaceSecondRadius : RadicalBivariate 18 :=
  RadicalBivariate.add (RadicalBivariate.constant (.constant (29 / 40)))
    (RadicalBivariate.mul (RadicalBivariate.constant (.constant (1 / 40)))
      RadicalBivariate.first)

private def exactFaceProjection : RadicalBivariate 18 :=
  RadicalBivariate.add (RadicalBivariate.constant (.constant (-209 / 256)))
    (RadicalBivariate.mul (RadicalBivariate.constant (.constant (1 / 256)))
      RadicalBivariate.second)

private theorem intervalFaceOne_contains (input : Fin 18 → ℝ) :
    intervalFaceOne.Contains input exactFaceOne :=
  IntervalBivariate.contains_constant (RationalInterval.singleton_contains 1)

private theorem intervalFaceSecondRadius_contains (input : Fin 18 → ℝ) :
    intervalFaceSecondRadius.Contains input exactFaceSecondRadius := by
  exact IntervalBivariate.contains_add
    (IntervalBivariate.contains_constant (RationalInterval.singleton_contains (29 / 40)))
    (IntervalBivariate.contains_mul
      (IntervalBivariate.contains_constant (RationalInterval.singleton_contains (1 / 40)))
      (IntervalBivariate.contains_first input))

private theorem intervalFaceProjection_contains (input : Fin 18 → ℝ) :
    intervalFaceProjection.Contains input exactFaceProjection := by
  exact IntervalBivariate.contains_add
    (IntervalBivariate.contains_constant
      (RationalInterval.singleton_contains (-209 / 256)))
    (IntervalBivariate.contains_mul
      (IntervalBivariate.contains_constant (RationalInterval.singleton_contains (1 / 256)))
      (IntervalBivariate.contains_second input))

private def intervalAffineFace (p : IntervalTrivariate) (scale : ℚ) :
    FaceIntervalPolynomial :=
  IntervalBivariate.mul (IntervalBivariate.constant (.singleton scale))
    (p.substituteFace intervalFaceOne intervalFaceSecondRadius intervalFaceProjection)

private def exactAffineFace (p : RadicalTrivariate 18) (scale : ℚ) :
    RadicalBivariate 18 :=
  RadicalBivariate.mul (RadicalBivariate.constant (.constant scale))
    (p.substituteFace exactFaceOne exactFaceSecondRadius exactFaceProjection)

/-- Substitute and scale a physical polynomial on the exceptional face. -/
def dyadicAffineFace (p : IntervalTrivariate) (scale : ℚ) :
    DyadicIntervalBivariate 96 :=
  let x := roundBivariate 96 intervalFaceOne
  let y := roundBivariate 96 intervalFaceSecondRadius
  let z := roundBivariate 96 intervalFaceProjection
  DyadicIntervalBivariate.mul
    (DyadicIntervalBivariate.constant (DyadicInterval.ofRat 96 scale))
    ((roundTrivariate 96 p).substituteFace x y z)

private theorem dyadicAffineFace_widens (p : IntervalTrivariate) (scale : ℚ) :
    (dyadicAffineFace p scale).Widens (intervalAffineFace p scale) := by
  apply DyadicIntervalBivariate.mul_widens
  · exact DyadicIntervalBivariate.constant_widens
      (DyadicInterval.ofInterval_widens facePrecision (.singleton scale))
  · exact DyadicIntervalTrivariate.substituteFace_widens
      (roundTrivariate_widens facePrecision p)
      (roundBivariate_widens facePrecision intervalFaceOne)
      (roundBivariate_widens facePrecision intervalFaceSecondRadius)
      (roundBivariate_widens facePrecision intervalFaceProjection)

private theorem intervalAffineFace_contains
    {P : IntervalTrivariate} {p : RadicalTrivariate 18}
    {input : Fin 18 → ℝ} (hp : P.Contains input p) (scale : ℚ) :
    (intervalAffineFace P scale).Contains input (exactAffineFace p scale) := by
  apply IntervalBivariate.contains_mul
  · exact IntervalBivariate.contains_constant
      (RationalInterval.singleton_contains scale)
  · exact IntervalTrivariate.substituteFace_contains hp
      (intervalFaceOne_contains input)
      (intervalFaceSecondRadius_contains input)
      (intervalFaceProjection_contains input)

private def intervalFaceCoefficient (p : FaceIntervalPolynomial) (i j : ℕ) :
    RationalInterval :=
  (p.getD i []).getD j (.singleton 0)

/-- A power coefficient of an outward-rounded exceptional-face polynomial. -/
def dyadicFaceCoefficient (p : DyadicIntervalBivariate 96) (i j : ℕ) :
    DyadicInterval 96 :=
  (p.getD i []).getD j (DyadicInterval.ofRat 96 0)

private def exactFaceCoefficient (p : RadicalBivariate 18) (input : Fin 18 → ℝ)
    (i j : ℕ) : ℝ :=
  ((p.getD i []).getD j (.constant 0)).eval input

private theorem IntervalUnivariate.getD_contains {n : ℕ}
    {P : IntervalUnivariate} {p : RadicalUnivariate n} {input : Fin n → ℝ}
    (hp : P.Contains input p) (i : ℕ) :
    (P.getD i (.singleton 0)).Contains
      ((p.getD i (.constant 0)).eval input) := by
  induction hp generalizing i with
  | nil => simpa [RadicalExpression.eval] using RationalInterval.singleton_contains 0
  | cons hhead htail ih =>
      cases i with
      | zero => exact hhead
      | succ i => exact ih i

private theorem IntervalBivariate.coefficient_contains {n : ℕ}
    {P : IntervalBivariate} {p : RadicalBivariate n} {input : Fin n → ℝ}
    (hp : P.Contains input p) (i j : ℕ) :
    (intervalFaceCoefficient P i j).Contains
      (((p.getD i []).getD j (.constant 0)).eval input) := by
  induction hp generalizing i with
  | nil => simpa [intervalFaceCoefficient, RadicalExpression.eval] using
      RationalInterval.singleton_contains 0
  | cons hhead htail ih =>
      cases i with
      | zero => exact IntervalUnivariate.getD_contains hhead j
      | succ i => exact ih i

private theorem dyadicFaceCoefficient_widens
    {P : FaceDyadicPolynomial} {p : FaceIntervalPolynomial}
    (hp : P.Widens p) (i j : ℕ) :
    (dyadicFaceCoefficient P i j).Widens (intervalFaceCoefficient p i j) :=
  DyadicIntervalUnivariate.getD_widens
    (DyadicIntervalBivariate.getD_widens hp i) j

private theorem DyadicInterval.interpret_contains_of_widens
    {D : DyadicInterval facePrecision} {interval : RationalInterval} {x : ℝ}
    (hD : D.Widens interval) (hx : interval.Contains x) :
    D.interpret.Contains x := by
  constructor
  · have hLower : (D.interpret.lower : ℝ) ≤ interval.lower := by
      exact_mod_cast hD.1.1
    exact hLower.trans hx.1
  · have hUpper : (interval.upper : ℝ) ≤ D.interpret.upper := by
      exact_mod_cast hD.2.2
    exact hx.2.trans hUpper

/-- A padded Bernstein coefficient of an outward-rounded exceptional-face polynomial. -/
def dyadicFaceBernsteinCoefficient
    (p : DyadicIntervalBivariate 96) (i : Fin 17) (j : Fin 9) :
    DyadicInterval 96 :=
  dyadicIntervalPowerToBernstein 96 8
    (fun j' ↦ dyadicIntervalPowerToBernstein 96 16
      (fun i' ↦ dyadicFaceCoefficient p i' j') i) j

private def exactFaceBernsteinCoefficient
    (p : RadicalBivariate 18) (input : Fin 18 → ℝ)
    (i : Fin 17) (j : Fin 9) : ℝ :=
  powerToBernstein 8
    (fun j' ↦ powerToBernstein 16
      (fun i' ↦ exactFaceCoefficient p input i' j') i) j

private theorem dyadicFaceBernsteinCoefficient_contains
    {P : FaceDyadicPolynomial} {Q : FaceIntervalPolynomial}
    {q : RadicalBivariate 18} {input : Fin 18 → ℝ}
    (hPQ : P.Widens Q) (hQq : Q.Contains input q) (i : Fin 17) (j : Fin 9) :
    (dyadicFaceBernsteinCoefficient P i j).interpret.Contains
      (exactFaceBernsteinCoefficient q input i j) := by
  let exactPower : Fin 17 → Fin 9 → RationalInterval :=
    fun i j ↦ intervalFaceCoefficient Q i j
  have hpower : ∀ (i : Fin 17) (j : Fin 9),
      (dyadicFaceCoefficient P i j).Widens (exactPower i j) :=
    fun i j ↦ dyadicFaceCoefficient_widens hPQ i j
  have hfirst (j' : Fin 9) :
      (dyadicIntervalPowerToBernstein facePrecision 16
        (fun i' ↦ dyadicFaceCoefficient P i' j') i).Widens
      (intervalPowerToBernstein 16 (fun i' ↦ exactPower i' j') i) :=
    dyadicIntervalPowerToBernstein_widens facePrecision 16
      (fun i' ↦ hpower i' j') i
  have hwidens : (dyadicFaceBernsteinCoefficient P i j).Widens
      (intervalPowerToBernstein 8
        (fun j' ↦ intervalPowerToBernstein 16
          (fun i' ↦ exactPower i' j') i) j) :=
    dyadicIntervalPowerToBernstein_widens facePrecision 8 hfirst j
  apply DyadicInterval.interpret_contains_of_widens hwidens
  apply intervalPowerToBernstein_contains
  intro j'
  apply intervalPowerToBernstein_contains
  intro i'
  exact IntervalBivariate.coefficient_contains hQq i' j'

private theorem exactAffineFace_eval (p : RadicalTrivariate 18) (scale : ℚ)
    (input : Fin 18 → ℝ) (u v : ℝ) :
    (exactAffineFace p scale).eval input u v =
      scale * p.eval input 1 (29 / 40 + u / 40) (-209 / 256 + v / 256) := by
  simp only [exactAffineFace, RadicalBivariate.eval_mul,
    RadicalBivariate.eval_constant, RadicalTrivariate.eval_substituteFace,
    exactFaceOne, exactFaceSecondRadius, exactFaceProjection,
    RadicalBivariate.eval_add, RadicalBivariate.eval_first,
    RadicalBivariate.eval_second, RadicalExpression.eval]
  congr 2 <;> ring

private def UnivariateFits {n : ℕ} (d : ℕ) (p : RadicalUnivariate n) : Prop :=
  p.length ≤ d + 1

private def BivariateFits {n : ℕ} (d e : ℕ) (p : RadicalBivariate n) : Prop :=
  p.length ≤ d + 1 ∧ ∀ row ∈ p, UnivariateFits e row

private theorem univariate_add_length {n : ℕ}
    (p q : RadicalUnivariate n) :
    (RadicalUnivariate.add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [RadicalUnivariate.add]
  | cons a p ih =>
      cases q with
      | nil => simp [RadicalUnivariate.add]
      | cons b q => simp [RadicalUnivariate.add, ih, Nat.succ_max_succ]

private theorem bivariate_add_length {n : ℕ}
    (p q : RadicalBivariate n) :
    (RadicalBivariate.add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [RadicalBivariate.add]
  | cons a p ih =>
      cases q with
      | nil => simp [RadicalBivariate.add]
      | cons b q => simp [RadicalBivariate.add, ih, Nat.succ_max_succ]

private theorem trivariate_add_length {n : ℕ}
    (p q : RadicalTrivariate n) :
    (RadicalTrivariate.add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [RadicalTrivariate.add]
  | cons a p ih =>
      cases q with
      | nil => simp [RadicalTrivariate.add]
      | cons b q => simp [RadicalTrivariate.add, ih, Nat.succ_max_succ]

private theorem univariate_add_fits {n d : ℕ} {p q : RadicalUnivariate n}
    (hp : UnivariateFits d p) (hq : UnivariateFits d q) :
    UnivariateFits d (RadicalUnivariate.add p q) := by
  rw [UnivariateFits, univariate_add_length]
  exact max_le hp hq

private theorem univariate_neg_fits {n d : ℕ} {p : RadicalUnivariate n}
    (hp : UnivariateFits d p) :
    UnivariateFits d (RadicalUnivariate.neg p) := by
  simpa [UnivariateFits, RadicalUnivariate.neg] using hp

private theorem univariate_mul_fits {n a b : ℕ} {p q : RadicalUnivariate n}
    (hp : UnivariateFits a p) (hq : UnivariateFits b q) :
    UnivariateFits (a + b) (RadicalUnivariate.mul p q) := by
  induction a generalizing p with
  | zero =>
      cases p with
      | nil => simp [UnivariateFits, RadicalUnivariate.mul]
      | cons x p =>
          have hpEmpty : p = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [UnivariateFits, List.length_cons] at hp
            omega
          subst p
          cases q with
          | nil => simp [UnivariateFits, RadicalUnivariate.mul,
              RadicalUnivariate.add, RadicalUnivariate.scale]
          | cons y q =>
              simp only [UnivariateFits, List.length_cons] at hq ⊢
              simp only [RadicalUnivariate.mul]
              rw [univariate_add_length]
              simp only [RadicalUnivariate.scale, List.length_map]
              apply max_le
              · simpa only [List.length_cons, zero_add] using hq
              · simp
  | succ a ih =>
      cases p with
      | nil => simp [UnivariateFits, RadicalUnivariate.mul]
      | cons x p =>
          have hpTail : UnivariateFits a p := by
            simp only [UnivariateFits, List.length_cons] at hp ⊢
            omega
          have hrec := ih hpTail
          rw [UnivariateFits, RadicalUnivariate.mul, univariate_add_length]
          simp only [RadicalUnivariate.scale, List.length_map, List.length_cons]
          rw [max_le_iff]
          constructor
          · dsimp only [UnivariateFits] at hq
            omega
          · dsimp only [UnivariateFits] at hrec
            omega

private theorem bivariate_mono {n d e d' e' : ℕ} {p : RadicalBivariate n}
    (hp : BivariateFits d e p) (hd : d ≤ d') (he : e ≤ e') :
    BivariateFits d' e' p := by
  refine ⟨hp.1.trans ?_, ?_⟩
  · omega
  · intro row hrow
    exact (hp.2 row hrow).trans (by omega)

private theorem bivariate_add_fits {n d e : ℕ} {p q : RadicalBivariate n}
    (hp : BivariateFits d e p) (hq : BivariateFits d e q) :
    BivariateFits d e (RadicalBivariate.add p q) := by
  constructor
  · rw [bivariate_add_length]
    exact max_le hp.1 hq.1
  · induction p generalizing q with
    | nil => simpa [RadicalBivariate.add] using hq.2
    | cons a p ih =>
        cases q with
        | nil => simpa [RadicalBivariate.add] using hp.2
        | cons b q =>
            intro row hrow
            simp only [RadicalBivariate.add, List.mem_cons] at hrow
            rcases hrow with rfl | hrow
            · apply univariate_add_fits
              · exact hp.2 a (by simp)
              · exact hq.2 b (by simp)
            · apply ih (q := q)
              · constructor
                · simp only [BivariateFits, List.length_cons] at hp
                  omega
                · intro row hrow'
                  exact hp.2 row (by simp [hrow'])
              · constructor
                · simp only [BivariateFits, List.length_cons] at hq
                  omega
                · intro row hrow'
                  exact hq.2 row (by simp [hrow'])
              · exact hrow

private theorem bivariate_neg_fits {n d e : ℕ} {p : RadicalBivariate n}
    (hp : BivariateFits d e p) :
    BivariateFits d e (RadicalBivariate.neg p) := by
  constructor
  · simpa [RadicalBivariate.neg] using hp.1
  · intro row hrow
    simp only [RadicalBivariate.neg, List.mem_map] at hrow
    obtain ⟨source, hsource, rfl⟩ := hrow
    exact univariate_neg_fits (hp.2 source hsource)

private theorem bivariate_scaleRow_fits {n db ea eb : ℕ}
    {a : RadicalUnivariate n} {p : RadicalBivariate n}
    (ha : UnivariateFits ea a) (hp : BivariateFits db eb p) :
    BivariateFits db (ea + eb) (RadicalBivariate.scaleRow a p) := by
  constructor
  · simpa [RadicalBivariate.scaleRow] using hp.1
  · intro row hrow
    simp only [RadicalBivariate.scaleRow, List.mem_map] at hrow
    obtain ⟨source, hsource, rfl⟩ := hrow
    exact univariate_mul_fits ha (hp.2 source hsource)

private theorem bivariate_zero_cons_fits {n d e : ℕ} {p : RadicalBivariate n}
    (hp : BivariateFits d e p) :
    BivariateFits (d + 1) e ([] :: p) := by
  constructor
  · dsimp only [BivariateFits] at hp ⊢
    simp only [List.length_cons]
    omega
  · intro row hrow
    simp only [List.mem_cons] at hrow
    rcases hrow with rfl | hrow
    · simp [UnivariateFits]
    · exact hp.2 row hrow

private theorem bivariate_mul_fits {n da db ea eb : ℕ}
    {p q : RadicalBivariate n}
    (hp : BivariateFits da ea p) (hq : BivariateFits db eb q) :
    BivariateFits (da + db) (ea + eb) (RadicalBivariate.mul p q) := by
  induction da generalizing p with
  | zero =>
      cases p with
      | nil => simp [BivariateFits, RadicalBivariate.mul]
      | cons a p =>
          have hpEmpty : p = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [BivariateFits, List.length_cons] at hp
            omega
          subst p
          apply bivariate_add_fits
          · simpa using bivariate_scaleRow_fits (hp.2 a (by simp)) hq
          · simp [BivariateFits, RadicalBivariate.mul, UnivariateFits]
  | succ da ih =>
      cases p with
      | nil => simp [BivariateFits, RadicalBivariate.mul]
      | cons a p =>
          have hpTail : BivariateFits da ea p := by
            constructor
            · simp only [BivariateFits, List.length_cons] at hp
              omega
            · intro row hrow
              exact hp.2 row (by simp [hrow])
          rw [RadicalBivariate.mul]
          apply bivariate_add_fits
          · exact bivariate_mono
              (bivariate_scaleRow_fits (hp.2 a (by simp)) hq) (by omega) le_rfl
          · simpa [Nat.succ_add] using bivariate_zero_cons_fits (ih hpTail)

private theorem trivariate_mono {n a b c a' b' c' : ℕ} {p : RadicalTrivariate n}
    (hp : p.Fits a b c) (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    p.Fits a' b' c' := by
  refine ⟨hp.1.trans ?_, ?_⟩
  · omega
  · intro slice hslice
    refine ⟨(hp.2 slice hslice).1.trans ?_, ?_⟩
    · omega
    · intro row hrow
      exact (hp.2 slice hslice).2 row hrow |>.trans (by omega)

private theorem trivariate_add_fits {n a b c : ℕ} {p q : RadicalTrivariate n}
    (hp : p.Fits a b c) (hq : q.Fits a b c) :
    (RadicalTrivariate.add p q).Fits a b c := by
  constructor
  · rw [trivariate_add_length]
    exact max_le hp.1 hq.1
  · induction p generalizing q with
    | nil => simpa [RadicalTrivariate.add] using hq.2
    | cons x p ih =>
        cases q with
        | nil => simpa [RadicalTrivariate.add] using hp.2
        | cons y q =>
            intro slice hslice
            simp only [RadicalTrivariate.add, List.mem_cons] at hslice
            rcases hslice with rfl | hslice
            · exact bivariate_add_fits (hp.2 x (by simp)) (hq.2 y (by simp))
            · apply ih (q := q)
              · constructor
                · simp only [RadicalTrivariate.Fits, List.length_cons] at hp
                  omega
                · intro slice hslice'
                  exact hp.2 slice (by simp [hslice'])
              · constructor
                · simp only [RadicalTrivariate.Fits, List.length_cons] at hq
                  omega
                · intro slice hslice'
                  exact hq.2 slice (by simp [hslice'])
              · exact hslice

private theorem trivariate_neg_fits {n a b c : ℕ} {p : RadicalTrivariate n}
    (hp : p.Fits a b c) : (RadicalTrivariate.neg p).Fits a b c := by
  constructor
  · simpa [RadicalTrivariate.neg] using hp.1
  · intro slice hslice
    simp only [RadicalTrivariate.neg, List.mem_map] at hslice
    obtain ⟨source, hsource, rfl⟩ := hslice
    exact bivariate_neg_fits (hp.2 source hsource)

private theorem trivariate_scaleSlice_fits {n ay az bxDegree byDegree bz : ℕ}
    {a : RadicalBivariate n} {p : RadicalTrivariate n}
    (ha : BivariateFits ay az a) (hp : p.Fits bxDegree byDegree bz) :
    (RadicalTrivariate.scaleSlice a p).Fits
      bxDegree (ay + byDegree) (az + bz) := by
  constructor
  · simpa [RadicalTrivariate.scaleSlice] using hp.1
  · intro slice hslice
    simp only [RadicalTrivariate.scaleSlice, List.mem_map] at hslice
    obtain ⟨source, hsource, rfl⟩ := hslice
    exact bivariate_mul_fits ha (hp.2 source hsource)

private theorem trivariate_zero_cons_fits {n a b c : ℕ} {p : RadicalTrivariate n}
    (hp : p.Fits a b c) :
    RadicalTrivariate.Fits (a + 1) b c ([] :: p) := by
  constructor
  · simp only [RadicalTrivariate.Fits] at hp ⊢
    simp only [List.length_cons]
    omega
  · intro slice hslice
    simp only [List.mem_cons] at hslice
    rcases hslice with rfl | hslice
    · simp
    · exact hp.2 slice hslice

private theorem trivariate_mul_fits {n ap aq bp bq cp cq : ℕ}
    {p q : RadicalTrivariate n}
    (hp : p.Fits ap bp cp) (hq : q.Fits aq bq cq) :
    (RadicalTrivariate.mul p q).Fits (ap + aq) (bp + bq) (cp + cq) := by
  induction ap generalizing p with
  | zero =>
      cases p with
      | nil => simp [RadicalTrivariate.Fits, RadicalTrivariate.mul]
      | cons a p =>
          have hpEmpty : p = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [RadicalTrivariate.Fits, List.length_cons] at hp
            omega
          subst p
          apply trivariate_add_fits
          · simpa using trivariate_scaleSlice_fits (hp.2 a (by simp)) hq
          · simp [RadicalTrivariate.Fits, RadicalTrivariate.mul]
  | succ ap ih =>
      cases p with
      | nil => simp [RadicalTrivariate.Fits, RadicalTrivariate.mul]
      | cons a p =>
          have hpTail : RadicalTrivariate.Fits ap bp cp p := by
            constructor
            · simp only [RadicalTrivariate.Fits, List.length_cons] at hp
              omega
            · intro slice hslice
              exact hp.2 slice (by simp [hslice])
          rw [RadicalTrivariate.mul]
          apply trivariate_add_fits
          · exact trivariate_mono
              (trivariate_scaleSlice_fits (hp.2 a (by simp)) hq)
              (by omega) le_rfl le_rfl
          · simpa [Nat.succ_add] using trivariate_zero_cons_fits (ih hpTail)

private theorem trivariate_constant_fits {n : ℕ} (a : RadicalExpression n) :
    (RadicalTrivariate.constant a).Fits 0 0 0 := by
  simp [RadicalTrivariate.Fits, RadicalTrivariate.constant]

private theorem trivariate_first_fits {n : ℕ} :
    (RadicalTrivariate.first : RadicalTrivariate n).Fits 1 0 0 := by
  simp [RadicalTrivariate.Fits, RadicalTrivariate.first]

private theorem trivariate_second_fits {n : ℕ} :
    (RadicalTrivariate.second : RadicalTrivariate n).Fits 0 1 0 := by
  simp [RadicalTrivariate.Fits, RadicalTrivariate.second]

private theorem trivariate_third_fits {n : ℕ} :
    (RadicalTrivariate.third : RadicalTrivariate n).Fits 0 0 1 := by
  simp [RadicalTrivariate.Fits, RadicalTrivariate.third]

private theorem trivariate_pow_fits {n a b c k : ℕ} {p : RadicalTrivariate n}
    (hp : p.Fits a b c) :
    (RadicalTrivariate.pow p k).Fits (k * a) (k * b) (k * c) := by
  induction k with
  | zero => simpa only [RadicalTrivariate.pow, zero_mul] using
      trivariate_constant_fits (.constant 1)
  | succ k ih =>
      simpa [RadicalTrivariate.pow, Nat.succ_mul, Nat.add_comm] using
        trivariate_mul_fits ih hp

private theorem univariate_derivative_length_le {n : ℕ}
    (p : RadicalUnivariate n) : p.derivative.length ≤ p.length := by
  induction p with
  | nil => simp [RadicalUnivariate.derivative]
  | cons a p ih =>
      rw [RadicalUnivariate.derivative, univariate_add_length]
      simp only [List.length_cons]
      apply max_le
      · omega
      · omega

private theorem univariate_derivative_fits {n d : ℕ} {p : RadicalUnivariate n}
    (hp : UnivariateFits d p) : UnivariateFits d p.derivative :=
  (univariate_derivative_length_le p).trans hp

private theorem bivariate_add_rows_fits {n e : ℕ} {p q : RadicalBivariate n}
    (hp : ∀ row ∈ p, UnivariateFits e row)
    (hq : ∀ row ∈ q, UnivariateFits e row) :
    ∀ row ∈ RadicalBivariate.add p q, UnivariateFits e row := by
  induction p generalizing q with
  | nil => simpa [RadicalBivariate.add] using hq
  | cons a p ih =>
      cases q with
      | nil => simpa [RadicalBivariate.add] using hp
      | cons b q =>
          intro row hrow
          simp only [RadicalBivariate.add, List.mem_cons] at hrow
          rcases hrow with rfl | hrow
          · exact univariate_add_fits (hp a (by simp)) (hq b (by simp))
          · apply ih (q := q)
            · intro source hsource
              exact hp source (by simp [hsource])
            · intro source hsource
              exact hq source (by simp [hsource])
            · exact hrow

private theorem bivariate_derivativeFirst_length_and_rows {n e : ℕ}
    (p : RadicalBivariate n) (hp : ∀ row ∈ p, UnivariateFits e row) :
    p.derivativeFirst.length ≤ p.length ∧
      ∀ row ∈ p.derivativeFirst, UnivariateFits e row := by
  induction p with
  | nil => simp [RadicalBivariate.derivativeFirst]
  | cons a p ih =>
      have hpTail : ∀ row ∈ p, UnivariateFits e row := by
        intro row hrow
        exact hp row (by simp [hrow])
      have hrec := ih hpTail
      constructor
      · rw [RadicalBivariate.derivativeFirst, bivariate_add_length]
        simp only [List.length_cons]
        apply max_le
        · omega
        · omega
      · rw [RadicalBivariate.derivativeFirst]
        apply bivariate_add_rows_fits hpTail
        intro row hrow
        simp only [List.mem_cons] at hrow
        rcases hrow with rfl | hrow
        · simp [UnivariateFits]
        · exact hrec.2 row hrow

private theorem bivariate_derivativeFirst_fits {n d e : ℕ}
    {p : RadicalBivariate n} (hp : BivariateFits d e p) :
    BivariateFits d e p.derivativeFirst := by
  have h := bivariate_derivativeFirst_length_and_rows p hp.2
  exact ⟨h.1.trans hp.1, h.2⟩

private theorem bivariate_derivativeSecond_fits {n d e : ℕ}
    {p : RadicalBivariate n} (hp : BivariateFits d e p) :
    BivariateFits d e p.derivativeSecond := by
  constructor
  · simpa [RadicalBivariate.derivativeSecond] using hp.1
  · intro row hrow
    simp only [RadicalBivariate.derivativeSecond, List.mem_map] at hrow
    obtain ⟨source, hsource, rfl⟩ := hrow
    exact univariate_derivative_fits (hp.2 source hsource)

private theorem trivariate_derivativeSecond_fits {n a b c : ℕ}
    {p : RadicalTrivariate n} (hp : p.Fits a b c) :
    p.derivativeSecond.Fits a b c := by
  constructor
  · simpa [RadicalTrivariate.derivativeSecond] using hp.1
  · intro slice hslice
    simp only [RadicalTrivariate.derivativeSecond, List.mem_map] at hslice
    obtain ⟨source, hsource, rfl⟩ := hslice
    exact bivariate_derivativeFirst_fits (hp.2 source hsource)

private theorem trivariate_derivativeThird_fits {n a b c : ℕ}
    {p : RadicalTrivariate n} (hp : p.Fits a b c) :
    p.derivativeThird.Fits a b c := by
  constructor
  · simpa [RadicalTrivariate.derivativeThird] using hp.1
  · intro slice hslice
    simp only [RadicalTrivariate.derivativeThird, List.mem_map] at hslice
    obtain ⟨source, hsource, rfl⟩ := hslice
    exact bivariate_derivativeSecond_fits (hp.2 source hsource)

private structure Tridegree where
  first : ℕ
  second : ℕ
  third : ℕ

private def Tridegree.zero : Tridegree := ⟨0, 0, 0⟩

private def Tridegree.sup (a b : Tridegree) : Tridegree :=
  ⟨max a.first b.first, max a.second b.second, max a.third b.third⟩

private def Tridegree.add (a b : Tridegree) : Tridegree :=
  ⟨a.first + b.first, a.second + b.second, a.third + b.third⟩

private def Tridegree.smul (k : ℕ) (a : Tridegree) : Tridegree :=
  ⟨k * a.first, k * a.second, k * a.third⟩

private def Tridegree.Fits {n : ℕ}
    (degree : Tridegree) (p : RadicalTrivariate n) : Prop :=
  p.Fits degree.first degree.second degree.third

private theorem tridegree_add_fits {n : ℕ} {p q : RadicalTrivariate n}
    {a b : Tridegree} (hp : a.Fits p) (hq : b.Fits q) :
    (a.sup b).Fits (RadicalTrivariate.add p q) := by
  apply trivariate_add_fits
  · exact trivariate_mono hp (Nat.le_max_left ..) (Nat.le_max_left ..)
      (Nat.le_max_left ..)
  · exact trivariate_mono hq (Nat.le_max_right ..) (Nat.le_max_right ..)
      (Nat.le_max_right ..)

private theorem tridegree_neg_fits {n : ℕ} {p : RadicalTrivariate n}
    {a : Tridegree} (hp : a.Fits p) : a.Fits (RadicalTrivariate.neg p) :=
  trivariate_neg_fits hp

private theorem tridegree_mul_fits {n : ℕ} {p q : RadicalTrivariate n}
    {a b : Tridegree} (hp : a.Fits p) (hq : b.Fits q) :
    (a.add b).Fits (RadicalTrivariate.mul p q) :=
  trivariate_mul_fits hp hq

private theorem tridegree_pow_fits {n : ℕ} {p : RadicalTrivariate n}
    {a : Tridegree} (hp : a.Fits p) (k : ℕ) :
    (a.smul k).Fits (RadicalTrivariate.pow p k) :=
  trivariate_pow_fits hp

private def tridegreeOperations : WeightedSelfFormulaOperations Tridegree where
  rational _ := .zero
  add := .sup
  neg := id
  mul := .add
  pow a k := a.smul k

private def radicalFormula : WeightedSelfFormula (RadicalTrivariate 18) :=
  weightedSelfFormula radicalPolynomialOperations
    (fun i ↦ RadicalTrivariate.constant (.var i))
    RadicalTrivariate.first RadicalTrivariate.second RadicalTrivariate.third

private def tridegreeFormula : WeightedSelfFormula Tridegree :=
  weightedSelfFormula tridegreeOperations (fun _ ↦ .zero)
    ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, 0, 1⟩

private theorem radicalFormula_fits :
    tridegreeFormula.p.Fits radicalFormula.p ∧
      tridegreeFormula.q.Fits radicalFormula.q ∧
      tridegreeFormula.radicand.Fits radicalFormula.radicand := by
  exact weightedSelfFormula_rel radicalPolynomialOperations tridegreeOperations
    (fun p degree ↦ degree.Fits p)
    (fun q ↦ trivariate_constant_fits (.constant q))
    (fun hp hq ↦ tridegree_add_fits hp hq)
    (fun hp ↦ tridegree_neg_fits hp)
    (fun hp hq ↦ tridegree_mul_fits hp hq)
    (fun hp k ↦ tridegree_pow_fits hp k)
    (atom := fun i ↦ RadicalTrivariate.constant (.var i))
    (atom' := fun _ ↦ .zero)
    (fun i ↦ trivariate_constant_fits (.var i))
    (r := RadicalTrivariate.first) (r' := ⟨1, 0, 0⟩)
    (b := RadicalTrivariate.second) (b' := ⟨0, 1, 0⟩)
    (t := RadicalTrivariate.third) (t' := ⟨0, 0, 1⟩)
    trivariate_first_fits trivariate_second_fits trivariate_third_fits

private theorem radicalFormula_exact_fits :
    radicalFormula.p.Fits 6 4 2 ∧
      radicalFormula.q.Fits 3 2 1 ∧
      radicalFormula.radicand.Fits 4 4 2 := by
  simpa [tridegreeFormula, tridegreeOperations, Tridegree.Fits,
    Tridegree.zero, Tridegree.sup, Tridegree.add, Tridegree.smul,
    weightedSelfFormula] using radicalFormula_fits

/-- The exact exceptional discriminant fits its natural tridegree box. -/
theorem weightedSelfExceptionalDiscriminantPolynomial_fits :
    weightedSelfExceptionalDiscriminantPolynomial.Fits 12 8 4 := by
  change (RadicalTrivariate.add
    (RadicalTrivariate.mul radicalFormula.p radicalFormula.p)
    (RadicalTrivariate.neg
      (RadicalTrivariate.mul
        (RadicalTrivariate.mul radicalFormula.q radicalFormula.q)
        radicalFormula.radicand))).Fits 12 8 4
  apply trivariate_add_fits
  · exact trivariate_mul_fits radicalFormula_exact_fits.1
      radicalFormula_exact_fits.1
  · apply trivariate_neg_fits
    apply trivariate_mono
      (trivariate_mul_fits
        (trivariate_mul_fits radicalFormula_exact_fits.2.1
          radicalFormula_exact_fits.2.1)
        radicalFormula_exact_fits.2.2)
    · norm_num
    · norm_num
    · norm_num

/-- The physical exceptional-face `bb` polynomial fits the discriminant degree box. -/
theorem weightedSelfExceptionalFaceBBPolynomial_fits :
    weightedSelfExceptionalFaceBBPolynomial.Fits 12 8 4 := by
  simpa only [weightedSelfExceptionalFaceBBPolynomial,
    weightedSelfExceptionalFaceBPolynomial] using
    trivariate_derivativeSecond_fits
      (trivariate_derivativeSecond_fits
        weightedSelfExceptionalDiscriminantPolynomial_fits)

/-- The exceptional-face `bb` margin polynomial fits the same physical degree box. -/
theorem weightedSelfExceptionalFaceBBMarginPolynomial_fits :
    weightedSelfExceptionalFaceBBMarginPolynomial.Fits 12 8 4 := by
  simpa only [weightedSelfExceptionalFaceBBMarginPolynomial] using
    trivariate_add_fits weightedSelfExceptionalFaceBBPolynomial_fits
      (trivariate_mono
        (trivariate_constant_fits (.constant (-1 / 10000)))
        (by norm_num) (by norm_num) (by norm_num))

/-- The physical exceptional-face mixed polynomial fits the discriminant degree box. -/
theorem weightedSelfExceptionalFaceBTPolynomial_fits :
    weightedSelfExceptionalFaceBTPolynomial.Fits 12 8 4 := by
  have hbt := trivariate_derivativeThird_fits
    (trivariate_derivativeSecond_fits
      weightedSelfExceptionalDiscriminantPolynomial_fits)
  have htb := trivariate_derivativeSecond_fits
    (trivariate_derivativeThird_fits
      weightedSelfExceptionalDiscriminantPolynomial_fits)
  have hsum := trivariate_add_fits hbt htb
  have hhalf := trivariate_constant_fits
    (n := 18) (.constant (1 / 2))
  simpa only [weightedSelfExceptionalFaceBTPolynomial,
    weightedSelfExceptionalFaceBPolynomial,
    weightedSelfExceptionalFaceTPolynomial, zero_add] using
    trivariate_mul_fits hhalf hsum

/-- The physical exceptional-face `tt` polynomial fits the discriminant degree box. -/
theorem weightedSelfExceptionalFaceTTPolynomial_fits :
    weightedSelfExceptionalFaceTTPolynomial.Fits 12 8 4 := by
  simpa only [weightedSelfExceptionalFaceTTPolynomial,
    weightedSelfExceptionalFaceTPolynomial] using
    trivariate_derivativeThird_fits
      (trivariate_derivativeThird_fits
        weightedSelfExceptionalDiscriminantPolynomial_fits)

private theorem bivariate_constant_fits (a : RadicalExpression 18) :
    BivariateFits 0 0 (RadicalBivariate.constant a) := by
  simp [BivariateFits, UnivariateFits, RadicalBivariate.constant]

private theorem bivariate_first_fits :
    BivariateFits 1 0 (RadicalBivariate.first : RadicalBivariate 18) := by
  simp [BivariateFits, UnivariateFits, RadicalBivariate.first]

private theorem bivariate_second_fits :
    BivariateFits 0 1 (RadicalBivariate.second : RadicalBivariate 18) := by
  simp [BivariateFits, UnivariateFits, RadicalBivariate.second]

private theorem RadicalUnivariate.substituteFace_fits
    (p : RadicalUnivariate 18) {z : RadicalBivariate 18} {first second : ℕ}
    (hz : BivariateFits first second z) :
    BivariateFits (p.length * first) (p.length * second)
      (p.substituteFace z) := by
  induction p with
  | nil => simp [RadicalUnivariate.substituteFace, BivariateFits]
  | cons a p ih =>
      rw [RadicalUnivariate.substituteFace]
      apply bivariate_add_fits
      · apply bivariate_mono (bivariate_constant_fits a)
        · omega
        · omega
      · simpa [Nat.add_mul, Nat.add_comm] using bivariate_mul_fits hz ih

private theorem RadicalBivariate.substituteFace_fits
    (p : RadicalBivariate 18) {y z : RadicalBivariate 18}
    {yFirst ySecond zFirst zSecond rowBound : ℕ}
    (hp : ∀ row ∈ p, row.length ≤ rowBound)
    (hy : BivariateFits yFirst ySecond y)
    (hz : BivariateFits zFirst zSecond z) :
    BivariateFits
      (p.length * yFirst + rowBound * zFirst)
      (p.length * ySecond + rowBound * zSecond)
      (p.substituteFace y z) := by
  induction p with
  | nil => simp [RadicalBivariate.substituteFace, BivariateFits]
  | cons a p ih =>
      have ha := hp a (by simp)
      have hpTail : ∀ row ∈ p, row.length ≤ rowBound := by
        intro row hrow
        exact hp row (by simp [hrow])
      rw [RadicalBivariate.substituteFace]
      apply bivariate_add_fits
      · apply bivariate_mono (RadicalUnivariate.substituteFace_fits a hz)
        · have h := Nat.mul_le_mul_right zFirst ha
          omega
        · have h := Nat.mul_le_mul_right zSecond ha
          omega
      · simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          bivariate_mul_fits hy (ih hpTail)

private theorem RadicalTrivariate.substituteFace_fits
    (p : RadicalTrivariate 18) {x y z : RadicalBivariate 18}
    {xFirst xSecond yFirst ySecond zFirst zSecond sliceBound rowBound : ℕ}
    (hpSlices : ∀ slice ∈ p, slice.length ≤ sliceBound)
    (hpRows : ∀ slice ∈ p, ∀ row ∈ slice, row.length ≤ rowBound)
    (hx : BivariateFits xFirst xSecond x)
    (hy : BivariateFits yFirst ySecond y)
    (hz : BivariateFits zFirst zSecond z) :
    BivariateFits
      (p.length * xFirst + sliceBound * yFirst + rowBound * zFirst)
      (p.length * xSecond + sliceBound * ySecond + rowBound * zSecond)
      (p.substituteFace x y z) := by
  induction p with
  | nil => simp [RadicalTrivariate.substituteFace, BivariateFits]
  | cons a p ih =>
      have haSlices := hpSlices a (by simp)
      have haRows := hpRows a (by simp)
      have hpTailSlices : ∀ slice ∈ p, slice.length ≤ sliceBound := by
        intro slice hslice
        exact hpSlices slice (by simp [hslice])
      have hpTailRows : ∀ slice ∈ p, ∀ row ∈ slice,
          row.length ≤ rowBound := by
        intro slice hslice row hrow
        exact hpRows slice (by simp [hslice]) row hrow
      rw [RadicalTrivariate.substituteFace]
      apply bivariate_add_fits
      · apply bivariate_mono
          (RadicalBivariate.substituteFace_fits a haRows hy hz)
        · have h := Nat.mul_le_mul_right yFirst haSlices
          omega
        · have h := Nat.mul_le_mul_right ySecond haSlices
          omega
      · simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          bivariate_mul_fits hx (ih hpTailSlices hpTailRows)

private theorem exactAffineFace_fits
    {p : RadicalTrivariate 18} (hp : p.Fits 12 8 4) (scale : ℚ) :
    BivariateFits 16 8 (exactAffineFace p scale) := by
  have hx : BivariateFits 0 0 exactFaceOne := by
    simpa only [exactFaceOne] using bivariate_constant_fits (.constant 1)
  have hy : BivariateFits 1 0 exactFaceSecondRadius := by
    simpa only [exactFaceSecondRadius, zero_add] using bivariate_add_fits
      (bivariate_mono (bivariate_constant_fits (.constant (29 / 40)))
        (by omega) (by omega))
      (bivariate_mul_fits
        (bivariate_constant_fits (.constant (1 / 40))) bivariate_first_fits)
  have hz : BivariateFits 0 1 exactFaceProjection := by
    simpa only [exactFaceProjection, zero_add] using bivariate_add_fits
      (bivariate_mono (bivariate_constant_fits (.constant (-209 / 256)))
        (by omega) (by omega))
      (bivariate_mul_fits
        (bivariate_constant_fits (.constant (1 / 256))) bivariate_second_fits)
  have hsub := RadicalTrivariate.substituteFace_fits p
    (fun slice hslice ↦ (hp.2 slice hslice).1)
    (fun slice hslice ↦ (hp.2 slice hslice).2) hx hy hz
  have hscaled := bivariate_mul_fits
    (bivariate_constant_fits (.constant scale)) hsub
  apply bivariate_mono hscaled <;> norm_num at hscaled ⊢

private def facePowerSum (a : Fin 17 → Fin 9 → ℝ) (u v : ℝ) : ℝ :=
  ∑ i, ∑ j, a i j * u ^ (i : ℕ) * v ^ (j : ℕ)

private def faceBernsteinSum (a : Fin 17 → Fin 9 → ℝ) (u v : I) : ℝ :=
  ∑ i, ∑ j, a i j * bernstein 16 i u * bernstein 8 j v

private theorem getD_row_length_le {n bound : ℕ} {p : RadicalBivariate n}
    (hp : ∀ row ∈ p, row.length ≤ bound) (i : ℕ) :
    (p.getD i []).length ≤ bound := by
  by_cases hi : i < p.length
  · rw [List.getD_eq_getElem p [] hi]
    exact hp p[i] (List.getElem_mem ..)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    simp

private theorem exactFace_eval_eq_powerSum
    {p : RadicalBivariate 18} (hp : BivariateFits 16 8 p)
    (input : Fin 18 → ℝ) (u v : ℝ) :
    p.eval input u v =
      facePowerSum (fun i j ↦ exactFaceCoefficient p input i j) u v := by
  rw [RadicalBivariate.eval_eq_sum_getD p hp.1]
  unfold facePowerSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [RadicalUnivariate.eval_eq_sum_getD _
    (getD_row_length_le hp.2 i)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [exactFaceCoefficient]
  ring

private theorem powerToBernstein_finSum (degree count : ℕ)
    (a : Fin count → Fin (degree + 1) → ℝ) (i : Fin (degree + 1)) :
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

private theorem facePowerSum_eq_bernsteinSum
    (a : Fin 17 → Fin 9 → ℝ) (u v : I) :
    facePowerSum a u v =
      faceBernsteinSum
        (fun i j ↦ powerToBernstein 8
          (fun j' ↦ powerToBernstein 16 (fun i' ↦ a i' j') i) j)
        u v := by
  unfold facePowerSum faceBernsteinSum
  calc
    (∑ i, ∑ j, a i j * (u : ℝ) ^ (i : ℕ) * (v : ℝ) ^ (j : ℕ)) =
        ∑ j, (∑ i, a i j * (u : ℝ) ^ (i : ℕ)) * (v : ℝ) ^ (j : ℕ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ = ∑ j, (∑ i, powerToBernstein 16 (fun i' ↦ a i' j) i *
          bernstein 16 i u) * (v : ℝ) ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show (∑ i, a i j * (u : ℝ) ^ (i : ℕ)) =
          ∑ i, powerToBernstein 16 (fun i' ↦ a i' j) i * bernstein 16 i u by
        simpa [paddedPowerEval] using
          paddedPowerEval_eq_bernstein_sum 16 (fun i ↦ a i j) u]
    _ = ∑ j, powerToBernstein 8
          (fun j' ↦ ∑ i, powerToBernstein 16 (fun i' ↦ a i' j') i *
            bernstein 16 i u) j * bernstein 8 j v := by
      simpa [paddedPowerEval] using
        paddedPowerEval_eq_bernstein_sum 8
          (fun j ↦ ∑ i, powerToBernstein 16 (fun i' ↦ a i' j) i *
            bernstein 16 i u) v
    _ = ∑ i, ∑ j, powerToBernstein 8
          (fun j' ↦ powerToBernstein 16 (fun i' ↦ a i' j') i) j *
          bernstein 16 i u * bernstein 8 j v := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [powerToBernstein_finSum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [powerToBernstein_mul]

private theorem faceBernsteinSum_nonneg {a : Fin 17 → Fin 9 → ℝ}
    (ha : ∀ i j, 0 ≤ a i j) (u v : I) :
    0 ≤ faceBernsteinSum a u v := by
  unfold faceBernsteinSum
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (mul_nonneg (ha i j) bernstein_nonneg) bernstein_nonneg

/-- Outward-rounded Bernstein intervals for a physical polynomial on the exceptional face. -/
def weightedSelfExceptionalFaceBernsteinIntervals
    (p : IntervalTrivariate) (scale : ℚ) (i : Fin 17) (j : Fin 9) :
    RationalInterval :=
  (dyadicFaceBernsteinCoefficient (dyadicAffineFace p scale) i j).interpret

/-- Check one row of outward-rounded Bernstein intervals has nonnegative lower endpoints. -/
def checkWeightedSelfExceptionalFaceBernsteinRow
    (p : IntervalTrivariate) (scale : ℚ) (i : Fin 17) : Bool :=
  decide (∀ j, 0 ≤ (weightedSelfExceptionalFaceBernsteinIntervals p scale i j).lower)

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
/-- The outward-rounded face intervals contain every exact chart coefficient. -/
private theorem weightedSelfExceptionalFaceBernsteinIntervals_contains
    {P : IntervalTrivariate} {q : RadicalTrivariate 18}
    {input : Fin 18 → ℝ}
    (hPq : P.Contains input q) (scale : ℚ)
    (i : Fin 17) (j : Fin 9) :
    (weightedSelfExceptionalFaceBernsteinIntervals P scale i j).Contains
      (exactFaceBernsteinCoefficient (exactAffineFace q scale) input i j) := by
  have hface := intervalAffineFace_contains hPq scale
  have hwidens := dyadicAffineFace_widens P scale
  change (weightedSelfExceptionalFaceBernsteinIntervals P scale i j).Contains
    (exactFaceBernsteinCoefficient (exactAffineFace q scale) input i j)
  exact dyadicFaceBernsteinCoefficient_contains hwidens hface i j

/-- A successful exact face-Bernstein check proves nonnegativity on the affine face. -/
theorem weightedSelfExceptionalFace_nonnegative_of_bernstein_check
    {P : IntervalTrivariate} {q : RadicalTrivariate 18}
    {input : Fin 18 → ℝ}
    (hPq : P.Contains input q) (hq : q.Fits 12 8 4) (scale : ℚ)
    (hcheck : ∀ i, checkWeightedSelfExceptionalFaceBernsteinRow P scale i = true)
    (u v : I) :
    0 ≤ scale * q.eval input 1
      (29 / 40 + (u : ℝ) / 40) (-209 / 256 + (v : ℝ) / 256) := by
  have hlower : ∀ i j,
      0 ≤ (weightedSelfExceptionalFaceBernsteinIntervals P scale i j).lower :=
    fun i ↦ of_decide_eq_true (hcheck i)
  have hcoeff : ∀ i j,
      0 ≤ exactFaceBernsteinCoefficient (exactAffineFace q scale) input i j := by
    intro i j
    have hcontains :=
      weightedSelfExceptionalFaceBernsteinIntervals_contains hPq scale i j
    have hlowerReal : (0 : ℝ) ≤
        (weightedSelfExceptionalFaceBernsteinIntervals P scale i j).lower := by
      exact_mod_cast hlower i j
    exact hlowerReal.trans hcontains.1
  rw [← exactAffineFace_eval q scale input]
  rw [exactFace_eval_eq_powerSum (exactAffineFace_fits hq scale)]
  rw [facePowerSum_eq_bernsteinSum]
  exact faceBernsteinSum_nonneg hcoeff u v


end Bescovitch
