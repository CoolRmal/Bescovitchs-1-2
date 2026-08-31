/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.MultivariateDensePolynomial
public import Bescovitch.SixPoint.WeightedMixedCertificateData.Basic
public import Bescovitch.SixPoint.WeightedQuadraticMajorant

/-!
# Exact polynomial for the mixed weighted certificate

Clearing the two stereographic denominators turns the quadratic mixed-score majorant into a
rational polynomial in the six lens coordinates.  This file constructs that polynomial exactly.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

namespace WeightedMixedPolynomial

/-- A dense rational polynomial in the six lens coordinates `(a, h, z, b, k, w)`. -/
abbrev Polynomial := MultivariateDensePolynomial 6

/-- A plane vector whose two coordinates are dense rational polynomials. -/
structure Vector where
  /-- First coordinate. -/
  first : Polynomial
  /-- Second coordinate. -/
  second : Polynomial

/-- Evaluate a polynomial vector at six real coordinates. -/
def Vector.eval (v : Vector) (x : Fin 6 → ℝ) : Plane :=
  !₂[MultivariateDensePolynomial.eval v.first x,
    MultivariateDensePolynomial.eval v.second x]

local notation "C" => MultivariateDensePolynomial.constant 6
local notation "X" => @MultivariateDensePolynomial.coordinate 6
local infixl:65 " +ₚ " => MultivariateDensePolynomial.add 6
local prefix:75 "-ₚ " => MultivariateDensePolynomial.neg 6
local infixr:73 " •ₚ " => fun q ↦ MultivariateDensePolynomial.scale q 6
local infixl:70 " *ₚ " => MultivariateDensePolynomial.mul 6
local infixr:80 " ^ₚ " => @MultivariateDensePolynomial.pow 6

/-- Polynomial subtraction. -/
def sub (p q : Polynomial) : Polynomial := p +ₚ -ₚ q

/-- Add two polynomial plane vectors. -/
def Vector.add (p q : Vector) : Vector := ⟨p.first +ₚ q.first, p.second +ₚ q.second⟩

/-- Subtract two polynomial plane vectors. -/
def Vector.sub (p q : Vector) : Vector :=
  ⟨WeightedMixedPolynomial.sub p.first q.first,
    WeightedMixedPolynomial.sub p.second q.second⟩

/-- Multiply a polynomial plane vector by a polynomial scalar. -/
def Vector.smul (p : Polynomial) (v : Vector) : Vector :=
  ⟨p *ₚ v.first, p *ₚ v.second⟩

/-- The polynomial squared length of a plane vector. -/
def Vector.normSq (v : Vector) : Polynomial :=
  v.first ^ₚ 2 +ₚ v.second ^ₚ 2

/-- The denominator `1 + z²` of a stereographic direction. -/
def denominator (z : Polynomial) : Polynomial := C 1 +ₚ z ^ₚ 2

/-- The numerator of a chord endpoint in stereographic coordinates. -/
def chordNumerator (side : ℚ) (a h z : Polynomial) : Vector :=
  let nx := side •ₚ sub (C 1) (z ^ₚ 2)
  let ny := 2 •ₚ z
  ⟨sub (a *ₚ nx) (h *ₚ ny), a *ₚ ny +ₚ h *ₚ nx⟩

/-- The numerator of the root vector after multiplication by a denominator. -/
def rootNumerator (d : Polynomial) : Vector := ⟨d, C 0⟩

/-- The numerator of a difference involving one rational chord endpoint. -/
def singleDifference (d : Polynomial) (v : Vector) : Vector :=
  (rootNumerator d).sub v

/-- The numerator of a difference involving endpoints from both rational chords. -/
def mixedDifference (dP dW : Polynomial) (p w : Vector) : Vector :=
  (rootNumerator (dP *ₚ dW)).sub ((p.smul dW).add (w.smul dP))

/-- One cleared quadratic upper tangent. -/
def positiveTerm (weight rho : ℚ) (v : Vector) (d factor : Polynomial) : Polynomial :=
  (weight / (2 * rho)) •ₚ ((v.normSq +ₚ (rho ^ 2) •ₚ (d ^ₚ 2)) *ₚ factor)

/-- First coordinate of the rational unit support with stereographic slope `slope`. -/
def supportFirst (slope : ℚ) : ℚ :=
  (1 - slope ^ 2) / (1 + slope ^ 2)

/-- Second coordinate of the rational unit support with stereographic slope `slope`. -/
def supportSecond (slope : ℚ) : ℚ :=
  2 * slope / (1 + slope ^ 2)

/-- The cleared curved lower support for one chord endpoint. -/
def supportNumerator (slope : ℚ) (v : Vector) (d : Polynomial) : Polynomial :=
  let along := (supportFirst slope) •ₚ v.first +ₚ (supportSecond slope) •ₚ v.second
  let across := (-supportSecond slope) •ₚ v.first +ₚ (supportFirst slope) •ₚ v.second
  along *ₚ d +ₚ (1 / 2) •ₚ (across ^ₚ 2)

/-- One cleared weighted lower support. -/
def negativeTerm (weight slope : ℚ) (v : Vector) (d factor : Polynomial) : Polynomial :=
  weight •ₚ (supportNumerator slope v d *ₚ factor)

/-- A point is substituted by the affine image of a centered cube coordinate. -/
def affineCoordinate (i : Fin 6) (lower upper : ℚ) : Polynomial :=
  C ((lower + upper) / 2) +ₚ ((upper - lower) / 2) •ₚ X i

/-- The fixed tensor multidegree `(2, 2, 4, 2, 2, 4)`. -/
def degreeProfile : Fin 6 → MultivariateDensePolynomial.BernsteinDegree
  | 0 | 1 | 3 | 4 => .quadratic
  | 2 | 5 => .quartic

/-- The exact cleared polynomial attached to one mixed-certificate leaf. -/
def leafPolynomial (sideP sideW : ℚ) (a h z b k w : Polynomial)
    (rho : Fin 6 → ℚ) (slope eta : Fin 4 → ℚ) : Polynomial :=
  let c : ℚ := 13866128436518096 / 10 ^ 16
  let lambda : ℚ := 8947642540885 / 10 ^ 14
  let mu : ℚ := 92883833887540 / 10 ^ 14
  let dP := denominator z
  let dW := denominator w
  let dPW := dP *ₚ dW
  let common := dPW ^ₚ 2
  let p₁ := chordNumerator sideP a h z
  let p₂ := chordNumerator sideP (sub a (C c)) h z
  let w₁ := chordNumerator sideW b k w
  let w₂ := chordNumerator sideW (sub b (C c)) k w
  let positives :=
    ((positiveTerm (mu / 2) (rho 0) (singleDifference dP p₁) dP (dW ^ₚ 2) +ₚ
          positiveTerm (mu / 2) (rho 1) (singleDifference dW w₁) dW (dP ^ₚ 2)) +ₚ
        (positiveTerm (1 + lambda) (rho 2) (mixedDifference dP dW p₁ w₁) dPW (C 1) +ₚ
          positiveTerm 1 (rho 3) (mixedDifference dP dW p₂ w₂) dPW (C 1))) +ₚ
      (positiveTerm (mu / 2) (rho 4) (mixedDifference dP dW p₁ w₂) dPW (C 1) +ₚ
        positiveTerm (mu / 2) (rho 5) (mixedDifference dP dW p₂ w₁) dPW (C 1))
  let firstPenalty := (c - 1) * (lambda / 2 + mu)
  let secondPenalty := (c + 1) * lambda / 2 + 3 * c * mu
  let constantTerm := 2 * c * (2 * c - 1) +
    lambda * (3 * c ^ 2 - 3 * c + 2) / 2 + mu * (c ^ 2 - c)
  let negatives :=
    (negativeTerm (firstPenalty / 2) (slope 0) p₁ dP (dW ^ₚ 2) +ₚ
        negativeTerm (firstPenalty / 2) (slope 1) w₁ dW (dP ^ₚ 2)) +ₚ
      (negativeTerm (secondPenalty / 2) (slope 2) p₂ dP (dW ^ₚ 2) +ₚ
        negativeTerm (secondPenalty / 2) (slope 3) w₂ dW (dP ^ₚ 2))
  let diskP₁ := sub (sub (C 1) (a ^ₚ 2)) (h ^ₚ 2)
  let diskP₂ := sub (sub (C 1) ((sub a (C c)) ^ₚ 2)) (h ^ₚ 2)
  let diskW₁ := sub (sub (C 1) (b ^ₚ 2)) (k ^ₚ 2)
  let diskW₂ := sub (sub (C 1) ((sub b (C c)) ^ₚ 2)) (k ^ₚ 2)
  (sub (sub positives negatives) (constantTerm •ₚ common) +ₚ
      (1 / 10 ^ 8) •ₚ common) +ₚ
    (((eta 0) •ₚ (diskP₁ *ₚ common) +ₚ (eta 1) •ₚ (diskP₂ *ₚ common)) +ₚ
      ((eta 2) •ₚ (diskW₁ *ₚ common) +ₚ (eta 3) •ₚ (diskW₂ *ₚ common)))

/-- Interpret the integer leaf data as rationals with common denominator `4096`. -/
def polynomialOfLeaf (sideP sideW : ℚ) (lower upper : Fin 6 → ℚ)
    (data : WeightedMixedLeaf) : Polynomial :=
  leafPolynomial sideP sideW
    (affineCoordinate 0 (lower 0) (upper 0))
    (affineCoordinate 1 (lower 1) (upper 1))
    (affineCoordinate 2 (lower 2) (upper 2))
    (affineCoordinate 3 (lower 3) (upper 3))
    (affineCoordinate 4 (lower 4) (upper 4))
    (affineCoordinate 5 (lower 5) (upper 5))
    (fun i ↦ data.rhoNumerator i / 4096)
    (fun i ↦ data.supportSlopeNumerator i / 4096)
    (fun i ↦ data.slackNumerator i / 4096)

private theorem eval_sub (p q : Polynomial) (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval (sub p q) x =
      MultivariateDensePolynomial.eval p x - MultivariateDensePolynomial.eval q x := by
  simp [sub, MultivariateDensePolynomial.eval_add, MultivariateDensePolynomial.eval_neg]
  ring

private theorem Vector.eval_add (p q : Vector) (x : Fin 6 → ℝ) :
    (p.add q).eval x = p.eval x + q.eval x := by
  ext i
  fin_cases i <;> simp [Vector.add, Vector.eval, MultivariateDensePolynomial.eval_add]

private theorem Vector.eval_sub (p q : Vector) (x : Fin 6 → ℝ) :
    (p.sub q).eval x = p.eval x - q.eval x := by
  ext i
  fin_cases i <;> simp [Vector.sub, Vector.eval, WeightedMixedPolynomial.eval_sub]

private theorem Vector.eval_smul (p : Polynomial) (v : Vector) (x : Fin 6 → ℝ) :
    (v.smul p).eval x = MultivariateDensePolynomial.eval p x • v.eval x := by
  ext i
  fin_cases i <;> simp [Vector.smul, Vector.eval, MultivariateDensePolynomial.eval_mul]

private theorem eval_normSq (v : Vector) (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval v.normSq x = ‖v.eval x‖ ^ 2 := by
  simp [Vector.normSq, MultivariateDensePolynomial.eval_add,
    MultivariateDensePolynomial.eval_pow, Vector.eval, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two]

private theorem eval_denominator (z : Polynomial) (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval (denominator z) x =
      1 + MultivariateDensePolynomial.eval z x ^ 2 := by
  simp [denominator, MultivariateDensePolynomial.eval_add,
    MultivariateDensePolynomial.eval_pow]

private theorem eval_chordNumerator (side : ℚ) (a h z : Polynomial)
    (x : Fin 6 → ℝ) :
    (chordNumerator side a h z).eval x =
      (1 + MultivariateDensePolynomial.eval z x ^ 2) •
        chordChartFirst side (MultivariateDensePolynomial.eval a x)
          (MultivariateDensePolynomial.eval h x) (MultivariateDensePolynomial.eval z x) := by
  ext i
  fin_cases i <;>
    simp [chordNumerator, Vector.eval, chordChartFirst, stereographicDirection, quarterTurn,
      eval_sub, MultivariateDensePolynomial.eval_scale, MultivariateDensePolynomial.eval_mul,
      MultivariateDensePolynomial.eval_add, MultivariateDensePolynomial.eval_pow]
  all_goals
    have hden : (1 : ℝ) + MultivariateDensePolynomial.eval z x ^ 2 ≠ 0 := by positivity
    field_simp [hden] <;> ring

private theorem eval_chordNumerator_second (side c : ℚ) (a h z : Polynomial)
    (x : Fin 6 → ℝ) :
    (chordNumerator side (sub a (C c)) h z).eval x =
      (1 + MultivariateDensePolynomial.eval z x ^ 2) •
        chordChartSecond side c (MultivariateDensePolynomial.eval a x)
          (MultivariateDensePolynomial.eval h x) (MultivariateDensePolynomial.eval z x) := by
  rw [eval_chordNumerator, eval_sub]
  simp only [MultivariateDensePolynomial.eval_constant]
  rfl

private theorem eval_rootNumerator (d : Polynomial) (x : Fin 6 → ℝ) :
    (rootNumerator d).eval x = MultivariateDensePolynomial.eval d x • !₂[1, 0] := by
  ext i
  fin_cases i <;> simp [rootNumerator, Vector.eval]

private theorem eval_singleDifference (d : Polynomial) (v : Vector) (x : Fin 6 → ℝ) :
    (singleDifference d v).eval x =
      MultivariateDensePolynomial.eval d x • !₂[1, 0] - v.eval x := by
  rw [singleDifference, Vector.eval_sub, eval_rootNumerator]

private theorem eval_singleDifference_of_scaled (d : Polynomial) (v : Vector)
    (x : Fin 6 → ℝ) (dval : ℝ) (p : Plane)
    (hd : MultivariateDensePolynomial.eval d x = dval)
    (hv : v.eval x = dval • p) :
    (singleDifference d v).eval x = dval • (!₂[1, 0] - p) := by
  rw [eval_singleDifference, hd, hv]
  module

private theorem eval_mixedDifference (dP dW : Polynomial) (p w : Vector)
    (x : Fin 6 → ℝ) :
    (mixedDifference dP dW p w).eval x =
      (MultivariateDensePolynomial.eval dP x * MultivariateDensePolynomial.eval dW x) •
        !₂[1, 0] -
      (MultivariateDensePolynomial.eval dW x • p.eval x +
        MultivariateDensePolynomial.eval dP x • w.eval x) := by
  rw [mixedDifference, Vector.eval_sub, eval_rootNumerator, Vector.eval_add,
    Vector.eval_smul, Vector.eval_smul, MultivariateDensePolynomial.eval_mul]

private theorem eval_mixedDifference_of_scaled (dP dW : Polynomial) (p w : Vector)
    (x : Fin 6 → ℝ) (dPval dWval : ℝ) (pval wval : Plane)
    (hdP : MultivariateDensePolynomial.eval dP x = dPval)
    (hdW : MultivariateDensePolynomial.eval dW x = dWval)
    (hp : p.eval x = dPval • pval) (hw : w.eval x = dWval • wval) :
    (mixedDifference dP dW p w).eval x =
      (dPval * dWval) • (!₂[1, 0] - pval - wval) := by
  rw [eval_mixedDifference, hdP, hdW, hp, hw]
  module

private theorem eval_positiveTerm (weight rho : ℚ) (v : Vector)
    (d factor : Polynomial) (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval (positiveTerm weight rho v d factor) x =
      (weight / (2 * rho) : ℚ) *
        (‖v.eval x‖ ^ 2 + (rho : ℝ) ^ 2 *
          MultivariateDensePolynomial.eval d x ^ 2) *
        MultivariateDensePolynomial.eval factor x := by
  simp [positiveTerm, MultivariateDensePolynomial.eval_scale,
    MultivariateDensePolynomial.eval_mul, MultivariateDensePolynomial.eval_add,
    MultivariateDensePolynomial.eval_pow, eval_normSq]
  ring

private theorem eval_positiveTerm_of_scaled (weight rho : ℚ) (v : Vector)
    (d factor : Polynomial) (x : Fin 6 → ℝ) (dval factorVal : ℝ) (q : Plane)
    (hrho : (rho : ℝ) ≠ 0)
    (hd : MultivariateDensePolynomial.eval d x = dval)
    (hfactor : MultivariateDensePolynomial.eval factor x = factorVal)
    (hv : v.eval x = dval • q) :
    MultivariateDensePolynomial.eval (positiveTerm weight rho v d factor) x =
      dval ^ 2 * factorVal * quadraticNormTangent weight rho (‖q‖ ^ 2) := by
  rw [eval_positiveTerm, hd, hfactor, hv, norm_smul, Real.norm_eq_abs,
    quadraticNormTangent]
  simp only [mul_pow, sq_abs]
  push_cast
  field_simp [hrho]

private theorem eval_supportNumerator (slope : ℚ) (v : Vector) (d : Polynomial)
    (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval (supportNumerator slope v d) x =
      ((supportFirst slope : ℝ) * (v.eval x) 0 +
          (supportSecond slope : ℝ) * (v.eval x) 1) *
          MultivariateDensePolynomial.eval d x +
        ((-(supportSecond slope : ℝ)) * (v.eval x) 0 +
          (supportFirst slope : ℝ) * (v.eval x) 1) ^ 2 / 2 := by
  simp [supportNumerator, Vector.eval, MultivariateDensePolynomial.eval_add,
    MultivariateDensePolynomial.eval_scale, MultivariateDensePolynomial.eval_mul,
    MultivariateDensePolynomial.eval_pow]
  ring

private theorem quadraticNormSupport_stereographic (slope : ℚ) (v : Plane) :
    quadraticNormSupport (stereographicDirection 1 slope) v =
      (supportFirst slope : ℝ) * v 0 + (supportSecond slope : ℝ) * v 1 +
        ((-(supportSecond slope : ℝ)) * v 0 +
          (supportFirst slope : ℝ) * v 1) ^ 2 / 2 := by
  have hfirst : (supportFirst slope : ℝ) =
      (1 - (slope : ℝ) ^ 2) / (1 + (slope : ℝ) ^ 2) := by
    simp [supportFirst]
  have hsecond : (supportSecond slope : ℝ) =
      2 * (slope : ℝ) / (1 + (slope : ℝ) ^ 2) := by
    simp [supportSecond]
  rw [hfirst, hsecond, quadraticNormSupport,
    norm_stereographicDirection (side := (1 : ℝ)) _ (by norm_num)]
  simp only [one_pow, one_mul]
  simp [stereographicDirection, PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two]
  have hden : (1 : ℝ) + (slope : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp [hden]
  ring

private theorem eval_supportNumerator_of_scaled (slope : ℚ) (v : Vector)
    (d : Polynomial) (x : Fin 6 → ℝ) (dval : ℝ) (p : Plane)
    (hd : MultivariateDensePolynomial.eval d x = dval)
    (hv : v.eval x = dval • p) :
    MultivariateDensePolynomial.eval (supportNumerator slope v d) x =
      dval ^ 2 * quadraticNormSupport (stereographicDirection 1 slope) p := by
  rw [eval_supportNumerator, hd, hv, quadraticNormSupport_stereographic]
  simp
  ring

private theorem eval_negativeTerm (weight slope : ℚ) (v : Vector)
    (d factor : Polynomial) (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval (negativeTerm weight slope v d factor) x =
      weight * MultivariateDensePolynomial.eval (supportNumerator slope v d) x *
        MultivariateDensePolynomial.eval factor x := by
  simp [negativeTerm, MultivariateDensePolynomial.eval_scale,
    MultivariateDensePolynomial.eval_mul]
  ring

private theorem eval_singlePositive (weight rho : ℚ) (dP dW : Polynomial)
    (p : Vector) (x : Fin 6 → ℝ) (dPval dWval : ℝ) (pval : Plane)
    (hrho : (rho : ℝ) ≠ 0)
    (hdP : MultivariateDensePolynomial.eval dP x = dPval)
    (hdW : MultivariateDensePolynomial.eval dW x = dWval)
    (hp : p.eval x = dPval • pval) :
    MultivariateDensePolynomial.eval
        (positiveTerm weight rho (singleDifference dP p) dP (dW ^ₚ 2)) x =
      (dPval * dWval) ^ 2 * quadraticNormTangent weight rho
        (‖(!₂[1, 0] : Plane) - pval‖ ^ 2) := by
  rw [eval_positiveTerm_of_scaled weight rho _ dP (dW ^ₚ 2) x dPval (dWval ^ 2)
    ((!₂[1, 0] : Plane) - pval) hrho hdP]
  · ring
  · simp [MultivariateDensePolynomial.eval_pow, hdW]
  · exact eval_singleDifference_of_scaled dP p x dPval pval hdP hp

private theorem eval_mixedPositive (weight rho : ℚ) (dP dW : Polynomial)
    (p w : Vector) (x : Fin 6 → ℝ) (dPval dWval : ℝ) (pval wval : Plane)
    (hrho : (rho : ℝ) ≠ 0)
    (hdP : MultivariateDensePolynomial.eval dP x = dPval)
    (hdW : MultivariateDensePolynomial.eval dW x = dWval)
    (hp : p.eval x = dPval • pval) (hw : w.eval x = dWval • wval) :
    MultivariateDensePolynomial.eval
        (positiveTerm weight rho (mixedDifference dP dW p w) (dP *ₚ dW) (C 1)) x =
      (dPval * dWval) ^ 2 * quadraticNormTangent weight rho
        (‖(!₂[1, 0] : Plane) - pval - wval‖ ^ 2) := by
  rw [eval_positiveTerm_of_scaled weight rho _ (dP *ₚ dW) (C 1) x
    (dPval * dWval) 1 ((!₂[1, 0] : Plane) - pval - wval) hrho]
  · ring
  · simp [MultivariateDensePolynomial.eval_mul, hdP, hdW]
  · simp
  · exact eval_mixedDifference_of_scaled dP dW p w x dPval dWval pval wval
      hdP hdW hp hw

private theorem eval_clearedSupport (weight slope : ℚ) (dP dW : Polynomial)
    (p : Vector) (x : Fin 6 → ℝ) (dPval dWval : ℝ) (pval : Plane)
    (hdP : MultivariateDensePolynomial.eval dP x = dPval)
    (hdW : MultivariateDensePolynomial.eval dW x = dWval)
    (hp : p.eval x = dPval • pval) :
    MultivariateDensePolynomial.eval (negativeTerm weight slope p dP (dW ^ₚ 2)) x =
      (dPval * dWval) ^ 2 * weight *
        quadraticNormSupport (stereographicDirection 1 slope) pval := by
  rw [eval_negativeTerm, eval_supportNumerator_of_scaled slope p dP x dPval pval hdP hp]
  simp only [MultivariateDensePolynomial.eval_pow, hdW]
  ring

@[simp]
theorem eval_affineCoordinate (i : Fin 6) (lower upper : ℚ) (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval (affineCoordinate i lower upper) x =
      (lower + upper) / 2 + (upper - lower) / 2 * x i := by
  simp [affineCoordinate, MultivariateDensePolynomial.eval_add,
    MultivariateDensePolynomial.eval_scale]

/-- The exact polynomial is the quadratic geometric majorant with its positive denominator
cleared. -/
theorem eval_leafPolynomial_eq_clearedMajorant
    (sideP sideW : ℚ) (a h z b k w : Polynomial)
    (rho : Fin 6 → ℚ) (slope eta : Fin 4 → ℚ) (x : Fin 6 → ℝ)
    (A H Z B K W : ℝ)
    (ha : MultivariateDensePolynomial.eval a x = A)
    (hh : MultivariateDensePolynomial.eval h x = H)
    (hz : MultivariateDensePolynomial.eval z x = Z)
    (hb : MultivariateDensePolynomial.eval b x = B)
    (hk : MultivariateDensePolynomial.eval k x = K)
    (hw : MultivariateDensePolynomial.eval w x = W)
    (hsideP : (sideP : ℝ) ^ 2 = 1) (hsideW : (sideW : ℝ) ^ 2 = 1)
    (hrho : ∀ i, (rho i : ℝ) ≠ 0) :
    MultivariateDensePolynomial.eval
        (leafPolynomial sideP sideW a h z b k w rho slope eta) x =
      ((1 + Z ^ 2) * (1 + W ^ 2)) ^ 2 *
        weightedLensQuadraticCertificateMajorant sideP Z A H sideW W B K
          (rho 0) (rho 1) (rho 2) (rho 3) (rho 4) (rho 5)
          (stereographicDirection 1 (slope 0))
          (stereographicDirection 1 (slope 1))
          (stereographicDirection 1 (slope 2))
          (stereographicDirection 1 (slope 3))
          (eta 0) (eta 1) (eta 2) (eta 3) := by
  let dP := denominator z
  let dW := denominator w
  let p₁ := chordNumerator sideP a h z
  let p₂ := chordNumerator sideP (sub a (C (13866128436518096 / 10 ^ 16))) h z
  let w₁ := chordNumerator sideW b k w
  let w₂ := chordNumerator sideW (sub b (C (13866128436518096 / 10 ^ 16))) k w
  let firstPenalty : ℚ := (13866128436518096 / 10 ^ 16 - 1) *
    (8947642540885 / 10 ^ 14 / 2 + 92883833887540 / 10 ^ 14)
  let secondPenalty : ℚ := (13866128436518096 / 10 ^ 16 + 1) *
    (8947642540885 / 10 ^ 14) / 2 +
      3 * (13866128436518096 / 10 ^ 16) * (92883833887540 / 10 ^ 14)
  have hdP : MultivariateDensePolynomial.eval dP x = 1 + Z ^ 2 := by
    simp [dP, eval_denominator, hz]
  have hdW : MultivariateDensePolynomial.eval dW x = 1 + W ^ 2 := by
    simp [dW, eval_denominator, hw]
  have hp₁ : p₁.eval x = (1 + Z ^ 2) • chordChartFirst sideP A H Z := by
    simpa [p₁, ha, hh, hz] using eval_chordNumerator sideP a h z x
  have hc : ((13866128436518096 / 10 ^ 16 : ℚ) : ℝ) = certificateChord := by
    norm_num [certificateChord]
  have hp₂ : p₂.eval x = (1 + Z ^ 2) •
      chordChartSecond sideP ((13866128436518096 / 10 ^ 16 : ℚ) : ℝ) A H Z := by
    dsimp [p₂]
    rw [eval_chordNumerator_second, ha, hh, hz]
  rw [hc] at hp₂
  have hw₁ : w₁.eval x = (1 + W ^ 2) • chordChartFirst sideW B K W := by
    simpa [w₁, hb, hk, hw] using eval_chordNumerator sideW b k w x
  have hw₂ : w₂.eval x = (1 + W ^ 2) •
      chordChartSecond sideW ((13866128436518096 / 10 ^ 16 : ℚ) : ℝ) B K W := by
    dsimp [w₂]
    rw [eval_chordNumerator_second, hb, hk, hw]
  rw [hc] at hw₂
  have hP := eval_singlePositive (92883833887540 / 10 ^ 14 / 2) (rho 0)
    dP dW p₁ x (1 + Z ^ 2) (1 + W ^ 2) _ (hrho 0) hdP hdW hp₁
  have hW := eval_singlePositive (92883833887540 / 10 ^ 14 / 2) (rho 1)
    dW dP w₁ x (1 + W ^ 2) (1 + Z ^ 2) _ (hrho 1) hdW hdP hw₁
  have h₁₁ := eval_mixedPositive (1 + 8947642540885 / 10 ^ 14) (rho 2)
    dP dW p₁ w₁ x (1 + Z ^ 2) (1 + W ^ 2) _ _ (hrho 2) hdP hdW hp₁ hw₁
  have h₂₂ := eval_mixedPositive 1 (rho 3)
    dP dW p₂ w₂ x (1 + Z ^ 2) (1 + W ^ 2) _ _ (hrho 3) hdP hdW hp₂ hw₂
  have h₁₂ := eval_mixedPositive (92883833887540 / 10 ^ 14 / 2) (rho 4)
    dP dW p₁ w₂ x (1 + Z ^ 2) (1 + W ^ 2) _ _ (hrho 4) hdP hdW hp₁ hw₂
  have h₂₁ := eval_mixedPositive (92883833887540 / 10 ^ 14 / 2) (rho 5)
    dP dW p₂ w₁ x (1 + Z ^ 2) (1 + W ^ 2) _ _ (hrho 5) hdP hdW hp₂ hw₁
  have hcrossOrder :
      (!₂[1, 0] : Plane) - chordChartSecond sideP certificateChord A H Z -
          chordChartFirst sideW B K W =
        !₂[1, 0] - chordChartFirst sideW B K W -
          chordChartSecond sideP certificateChord A H Z := by
    abel
  rw [hcrossOrder] at h₂₁
  have hsP₁ := eval_clearedSupport (firstPenalty / 2) (slope 0) dP dW p₁ x
    (1 + Z ^ 2) (1 + W ^ 2) _ hdP hdW hp₁
  have hsW₁ := eval_clearedSupport (firstPenalty / 2) (slope 1) dW dP w₁ x
    (1 + W ^ 2) (1 + Z ^ 2) _ hdW hdP hw₁
  have hsP₂ := eval_clearedSupport (secondPenalty / 2) (slope 2) dP dW p₂ x
    (1 + Z ^ 2) (1 + W ^ 2) _ hdP hdW hp₂
  have hsW₂ := eval_clearedSupport (secondPenalty / 2) (slope 3) dW dP w₂ x
    (1 + W ^ 2) (1 + Z ^ 2) _ hdW hdP hw₂
  simp only [leafPolynomial, MultivariateDensePolynomial.eval_add, eval_sub,
    MultivariateDensePolynomial.eval_scale, MultivariateDensePolynomial.eval_mul,
    MultivariateDensePolynomial.eval_pow, MultivariateDensePolynomial.eval_constant]
  rw [show denominator z = dP by rfl, show denominator w = dW by rfl]
  rw [show chordNumerator sideP a h z = p₁ by rfl,
    show chordNumerator sideP (sub a (C (13866128436518096 / 10 ^ 16))) h z = p₂ by rfl,
    show chordNumerator sideW b k w = w₁ by rfl,
    show chordNumerator sideW (sub b (C (13866128436518096 / 10 ^ 16))) k w = w₂ by rfl]
  rw [hP, hW, h₁₁, h₂₂, h₁₂, h₂₁, hsP₁, hsW₁, hsP₂, hsW₂, hdP, hdW,
    ha, hh, hb, hk]
  rw [weightedLensQuadraticCertificateMajorant, weightedPairScoreQuadraticMajorant,
    norm_chordChartFirst_sq A H Z hsideP,
    norm_chordChartSecond_sq certificateChord A H Z hsideP,
    norm_chordChartFirst_sq B K W hsideW,
    norm_chordChartSecond_sq certificateChord B K W hsideW]
  norm_num [certificateChord, certificateLambda, certificateMu, weightedFirstPenalty,
    weightedSecondPenalty, weightedConstantTerm]
  set_option maxRecDepth 10000 in
    ring_nf

end WeightedMixedPolynomial

end Bescovitch
