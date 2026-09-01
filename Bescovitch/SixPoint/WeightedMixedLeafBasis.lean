/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.RationalEndpointData
public import Bescovitch.SixPoint.WeightedMixedPolynomial

/-!
# The leaf-independent basis of the mixed certificate polynomial

`polynomialOfLeaf` is rebuilt from scratch at every leaf of an adaptive tree, and that rebuild is
the dominant cost of the mixed certificate.  It is however a fixed linear combination of
polynomials in which the stored leaf data does not occur at all: a leaf contributes only the
scalar weights.  This file isolates that basis and evaluates the combination.

Six cleared upper tangents contribute two basis polynomials each, four cleared lower supports
contribute five each, and the cleared common denominator and its four disk slacks contribute one
each, for thirty-seven in all.
-/

@[expose] public section

noncomputable section

namespace Bescovitch
namespace WeightedMixedPolynomial

local notation "C" => MultivariateDensePolynomial.constant 6
local infixl:65 " +ₚ " => MultivariateDensePolynomial.add 6
local infixr:73 " •ₚ " => fun q ↦ MultivariateDensePolynomial.scale q 6
local infixl:70 " *ₚ " => MultivariateDensePolynomial.mul 6
local infixr:80 " ^ₚ " => @MultivariateDensePolynomial.pow 6

open MultivariateDensePolynomial (eval eval_add eval_neg eval_scale eval_mul eval_pow)

/-- The two leaf-independent polynomials of one cleared quadratic upper tangent. -/
structure TangentBasis where
  /-- The cleared squared distance, already multiplied by the term's cofactor. -/
  distance : Polynomial
  /-- The squared stereographic denominator, already multiplied by the same cofactor. -/
  denominator : Polynomial

/-- The upper tangent basis of one cleared difference vector. -/
def tangentBasis (v : Vector) (d factor : Polynomial) : TangentBasis where
  distance := v.normSq *ₚ factor
  denominator := (d ^ₚ 2) *ₚ factor

/-- A cleared upper tangent is the tangent parameter's combination of its two basis polynomials. -/
theorem eval_positiveTerm (weight : ℚ) {rho : ℚ} (hrho : rho ≠ 0) (v : Vector)
    (d factor : Polynomial) (x : Fin 6 → ℝ) :
    eval (positiveTerm weight rho v d factor) x =
      (weight / (2 * rho) : ℚ) * eval (tangentBasis v d factor).distance x +
        (weight * rho / 2 : ℚ) * eval (tangentBasis v d factor).denominator x := by
  have hrhoReal : (rho : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hrho
  simp only [positiveTerm, tangentBasis, eval_scale, eval_mul, eval_add, eval_pow,
    Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  field_simp

/-- The five leaf-independent polynomials of one cleared lower support. -/
structure SupportBasis where
  /-- The first coordinate against the cleared denominator. -/
  alongFirst : Polynomial
  /-- The second coordinate against the cleared denominator. -/
  alongSecond : Polynomial
  /-- The square of the first coordinate. -/
  squareFirst : Polynomial
  /-- The product of the two coordinates. -/
  crossTerm : Polynomial
  /-- The square of the second coordinate. -/
  squareSecond : Polynomial

/-- The lower support basis of one cleared chord endpoint. -/
def supportBasis (v : Vector) (d factor : Polynomial) : SupportBasis where
  alongFirst := (v.first *ₚ d) *ₚ factor
  alongSecond := (v.second *ₚ d) *ₚ factor
  squareFirst := (v.first *ₚ v.first) *ₚ factor
  crossTerm := (v.first *ₚ v.second) *ₚ factor
  squareSecond := (v.second *ₚ v.second) *ₚ factor

/-- A cleared lower support is the support slope's combination of its five basis polynomials. -/
theorem eval_negativeTerm (weight slope : ℚ) (v : Vector) (d factor : Polynomial)
    (x : Fin 6 → ℝ) :
    eval (negativeTerm weight slope v d factor) x =
      (weight * supportFirst slope : ℚ) * eval (supportBasis v d factor).alongFirst x +
        (weight * supportSecond slope : ℚ) * eval (supportBasis v d factor).alongSecond x +
        (weight * supportSecond slope ^ 2 / 2 : ℚ) *
            eval (supportBasis v d factor).squareFirst x -
          (weight * supportFirst slope * supportSecond slope : ℚ) *
              eval (supportBasis v d factor).crossTerm x +
            (weight * supportFirst slope ^ 2 / 2 : ℚ) *
              eval (supportBasis v d factor).squareSecond x := by
  simp only [negativeTerm, supportNumerator, supportBasis, eval_scale, eval_mul, eval_add,
    eval_pow, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat]
  ring

/-- The exact chord length of the certificate charts. -/
def chord : ℚ := 3467 / 2500

/-- The first exact endpoint weight. -/
def lambda : ℚ := 8947642540885 / 10 ^ 14

/-- The second exact endpoint weight. -/
def mu : ℚ := 92883833887540 / 10 ^ 14

/-- The penalty carried by the two root-adjacent supports. -/
def firstPenalty : ℚ := (chord - 1) * (lambda / 2 + mu)

/-- The penalty carried by the two far supports. -/
def secondPenalty : ℚ := (chord + 1) * lambda / 2 + 3 * chord * mu

/-- The thirty-seven leaf-independent polynomials of one mixed-certificate box. -/
structure LeafBasis where
  /-- The two upper-tangent polynomials of each of the six cleared differences. -/
  tangent : Fin 6 → TangentBasis
  /-- The five lower-support polynomials of each of the four cleared chord endpoints. -/
  support : Fin 4 → SupportBasis
  /-- The squared product of the two stereographic denominators. -/
  common : Polynomial
  /-- Each cleared unit-disk slack against that common denominator. -/
  disk : Fin 4 → Polynomial

/-- The leaf-independent basis attached to one mixed-certificate chart box. -/
def leafBasis (sideP sideW : ℚ) (a h z b k w : Polynomial) : LeafBasis :=
  let dP := denominator z
  let dW := denominator w
  let dPW := dP *ₚ dW
  let common := dPW ^ₚ 2
  let p₁ := chordNumerator sideP a h z
  let p₂ := chordNumerator sideP (sub a (C chord)) h z
  let w₁ := chordNumerator sideW b k w
  let w₂ := chordNumerator sideW (sub b (C chord)) k w
  let diskP₁ := sub (sub (C 1) (a ^ₚ 2)) (h ^ₚ 2)
  let diskP₂ := sub (sub (C 1) ((sub a (C chord)) ^ₚ 2)) (h ^ₚ 2)
  let diskW₁ := sub (sub (C 1) (b ^ₚ 2)) (k ^ₚ 2)
  let diskW₂ := sub (sub (C 1) ((sub b (C chord)) ^ₚ 2)) (k ^ₚ 2)
  { tangent := ![tangentBasis (singleDifference dP p₁) dP (dW ^ₚ 2),
      tangentBasis (singleDifference dW w₁) dW (dP ^ₚ 2),
      tangentBasis (mixedDifference dP dW p₁ w₁) dPW (C 1),
      tangentBasis (mixedDifference dP dW p₂ w₂) dPW (C 1),
      tangentBasis (mixedDifference dP dW p₁ w₂) dPW (C 1),
      tangentBasis (mixedDifference dP dW p₂ w₁) dPW (C 1)]
    support := ![supportBasis p₁ dP (dW ^ₚ 2), supportBasis w₁ dW (dP ^ₚ 2),
      supportBasis p₂ dP (dW ^ₚ 2), supportBasis w₂ dW (dP ^ₚ 2)]
    common := common
    disk := ![diskP₁ *ₚ common, diskP₂ *ₚ common,
      diskW₁ *ₚ common, diskW₂ *ₚ common] }

/-- The weight of each of the six cleared upper tangents. -/
def tangentWeight : Fin 6 → ℚ := ![mu / 2, mu / 2, 1 + lambda, 1, mu / 2, mu / 2]

/-- The weight of each of the four cleared lower supports. -/
def supportWeight : Fin 4 → ℚ :=
  ![firstPenalty / 2, firstPenalty / 2, secondPenalty / 2, secondPenalty / 2]

/-- The cleared constant subtracted from the certificate. -/
def constantWeight : ℚ :=
  2 * chord * (2 * chord - 1) + lambda * (3 * chord ^ 2 - 3 * chord + 2) / 2 +
    mu * (chord ^ 2 - chord) - 1 / 10 ^ 8

/-- The real value of one leaf's combination of its thirty-seven basis polynomials. -/
def LeafBasis.combine (basis : LeafBasis) (rho : Fin 6 → ℚ) (slope eta : Fin 4 → ℚ)
    (x : Fin 6 → ℝ) : ℝ :=
  (∑ i : Fin 6, ((tangentWeight i / (2 * rho i) : ℚ) * eval (basis.tangent i).distance x +
        (tangentWeight i * rho i / 2 : ℚ) * eval (basis.tangent i).denominator x)) -
      (∑ j : Fin 4, ((supportWeight j * supportFirst (slope j) : ℚ) *
              eval (basis.support j).alongFirst x +
            (supportWeight j * supportSecond (slope j) : ℚ) *
              eval (basis.support j).alongSecond x +
            (supportWeight j * supportSecond (slope j) ^ 2 / 2 : ℚ) *
              eval (basis.support j).squareFirst x -
            (supportWeight j * supportFirst (slope j) * supportSecond (slope j) : ℚ) *
              eval (basis.support j).crossTerm x +
            (supportWeight j * supportFirst (slope j) ^ 2 / 2 : ℚ) *
              eval (basis.support j).squareSecond x)) -
    (constantWeight : ℚ) * eval basis.common x +
      ∑ j : Fin 4, (eta j : ℚ) * eval (basis.disk j) x

/-- Evaluation of a polynomial difference. -/
theorem eval_sub (p q : Polynomial) (x : Fin 6 → ℝ) :
    eval (sub p q) x = eval p x - eval q x := by
  simp only [sub, eval_add, eval_neg]
  ring

/-- Evaluation of the assembled certificate. -/
theorem eval_assembleCertificate (positives negatives common : Polynomial)
    (constantTerm : ℚ) (corrections : Polynomial) (x : Fin 6 → ℝ) :
    eval (assembleCertificate positives negatives common constantTerm corrections) x =
      eval positives x - eval negatives x -
        ((constantTerm - 1 / 10 ^ 8 : ℚ) : ℝ) * eval common x + eval corrections x := by
  simp only [assembleCertificate, eval_add, eval_scale, eval_sub, Rat.cast_sub,
    Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  ring

/-- The squared product of the two cleared stereographic denominators. -/
def leafCommon (z w : Polynomial) : Polynomial := (denominator z *ₚ denominator w) ^ₚ 2

/-- The six cleared upper tangents of one leaf. -/
def leafPositives (sideP sideW : ℚ) (a h z b k w : Polynomial) (rho : Fin 6 → ℚ) :
    Polynomial :=
  let dP := denominator z
  let dW := denominator w
  let dPW := dP *ₚ dW
  let p₁ := chordNumerator sideP a h z
  let p₂ := chordNumerator sideP (sub a (C chord)) h z
  let w₁ := chordNumerator sideW b k w
  let w₂ := chordNumerator sideW (sub b (C chord)) k w
  ((positiveTerm (mu / 2) (rho 0) (singleDifference dP p₁) dP (dW ^ₚ 2) +ₚ
        positiveTerm (mu / 2) (rho 1) (singleDifference dW w₁) dW (dP ^ₚ 2)) +ₚ
      (positiveTerm (1 + lambda) (rho 2) (mixedDifference dP dW p₁ w₁) dPW (C 1) +ₚ
        positiveTerm 1 (rho 3) (mixedDifference dP dW p₂ w₂) dPW (C 1))) +ₚ
    (positiveTerm (mu / 2) (rho 4) (mixedDifference dP dW p₁ w₂) dPW (C 1) +ₚ
      positiveTerm (mu / 2) (rho 5) (mixedDifference dP dW p₂ w₁) dPW (C 1))

set_option maxHeartbeats 800000 in
/-- The cleared upper tangents are the leaf's combination of their basis polynomials. -/
theorem eval_leafPositives (sideP sideW : ℚ) (a h z b k w : Polynomial)
    {rho : Fin 6 → ℚ} (hrho : ∀ i, rho i ≠ 0) (x : Fin 6 → ℝ) :
    eval (leafPositives sideP sideW a h z b k w rho) x =
      ∑ i : Fin 6, ((tangentWeight i / (2 * rho i) : ℚ) *
          eval ((leafBasis sideP sideW a h z b k w).tangent i).distance x +
        (tangentWeight i * rho i / 2 : ℚ) *
          eval ((leafBasis sideP sideW a h z b k w).tangent i).denominator x) := by
  have hpos (weight : ℚ) (i : Fin 6) (v : Vector) (d factor : Polynomial) :
      eval (positiveTerm weight (rho i) v d factor) x =
        (weight / (2 * rho i) : ℚ) * eval (tangentBasis v d factor).distance x +
          (weight * rho i / 2 : ℚ) * eval (tangentBasis v d factor).denominator x :=
    eval_positiveTerm weight (hrho i) v d factor x
  simp only [leafPositives, leafBasis, tangentWeight, hpos, eval_add, Fin.sum_univ_six,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  push_cast
  ring

set_option maxHeartbeats 4000000 in
/-- The certificate polynomial of a leaf is that leaf's combination of the basis. -/
theorem eval_leafPolynomial (sideP sideW : ℚ) (a h z b k w : Polynomial)
    {rho : Fin 6 → ℚ} (hrho : ∀ i, rho i ≠ 0) (slope eta : Fin 4 → ℚ)
    (x : Fin 6 → ℝ) :
    eval (leafPolynomial sideP sideW a h z b k w rho slope eta) x =
      (leafBasis sideP sideW a h z b k w).combine rho slope eta x := by
  have hpos (weight : ℚ) (i : Fin 6) (v : Vector) (d factor : Polynomial) :
      eval (positiveTerm weight (rho i) v d factor) x =
        (weight / (2 * rho i) : ℚ) * eval (tangentBasis v d factor).distance x +
          (weight * rho i / 2 : ℚ) * eval (tangentBasis v d factor).denominator x :=
    eval_positiveTerm weight (hrho i) v d factor x
  simp only [leafPolynomial, assembleCertificate, leafBasis, LeafBasis.combine,
    tangentWeight, supportWeight, constantWeight, chord, lambda, mu,
    firstPenalty, secondPenalty, hpos, eval_negativeTerm, eval_sub, eval_add,
    eval_scale, eval_mul, Fin.sum_univ_six, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons]
  push_cast
  ring

end WeightedMixedPolynomial
end Bescovitch
