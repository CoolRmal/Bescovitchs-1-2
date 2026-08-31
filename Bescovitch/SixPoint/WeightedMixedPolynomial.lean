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
def Vector.eval (v : Vector) (x : Fin 6 → ℝ) : (EuclideanSpace ℝ (Fin 2)) :=
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

/-- Assemble the positive, negative, constant, and disk-slack certificate terms. -/
def assembleCertificate (positives negatives common : Polynomial) (constantTerm : ℚ)
    (corrections : Polynomial) : Polynomial :=
  (sub (sub positives negatives) (constantTerm •ₚ common) +ₚ
      (1 / 10 ^ 8) •ₚ common) +ₚ corrections

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
  assembleCertificate positives negatives common constantTerm
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
    data.rho data.supportSlope data.slack

private abbrev DegreeProfile := Fin 6 → ℕ

private def firstChordDegree : DegreeProfile := ![1, 1, 2, 0, 0, 0]

private def secondChordDegree : DegreeProfile := ![0, 0, 0, 1, 1, 2]

private def mixedDegree : DegreeProfile := ![1, 1, 2, 1, 1, 2]

private def firstDenominatorDegree : DegreeProfile := ![0, 0, 2, 0, 0, 0]

private def secondDenominatorDegree : DegreeProfile := ![0, 0, 0, 0, 0, 2]

private def commonDegree : DegreeProfile := ![0, 0, 4, 0, 0, 4]

private abbrev certificateDegree : DegreeProfile :=
  fun i ↦ (degreeProfile i).value

private def VectorDegreeBound (degrees : DegreeProfile) (v : Vector) : Prop :=
  MultivariateDensePolynomial.DegreeBound degrees v.first ∧
    MultivariateDensePolynomial.DegreeBound degrees v.second

private theorem degree_bound_sub {degrees : DegreeProfile} {p q : Polynomial}
    (hp : MultivariateDensePolynomial.DegreeBound degrees p)
    (hq : MultivariateDensePolynomial.DegreeBound degrees q) :
    MultivariateDensePolynomial.DegreeBound degrees (sub p q) := by
  exact hp.add hq.neg

private theorem vector_degree_bound_mono {first second : DegreeProfile} {v : Vector}
    (hv : VectorDegreeBound first v) (hdegrees : ∀ i, first i ≤ second i) :
    VectorDegreeBound second v :=
  ⟨hv.1.mono hdegrees, hv.2.mono hdegrees⟩

private theorem vector_degree_bound_add {degrees : DegreeProfile} {p q : Vector}
    (hp : VectorDegreeBound degrees p) (hq : VectorDegreeBound degrees q) :
    VectorDegreeBound degrees (p.add q) := ⟨hp.1.add hq.1, hp.2.add hq.2⟩

private theorem vector_degree_bound_sub {degrees : DegreeProfile} {p q : Vector}
    (hp : VectorDegreeBound degrees p) (hq : VectorDegreeBound degrees q) :
    VectorDegreeBound degrees (p.sub q) :=
  ⟨degree_bound_sub hp.1 hq.1, degree_bound_sub hp.2 hq.2⟩

private theorem vector_degree_bound_smul {scalar vector : DegreeProfile} {p : Polynomial}
    {v : Vector} (hp : MultivariateDensePolynomial.DegreeBound scalar p)
    (hv : VectorDegreeBound vector v) :
    VectorDegreeBound (fun i ↦ scalar i + vector i) (v.smul p) :=
  ⟨hp.mul hv.1, hp.mul hv.2⟩

private theorem degree_bound_norm_sq {degrees : DegreeProfile} {v : Vector}
    (hv : VectorDegreeBound degrees v) :
    MultivariateDensePolynomial.DegreeBound (fun i ↦ 2 * degrees i) v.normSq := by
  exact (hv.1.pow 2).add (hv.2.pow 2)

private theorem degree_bound_affine_coordinate (i : Fin 6) (lower upper : ℚ) :
    MultivariateDensePolynomial.DegreeBound
      (MultivariateDensePolynomial.coordinateDegree i) (affineCoordinate i lower upper) := by
  exact (MultivariateDensePolynomial.degree_bound_constant _ _).add
    (MultivariateDensePolynomial.DegreeBound.scale _
      (MultivariateDensePolynomial.degree_bound_coordinate_degree i))

private theorem degree_bound_denominator {degrees : DegreeProfile} {z : Polynomial}
    (hz : MultivariateDensePolynomial.DegreeBound degrees z) :
    MultivariateDensePolynomial.DegreeBound (fun i ↦ 2 * degrees i) (denominator z) := by
  exact (MultivariateDensePolynomial.degree_bound_constant _ 1).add (hz.pow 2)

private theorem degree_bound_chord_numerator {aDegree hDegree zDegree : DegreeProfile}
    (side : ℚ) {a h z : Polynomial}
    (ha : MultivariateDensePolynomial.DegreeBound aDegree a)
    (hh : MultivariateDensePolynomial.DegreeBound hDegree h)
    (hz : MultivariateDensePolynomial.DegreeBound zDegree z) :
    VectorDegreeBound (fun i ↦ aDegree i + hDegree i + 2 * zDegree i)
      (chordNumerator side a h z) := by
  have hzSquare := hz.pow 2
  have hnx : MultivariateDensePolynomial.DegreeBound (fun i ↦ 2 * zDegree i)
      (side •ₚ sub (C 1) (z ^ₚ 2)) := by
    exact ((MultivariateDensePolynomial.degree_bound_constant _ 1).add hzSquare.neg).scale side
  have hny : MultivariateDensePolynomial.DegreeBound zDegree (2 •ₚ z) := hz.scale 2
  have haNx := ha.mul hnx
  have hhNy := hh.mul hny
  have haNy := ha.mul hny
  have hhNx := hh.mul hnx
  refine ⟨degree_bound_sub (haNx.mono ?_) (hhNy.mono ?_),
    (haNy.mono ?_).add (hhNx.mono ?_)⟩
  all_goals
    intro i
    omega

private theorem degree_bound_root_numerator {degrees : DegreeProfile} {d : Polynomial}
    (hd : MultivariateDensePolynomial.DegreeBound degrees d) :
    VectorDegreeBound degrees (rootNumerator d) :=
  ⟨hd, MultivariateDensePolynomial.degree_bound_constant degrees 0⟩

private theorem degree_bound_single_difference {degrees : DegreeProfile}
    {d : Polynomial} {v : Vector}
    (hd : MultivariateDensePolynomial.DegreeBound degrees d)
    (hv : VectorDegreeBound degrees v) :
    VectorDegreeBound degrees (singleDifference d v) :=
  vector_degree_bound_sub (degree_bound_root_numerator hd) hv

private theorem degree_bound_mixed_difference
    {dPDegree dWDegree pDegree wDegree target : DegreeProfile}
    {dP dW : Polynomial} {p w : Vector}
    (hdP : MultivariateDensePolynomial.DegreeBound dPDegree dP)
    (hdW : MultivariateDensePolynomial.DegreeBound dWDegree dW)
    (hp : VectorDegreeBound pDegree p) (hw : VectorDegreeBound wDegree w)
    (hdPW : ∀ i, dPDegree i + dWDegree i ≤ target i)
    (hpW : ∀ i, dWDegree i + pDegree i ≤ target i)
    (hwP : ∀ i, dPDegree i + wDegree i ≤ target i) :
    VectorDegreeBound target (mixedDifference dP dW p w) := by
  have hroot := degree_bound_root_numerator ((hdP.mul hdW).mono hdPW)
  have hpScaled := vector_degree_bound_mono (vector_degree_bound_smul hdW hp) hpW
  have hwScaled := vector_degree_bound_mono (vector_degree_bound_smul hdP hw) hwP
  exact vector_degree_bound_sub hroot (vector_degree_bound_add hpScaled hwScaled)

private theorem degree_bound_positive_term
    {vectorDegree denominatorDegree factorDegree : DegreeProfile}
    (weight rho : ℚ) {v : Vector} {d factor : Polynomial}
    (hv : VectorDegreeBound vectorDegree v)
    (hd : MultivariateDensePolynomial.DegreeBound denominatorDegree d)
    (hfactor : MultivariateDensePolynomial.DegreeBound factorDegree factor)
    (hdenominator : ∀ i, denominatorDegree i ≤ vectorDegree i) :
    MultivariateDensePolynomial.DegreeBound
      (fun i ↦ 2 * vectorDegree i + factorDegree i) (positiveTerm weight rho v d factor) := by
  have hnorm := degree_bound_norm_sq hv
  have hdSquare : MultivariateDensePolynomial.DegreeBound (fun i ↦ 2 * vectorDegree i)
      (d ^ₚ 2) := (hd.pow 2).mono fun i ↦ by
    exact Nat.mul_le_mul_left 2 (hdenominator i)
  exact ((hnorm.add (hdSquare.scale (rho ^ 2))).mul hfactor).scale _

private theorem degree_bound_support_numerator
    {vectorDegree denominatorDegree : DegreeProfile} (slope : ℚ)
    {v : Vector} {d : Polynomial} (hv : VectorDegreeBound vectorDegree v)
    (hd : MultivariateDensePolynomial.DegreeBound denominatorDegree d)
    (hdenominator : ∀ i, denominatorDegree i ≤ vectorDegree i) :
    MultivariateDensePolynomial.DegreeBound (fun i ↦ 2 * vectorDegree i)
      (supportNumerator slope v d) := by
  have halong : MultivariateDensePolynomial.DegreeBound vectorDegree
      ((supportFirst slope) •ₚ v.first +ₚ (supportSecond slope) •ₚ v.second) :=
    (hv.1.scale _).add (hv.2.scale _)
  have hacross : MultivariateDensePolynomial.DegreeBound vectorDegree
      ((-supportSecond slope) •ₚ v.first +ₚ (supportFirst slope) •ₚ v.second) :=
    (hv.1.scale _).add (hv.2.scale _)
  have halongD : MultivariateDensePolynomial.DegreeBound (fun i ↦ 2 * vectorDegree i)
      (((supportFirst slope) •ₚ v.first +ₚ (supportSecond slope) •ₚ v.second) *ₚ d) :=
    (halong.mul hd).mono fun i ↦ by
      have := hdenominator i
      omega
  exact halongD.add ((hacross.pow 2).scale (1 / 2))

private theorem degree_bound_negative_term
    {vectorDegree denominatorDegree factorDegree : DegreeProfile}
    (weight slope : ℚ) {v : Vector} {d factor : Polynomial}
    (hv : VectorDegreeBound vectorDegree v)
    (hd : MultivariateDensePolynomial.DegreeBound denominatorDegree d)
    (hfactor : MultivariateDensePolynomial.DegreeBound factorDegree factor)
    (hdenominator : ∀ i, denominatorDegree i ≤ vectorDegree i) :
    MultivariateDensePolynomial.DegreeBound
      (fun i ↦ 2 * vectorDegree i + factorDegree i)
      (negativeTerm weight slope v d factor) := by
  exact ((degree_bound_support_numerator slope hv hd hdenominator).mul hfactor).scale weight

private theorem degree_bound_disk_slack {aDegree hDegree : DegreeProfile}
    {a h : Polynomial} (ha : MultivariateDensePolynomial.DegreeBound aDegree a)
    (hh : MultivariateDensePolynomial.DegreeBound hDegree h) :
    MultivariateDensePolynomial.DegreeBound (fun i ↦ 2 * aDegree i + 2 * hDegree i)
      (sub (sub (C 1) (a ^ₚ 2)) (h ^ₚ 2)) := by
  let target := fun i ↦ 2 * aDegree i + 2 * hDegree i
  have haSquare := (ha.pow 2).mono (second := target) fun i ↦ by
    dsimp only [target]
    omega
  have hhSquare := (hh.pow 2).mono (second := target) fun i ↦ by
    dsimp only [target]
    omega
  exact degree_bound_sub
    (degree_bound_sub (MultivariateDensePolynomial.degree_bound_constant target 1) haSquare)
    hhSquare

private theorem degree_bound_assemble_certificate {positives negatives common corrections :
    Polynomial} (constantTerm : ℚ)
    (hpositives : MultivariateDensePolynomial.DegreeBound certificateDegree positives)
    (hnegatives : MultivariateDensePolynomial.DegreeBound certificateDegree negatives)
    (hcommon : MultivariateDensePolynomial.DegreeBound certificateDegree common)
    (hcorrections : MultivariateDensePolynomial.DegreeBound certificateDegree corrections) :
    MultivariateDensePolynomial.DegreeBound certificateDegree
      (assembleCertificate positives negatives common constantTerm corrections) := by
  rw [assembleCertificate]
  exact ((degree_bound_sub (degree_bound_sub hpositives hnegatives)
    (hcommon.scale constantTerm)).add (hcommon.scale (1 / 10 ^ 8))).add hcorrections

set_option maxHeartbeats 1000000 in
private theorem degree_bound_leaf_polynomial (sideP sideW : ℚ) (a h z b k w : Polynomial)
    (rho : Fin 6 → ℚ) (slope eta : Fin 4 → ℚ)
    (ha : MultivariateDensePolynomial.DegreeBound
      (MultivariateDensePolynomial.coordinateDegree 0) a)
    (hh : MultivariateDensePolynomial.DegreeBound
      (MultivariateDensePolynomial.coordinateDegree 1) h)
    (hz : MultivariateDensePolynomial.DegreeBound
      (MultivariateDensePolynomial.coordinateDegree 2) z)
    (hb : MultivariateDensePolynomial.DegreeBound
      (MultivariateDensePolynomial.coordinateDegree 3) b)
    (hk : MultivariateDensePolynomial.DegreeBound
      (MultivariateDensePolynomial.coordinateDegree 4) k)
    (hw : MultivariateDensePolynomial.DegreeBound
      (MultivariateDensePolynomial.coordinateDegree 5) w) :
    MultivariateDensePolynomial.DegreeBound certificateDegree
      (leafPolynomial sideP sideW a h z b k w rho slope eta) := by
  rw [leafPolynomial]
  let c : ℚ := 13866128436518096 / 10 ^ 16
  let lambda : ℚ := 8947642540885 / 10 ^ 14
  let mu : ℚ := 92883833887540 / 10 ^ 14
  let dP := denominator z
  let dW := denominator w
  let p₁ := chordNumerator sideP a h z
  let p₂ := chordNumerator sideP (sub a (C c)) h z
  let w₁ := chordNumerator sideW b k w
  let w₂ := chordNumerator sideW (sub b (C c)) k w
  have hdP : MultivariateDensePolynomial.DegreeBound firstDenominatorDegree dP :=
    (degree_bound_denominator hz).mono (by
      intro i
      fin_cases i <;> norm_num [firstDenominatorDegree,
        MultivariateDensePolynomial.coordinateDegree] <;> decide)
  have hdW : MultivariateDensePolynomial.DegreeBound secondDenominatorDegree dW :=
    (degree_bound_denominator hw).mono (by
      intro i
      fin_cases i <;> norm_num [secondDenominatorDegree,
        MultivariateDensePolynomial.coordinateDegree] <;> decide)
  have hp₁ : VectorDegreeBound firstChordDegree p₁ :=
    vector_degree_bound_mono (degree_bound_chord_numerator sideP ha hh hz) (by
      intro i
      fin_cases i <;> norm_num [firstChordDegree,
        MultivariateDensePolynomial.coordinateDegree] <;> decide)
  have ha₂ := degree_bound_sub ha
    (MultivariateDensePolynomial.degree_bound_constant
      (MultivariateDensePolynomial.coordinateDegree 0) c)
  have hp₂ : VectorDegreeBound firstChordDegree p₂ :=
    vector_degree_bound_mono (degree_bound_chord_numerator sideP ha₂ hh hz) (by
      intro i
      fin_cases i <;> norm_num [firstChordDegree,
        MultivariateDensePolynomial.coordinateDegree] <;> decide)
  have hw₁ : VectorDegreeBound secondChordDegree w₁ :=
    vector_degree_bound_mono (degree_bound_chord_numerator sideW hb hk hw) (by
      intro i
      fin_cases i <;> norm_num [secondChordDegree,
        MultivariateDensePolynomial.coordinateDegree] <;> decide)
  have hb₂ := degree_bound_sub hb
    (MultivariateDensePolynomial.degree_bound_constant
      (MultivariateDensePolynomial.coordinateDegree 3) c)
  have hw₂ : VectorDegreeBound secondChordDegree w₂ :=
    vector_degree_bound_mono (degree_bound_chord_numerator sideW hb₂ hk hw) (by
      intro i
      fin_cases i <;> norm_num [secondChordDegree,
        MultivariateDensePolynomial.coordinateDegree] <;> decide)
  have hdPFirst : ∀ i, firstDenominatorDegree i ≤ firstChordDegree i := by
    intro i
    fin_cases i <;> norm_num [firstDenominatorDegree, firstChordDegree]
  have hdWSecond : ∀ i, secondDenominatorDegree i ≤ secondChordDegree i := by
    intro i
    fin_cases i <;> norm_num [secondDenominatorDegree, secondChordDegree]
  have hdPWMixed : ∀ i,
      firstDenominatorDegree i + secondDenominatorDegree i ≤ mixedDegree i := by
    intro i
    fin_cases i <;> norm_num [firstDenominatorDegree, secondDenominatorDegree, mixedDegree]
  have hdWPFirst : ∀ i,
      secondDenominatorDegree i + firstChordDegree i ≤ mixedDegree i := by
    intro i
    fin_cases i <;> norm_num [secondDenominatorDegree, firstChordDegree, mixedDegree]
  have hdPWSecond : ∀ i,
      firstDenominatorDegree i + secondChordDegree i ≤ mixedDegree i := by
    intro i
    fin_cases i <;> norm_num [firstDenominatorDegree, secondChordDegree, mixedDegree]
  have hsingleP₁ := degree_bound_single_difference (hdP.mono hdPFirst) hp₁
  have hsingleW₁ := degree_bound_single_difference (hdW.mono hdWSecond) hw₁
  have hmixed₁₁ := degree_bound_mixed_difference hdP hdW hp₁ hw₁
    hdPWMixed hdWPFirst hdPWSecond
  have hmixed₂₂ := degree_bound_mixed_difference hdP hdW hp₂ hw₂
    hdPWMixed hdWPFirst hdPWSecond
  have hmixed₁₂ := degree_bound_mixed_difference hdP hdW hp₁ hw₂
    hdPWMixed hdWPFirst hdPWSecond
  have hmixed₂₁ := degree_bound_mixed_difference hdP hdW hp₂ hw₁
    hdPWMixed hdWPFirst hdPWSecond
  have hfactorP := hdP.pow 2
  have hfactorW := hdW.pow 2
  have hdPW := hdP.mul hdW
  have hconstant : MultivariateDensePolynomial.DegreeBound (fun _ : Fin 6 ↦ 0) (C 1) :=
    MultivariateDensePolynomial.degree_bound_constant _ 1
  have hP := degree_bound_positive_term (mu / 2) (rho 0) hsingleP₁ hdP hfactorW hdPFirst
  have hW := degree_bound_positive_term (mu / 2) (rho 1) hsingleW₁ hdW hfactorP
    hdWSecond
  have h₁₁ := degree_bound_positive_term (1 + lambda) (rho 2) hmixed₁₁ hdPW hconstant
    hdPWMixed
  have h₂₂ := degree_bound_positive_term 1 (rho 3) hmixed₂₂ hdPW hconstant hdPWMixed
  have h₁₂ := degree_bound_positive_term (mu / 2) (rho 4) hmixed₁₂ hdPW hconstant
    hdPWMixed
  have h₂₁ := degree_bound_positive_term (mu / 2) (rho 5) hmixed₂₁ hdPW hconstant
    hdPWMixed
  have toCertificate {degrees : DegreeProfile} {p : Polynomial}
      (hp : MultivariateDensePolynomial.DegreeBound degrees p)
      (hdegrees : ∀ i, degrees i ≤ certificateDegree i) :
      MultivariateDensePolynomial.DegreeBound certificateDegree p := hp.mono hdegrees
  have hFirstCertificate : ∀ i,
      2 * firstChordDegree i + 2 * secondDenominatorDegree i ≤ certificateDegree i := by
    intro i
    fin_cases i <;> norm_num [firstChordDegree, secondDenominatorDegree,
      certificateDegree, degreeProfile, MultivariateDensePolynomial.BernsteinDegree.value]
  have hSecondCertificate : ∀ i,
      2 * secondChordDegree i + 2 * firstDenominatorDegree i ≤ certificateDegree i := by
    intro i
    fin_cases i <;> norm_num [secondChordDegree, firstDenominatorDegree,
      certificateDegree, degreeProfile, MultivariateDensePolynomial.BernsteinDegree.value]
  have hP' := toCertificate hP hFirstCertificate
  have hW' := toCertificate hW hSecondCertificate
  have hMixed {p : Polynomial} (hp : MultivariateDensePolynomial.DegreeBound
      (fun i ↦ 2 * mixedDegree i + (fun _ ↦ 0) i) p) :
      MultivariateDensePolynomial.DegreeBound certificateDegree p :=
    toCertificate hp (by
      intro i
      fin_cases i <;> norm_num [mixedDegree, certificateDegree, degreeProfile,
        MultivariateDensePolynomial.BernsteinDegree.value])
  have hpositives := ((hP'.add hW').add ((hMixed h₁₁).add (hMixed h₂₂))).add
    ((hMixed h₁₂).add (hMixed h₂₁))
  let firstPenalty := (c - 1) * (lambda / 2 + mu)
  let secondPenalty := (c + 1) * lambda / 2 + 3 * c * mu
  have hnP₁ := degree_bound_negative_term (firstPenalty / 2) (slope 0) hp₁ hdP hfactorW
    hdPFirst
  have hnW₁ := degree_bound_negative_term (firstPenalty / 2) (slope 1) hw₁ hdW hfactorP
    hdWSecond
  have hnP₂ := degree_bound_negative_term (secondPenalty / 2) (slope 2) hp₂ hdP hfactorW
    hdPFirst
  have hnW₂ := degree_bound_negative_term (secondPenalty / 2) (slope 3) hw₂ hdW hfactorP
    hdWSecond
  have hnegatives := ((toCertificate hnP₁ hFirstCertificate).add
      (toCertificate hnW₁ hSecondCertificate)).add
    ((toCertificate hnP₂ hFirstCertificate).add
      (toCertificate hnW₂ hSecondCertificate))
  have hcommon : MultivariateDensePolynomial.DegreeBound commonDegree
      ((dP *ₚ dW) ^ₚ 2) := (hdPW.pow 2).mono (by
    intro i
    fin_cases i <;> norm_num [firstDenominatorDegree, secondDenominatorDegree, commonDegree])
  have hcommon' := toCertificate hcommon (by
    intro i
    fin_cases i <;> norm_num [commonDegree, certificateDegree, degreeProfile,
      MultivariateDensePolynomial.BernsteinDegree.value])
  have hPdiskCertificate : ∀ i,
      2 * MultivariateDensePolynomial.coordinateDegree 0 i +
          2 * MultivariateDensePolynomial.coordinateDegree 1 i + commonDegree i ≤
        certificateDegree i := by
    intro i
    fin_cases i <;> norm_num [MultivariateDensePolynomial.coordinateDegree, commonDegree,
      certificateDegree, degreeProfile, MultivariateDensePolynomial.BernsteinDegree.value]
  have hWdiskCertificate : ∀ i,
      2 * MultivariateDensePolynomial.coordinateDegree 3 i +
          2 * MultivariateDensePolynomial.coordinateDegree 4 i + commonDegree i ≤
        certificateDegree i := by
    intro i
    fin_cases i <;> norm_num [MultivariateDensePolynomial.coordinateDegree, commonDegree,
      certificateDegree, degreeProfile, MultivariateDensePolynomial.BernsteinDegree.value] <;>
      decide
  have hdiskP₁ := toCertificate
    ((degree_bound_disk_slack ha hh).mul hcommon |>.scale (eta 0)) hPdiskCertificate
  have hdiskP₂ := toCertificate
    ((degree_bound_disk_slack ha₂ hh).mul hcommon |>.scale (eta 1)) hPdiskCertificate
  have hdiskW₁ := toCertificate
    ((degree_bound_disk_slack hb hk).mul hcommon |>.scale (eta 2)) hWdiskCertificate
  have hdiskW₂ := toCertificate
    ((degree_bound_disk_slack hb₂ hk).mul hcommon |>.scale (eta 3)) hWdiskCertificate
  have hcorrections := (hdiskP₁.add hdiskP₂).add (hdiskW₁.add hdiskW₂)
  let constantTerm := 2 * c * (2 * c - 1) +
    lambda * (3 * c ^ 2 - 3 * c + 2) / 2 + mu * (c ^ 2 - c)
  exact degree_bound_assemble_certificate constantTerm hpositives hnegatives hcommon'
    hcorrections

/-- Every mixed leaf polynomial satisfies the multidegree used by its Bernstein checker. -/
theorem polynomial_of_leaf_degree_bound (sideP sideW : ℚ) (lower upper : Fin 6 → ℚ)
    (data : WeightedMixedLeaf) :
    MultivariateDensePolynomial.DegreeBound (fun i ↦ (degreeProfile i).value)
      (polynomialOfLeaf sideP sideW lower upper data) := by
  change MultivariateDensePolynomial.DegreeBound certificateDegree
    (leafPolynomial sideP sideW
      (affineCoordinate 0 (lower 0) (upper 0))
      (affineCoordinate 1 (lower 1) (upper 1))
      (affineCoordinate 2 (lower 2) (upper 2))
      (affineCoordinate 3 (lower 3) (upper 3))
      (affineCoordinate 4 (lower 4) (upper 4))
      (affineCoordinate 5 (lower 5) (upper 5)) data.rho data.supportSlope data.slack)
  exact degree_bound_leaf_polynomial sideP sideW
    (affineCoordinate 0 (lower 0) (upper 0))
    (affineCoordinate 1 (lower 1) (upper 1))
    (affineCoordinate 2 (lower 2) (upper 2))
    (affineCoordinate 3 (lower 3) (upper 3))
    (affineCoordinate 4 (lower 4) (upper 4))
    (affineCoordinate 5 (lower 5) (upper 5)) data.rho data.supportSlope data.slack
    (degree_bound_affine_coordinate 0 (lower 0) (upper 0))
    (degree_bound_affine_coordinate 1 (lower 1) (upper 1))
    (degree_bound_affine_coordinate 2 (lower 2) (upper 2))
    (degree_bound_affine_coordinate 3 (lower 3) (upper 3))
    (degree_bound_affine_coordinate 4 (lower 4) (upper 4))
    (degree_bound_affine_coordinate 5 (lower 5) (upper 5))

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

private theorem eval_norm_sq (v : Vector) (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval v.normSq x = ‖v.eval x‖ ^ 2 := by
  simp [Vector.normSq, MultivariateDensePolynomial.eval_add,
    MultivariateDensePolynomial.eval_pow, Vector.eval, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two]

private theorem eval_denominator (z : Polynomial) (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval (denominator z) x =
      1 + MultivariateDensePolynomial.eval z x ^ 2 := by
  simp [denominator, MultivariateDensePolynomial.eval_add,
    MultivariateDensePolynomial.eval_pow]

private theorem eval_chord_numerator (side : ℚ) (a h z : Polynomial)
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

private theorem eval_chord_numerator_second (side c : ℚ) (a h z : Polynomial)
    (x : Fin 6 → ℝ) :
    (chordNumerator side (sub a (C c)) h z).eval x =
      (1 + MultivariateDensePolynomial.eval z x ^ 2) •
        chordChartSecond side c (MultivariateDensePolynomial.eval a x)
          (MultivariateDensePolynomial.eval h x) (MultivariateDensePolynomial.eval z x) := by
  rw [eval_chord_numerator, eval_sub]
  simp only [MultivariateDensePolynomial.eval_constant]
  rfl

private theorem eval_root_numerator (d : Polynomial) (x : Fin 6 → ℝ) :
    (rootNumerator d).eval x = MultivariateDensePolynomial.eval d x • !₂[1, 0] := by
  ext i
  fin_cases i <;> simp [rootNumerator, Vector.eval]

private theorem eval_single_difference (d : Polynomial) (v : Vector) (x : Fin 6 → ℝ) :
    (singleDifference d v).eval x =
      MultivariateDensePolynomial.eval d x • !₂[1, 0] - v.eval x := by
  rw [singleDifference, Vector.eval_sub, eval_root_numerator]

private theorem eval_single_difference_of_scaled (d : Polynomial) (v : Vector)
    (x : Fin 6 → ℝ) (dval : ℝ) (p : (EuclideanSpace ℝ (Fin 2)))
    (hd : MultivariateDensePolynomial.eval d x = dval)
    (hv : v.eval x = dval • p) :
    (singleDifference d v).eval x = dval • (!₂[1, 0] - p) := by
  rw [eval_single_difference, hd, hv]
  module

private theorem eval_mixed_difference (dP dW : Polynomial) (p w : Vector)
    (x : Fin 6 → ℝ) :
    (mixedDifference dP dW p w).eval x =
      (MultivariateDensePolynomial.eval dP x * MultivariateDensePolynomial.eval dW x) •
        !₂[1, 0] -
      (MultivariateDensePolynomial.eval dW x • p.eval x +
        MultivariateDensePolynomial.eval dP x • w.eval x) := by
  rw [mixedDifference, Vector.eval_sub, eval_root_numerator, Vector.eval_add,
    Vector.eval_smul, Vector.eval_smul, MultivariateDensePolynomial.eval_mul]

private theorem eval_mixed_difference_of_scaled (dP dW : Polynomial) (p w : Vector)
    (x : Fin 6 → ℝ) (dPval dWval : ℝ) (pval wval : (EuclideanSpace ℝ (Fin 2)))
    (hdP : MultivariateDensePolynomial.eval dP x = dPval)
    (hdW : MultivariateDensePolynomial.eval dW x = dWval)
    (hp : p.eval x = dPval • pval) (hw : w.eval x = dWval • wval) :
    (mixedDifference dP dW p w).eval x =
      (dPval * dWval) • (!₂[1, 0] - pval - wval) := by
  rw [eval_mixed_difference, hdP, hdW, hp, hw]
  module

private theorem eval_positive_term (weight rho : ℚ) (v : Vector)
    (d factor : Polynomial) (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval (positiveTerm weight rho v d factor) x =
      (weight / (2 * rho) : ℚ) *
        (‖v.eval x‖ ^ 2 + (rho : ℝ) ^ 2 *
          MultivariateDensePolynomial.eval d x ^ 2) *
        MultivariateDensePolynomial.eval factor x := by
  simp [positiveTerm, MultivariateDensePolynomial.eval_scale,
    MultivariateDensePolynomial.eval_mul, MultivariateDensePolynomial.eval_add,
    MultivariateDensePolynomial.eval_pow, eval_norm_sq]
  ring

private theorem eval_positive_term_of_scaled (weight rho : ℚ) (v : Vector)
    (d factor : Polynomial) (x : Fin 6 → ℝ) (dval factorVal : ℝ)
    (q : EuclideanSpace ℝ (Fin 2))
    (hrho : (rho : ℝ) ≠ 0)
    (hd : MultivariateDensePolynomial.eval d x = dval)
    (hfactor : MultivariateDensePolynomial.eval factor x = factorVal)
    (hv : v.eval x = dval • q) :
    MultivariateDensePolynomial.eval (positiveTerm weight rho v d factor) x =
      dval ^ 2 * factorVal * quadraticNormTangent weight rho (‖q‖ ^ 2) := by
  rw [eval_positive_term, hd, hfactor, hv, norm_smul, Real.norm_eq_abs,
    quadraticNormTangent]
  simp only [mul_pow, sq_abs]
  push_cast
  field_simp [hrho]

private theorem eval_support_numerator (slope : ℚ) (v : Vector) (d : Polynomial)
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

private theorem quadratic_norm_support_stereographic (slope : ℚ)
    (v : EuclideanSpace ℝ (Fin 2)) :
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

private theorem eval_support_numerator_of_scaled (slope : ℚ) (v : Vector)
    (d : Polynomial) (x : Fin 6 → ℝ) (dval : ℝ) (p : (EuclideanSpace ℝ (Fin 2)))
    (hd : MultivariateDensePolynomial.eval d x = dval)
    (hv : v.eval x = dval • p) :
    MultivariateDensePolynomial.eval (supportNumerator slope v d) x =
      dval ^ 2 * quadraticNormSupport (stereographicDirection 1 slope) p := by
  rw [eval_support_numerator, hd, hv, quadratic_norm_support_stereographic]
  simp
  ring

private theorem eval_negative_term (weight slope : ℚ) (v : Vector)
    (d factor : Polynomial) (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval (negativeTerm weight slope v d factor) x =
      weight * MultivariateDensePolynomial.eval (supportNumerator slope v d) x *
        MultivariateDensePolynomial.eval factor x := by
  simp [negativeTerm, MultivariateDensePolynomial.eval_scale,
    MultivariateDensePolynomial.eval_mul]
  ring

private theorem eval_single_positive (weight rho : ℚ) (dP dW : Polynomial)
    (p : Vector) (x : Fin 6 → ℝ) (dPval dWval : ℝ) (pval : (EuclideanSpace ℝ (Fin 2)))
    (hrho : (rho : ℝ) ≠ 0)
    (hdP : MultivariateDensePolynomial.eval dP x = dPval)
    (hdW : MultivariateDensePolynomial.eval dW x = dWval)
    (hp : p.eval x = dPval • pval) :
    MultivariateDensePolynomial.eval
        (positiveTerm weight rho (singleDifference dP p) dP (dW ^ₚ 2)) x =
      (dPval * dWval) ^ 2 * quadraticNormTangent weight rho
        (‖(!₂[1, 0] : (EuclideanSpace ℝ (Fin 2))) - pval‖ ^ 2) := by
  rw [eval_positive_term_of_scaled weight rho _ dP (dW ^ₚ 2) x dPval (dWval ^ 2)
    ((!₂[1, 0] : (EuclideanSpace ℝ (Fin 2))) - pval) hrho hdP]
  · ring
  · simp [MultivariateDensePolynomial.eval_pow, hdW]
  · exact eval_single_difference_of_scaled dP p x dPval pval hdP hp

private theorem eval_mixed_positive (weight rho : ℚ) (dP dW : Polynomial)
    (p w : Vector) (x : Fin 6 → ℝ) (dPval dWval : ℝ)
    (pval wval : EuclideanSpace ℝ (Fin 2))
    (hrho : (rho : ℝ) ≠ 0)
    (hdP : MultivariateDensePolynomial.eval dP x = dPval)
    (hdW : MultivariateDensePolynomial.eval dW x = dWval)
    (hp : p.eval x = dPval • pval) (hw : w.eval x = dWval • wval) :
    MultivariateDensePolynomial.eval
        (positiveTerm weight rho (mixedDifference dP dW p w) (dP *ₚ dW) (C 1)) x =
      (dPval * dWval) ^ 2 * quadraticNormTangent weight rho
        (‖(!₂[1, 0] : (EuclideanSpace ℝ (Fin 2))) - pval - wval‖ ^ 2) := by
  rw [eval_positive_term_of_scaled weight rho _ (dP *ₚ dW) (C 1) x
    (dPval * dWval) 1 ((!₂[1, 0] : (EuclideanSpace ℝ (Fin 2))) - pval - wval) hrho]
  · ring
  · simp [MultivariateDensePolynomial.eval_mul, hdP, hdW]
  · simp
  · exact eval_mixed_difference_of_scaled dP dW p w x dPval dWval pval wval
      hdP hdW hp hw

private theorem eval_cleared_support (weight slope : ℚ) (dP dW : Polynomial)
    (p : Vector) (x : Fin 6 → ℝ) (dPval dWval : ℝ) (pval : (EuclideanSpace ℝ (Fin 2)))
    (hdP : MultivariateDensePolynomial.eval dP x = dPval)
    (hdW : MultivariateDensePolynomial.eval dW x = dWval)
    (hp : p.eval x = dPval • pval) :
    MultivariateDensePolynomial.eval (negativeTerm weight slope p dP (dW ^ₚ 2)) x =
      (dPval * dWval) ^ 2 * weight *
        quadraticNormSupport (stereographicDirection 1 slope) pval := by
  rw [eval_negative_term, eval_support_numerator_of_scaled slope p dP x dPval pval hdP hp]
  simp only [MultivariateDensePolynomial.eval_pow, hdW]
  ring

@[simp]
theorem eval_affine_coordinate (i : Fin 6) (lower upper : ℚ) (x : Fin 6 → ℝ) :
    MultivariateDensePolynomial.eval (affineCoordinate i lower upper) x =
      (lower + upper) / 2 + (upper - lower) / 2 * x i := by
  simp [affineCoordinate, MultivariateDensePolynomial.eval_add,
    MultivariateDensePolynomial.eval_scale]

/-- The exact polynomial is the quadratic geometric majorant with its positive denominator
cleared. -/
theorem eval_leaf_polynomial_eq_cleared_majorant
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
    simpa [p₁, ha, hh, hz] using eval_chord_numerator sideP a h z x
  have hc : ((13866128436518096 / 10 ^ 16 : ℚ) : ℝ) = certificateChord := by
    norm_num [certificateChord]
  have hp₂ : p₂.eval x = (1 + Z ^ 2) •
      chordChartSecond sideP ((13866128436518096 / 10 ^ 16 : ℚ) : ℝ) A H Z := by
    dsimp [p₂]
    rw [eval_chord_numerator_second, ha, hh, hz]
  rw [hc] at hp₂
  have hw₁ : w₁.eval x = (1 + W ^ 2) • chordChartFirst sideW B K W := by
    simpa [w₁, hb, hk, hw] using eval_chord_numerator sideW b k w x
  have hw₂ : w₂.eval x = (1 + W ^ 2) •
      chordChartSecond sideW ((13866128436518096 / 10 ^ 16 : ℚ) : ℝ) B K W := by
    dsimp [w₂]
    rw [eval_chord_numerator_second, hb, hk, hw]
  rw [hc] at hw₂
  have hP := eval_single_positive (92883833887540 / 10 ^ 14 / 2) (rho 0)
    dP dW p₁ x (1 + Z ^ 2) (1 + W ^ 2) _ (hrho 0) hdP hdW hp₁
  have hW := eval_single_positive (92883833887540 / 10 ^ 14 / 2) (rho 1)
    dW dP w₁ x (1 + W ^ 2) (1 + Z ^ 2) _ (hrho 1) hdW hdP hw₁
  have h₁₁ := eval_mixed_positive (1 + 8947642540885 / 10 ^ 14) (rho 2)
    dP dW p₁ w₁ x (1 + Z ^ 2) (1 + W ^ 2) _ _ (hrho 2) hdP hdW hp₁ hw₁
  have h₂₂ := eval_mixed_positive 1 (rho 3)
    dP dW p₂ w₂ x (1 + Z ^ 2) (1 + W ^ 2) _ _ (hrho 3) hdP hdW hp₂ hw₂
  have h₁₂ := eval_mixed_positive (92883833887540 / 10 ^ 14 / 2) (rho 4)
    dP dW p₁ w₂ x (1 + Z ^ 2) (1 + W ^ 2) _ _ (hrho 4) hdP hdW hp₁ hw₂
  have h₂₁ := eval_mixed_positive (92883833887540 / 10 ^ 14 / 2) (rho 5)
    dP dW p₂ w₁ x (1 + Z ^ 2) (1 + W ^ 2) _ _ (hrho 5) hdP hdW hp₂ hw₁
  have hcrossOrder :
      (!₂[1, 0] : (EuclideanSpace ℝ (Fin 2))) - chordChartSecond sideP certificateChord A H Z -
          chordChartFirst sideW B K W =
        !₂[1, 0] - chordChartFirst sideW B K W -
          chordChartSecond sideP certificateChord A H Z := by
    abel
  rw [hcrossOrder] at h₂₁
  have hsP₁ := eval_cleared_support (firstPenalty / 2) (slope 0) dP dW p₁ x
    (1 + Z ^ 2) (1 + W ^ 2) _ hdP hdW hp₁
  have hsW₁ := eval_cleared_support (firstPenalty / 2) (slope 1) dW dP w₁ x
    (1 + W ^ 2) (1 + Z ^ 2) _ hdW hdP hw₁
  have hsP₂ := eval_cleared_support (secondPenalty / 2) (slope 2) dP dW p₂ x
    (1 + Z ^ 2) (1 + W ^ 2) _ hdP hdW hp₂
  have hsW₂ := eval_cleared_support (secondPenalty / 2) (slope 3) dW dP w₂ x
    (1 + W ^ 2) (1 + Z ^ 2) _ hdW hdP hw₂
  simp only [leafPolynomial, assembleCertificate, MultivariateDensePolynomial.eval_add, eval_sub,
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

/-- Evaluating an encoded leaf gives its quadratic majorant times the cleared denominator. -/
theorem eval_polynomial_of_leaf_eq_cleared_majorant
    (sideP sideW : ℚ) (lower upper : Fin 6 → ℚ) (data : WeightedMixedLeaf)
    (y values : Fin 6 → ℝ)
    (hcoordinate : ∀ i, MultivariateDensePolynomial.eval
      (affineCoordinate i (lower i) (upper i)) y = values i)
    (hsideP : (sideP : ℝ) ^ 2 = 1) (hsideW : (sideW : ℝ) ^ 2 = 1)
    (hrho : ∀ i, (data.rho i : ℝ) ≠ 0) :
    MultivariateDensePolynomial.eval (polynomialOfLeaf sideP sideW lower upper data) y =
      ((1 + values 2 ^ 2) * (1 + values 5 ^ 2)) ^ 2 *
        weightedLensQuadraticCertificateMajorant
          sideP (values 2) (values 0) (values 1) sideW (values 5) (values 3) (values 4)
          (data.rho 0) (data.rho 1) (data.rho 2) (data.rho 3) (data.rho 4) (data.rho 5)
          (stereographicDirection 1 (data.supportSlope 0))
          (stereographicDirection 1 (data.supportSlope 1))
          (stereographicDirection 1 (data.supportSlope 2))
          (stereographicDirection 1 (data.supportSlope 3))
          (data.slack 0) (data.slack 1) (data.slack 2) (data.slack 3) := by
  rw [show polynomialOfLeaf sideP sideW lower upper data =
    leafPolynomial sideP sideW
      (affineCoordinate 0 (lower 0) (upper 0))
      (affineCoordinate 1 (lower 1) (upper 1))
      (affineCoordinate 2 (lower 2) (upper 2))
      (affineCoordinate 3 (lower 3) (upper 3))
      (affineCoordinate 4 (lower 4) (upper 4))
      (affineCoordinate 5 (lower 5) (upper 5)) data.rho data.supportSlope data.slack by rfl]
  exact eval_leaf_polynomial_eq_cleared_majorant sideP sideW
    (affineCoordinate 0 (lower 0) (upper 0))
    (affineCoordinate 1 (lower 1) (upper 1))
    (affineCoordinate 2 (lower 2) (upper 2))
    (affineCoordinate 3 (lower 3) (upper 3))
    (affineCoordinate 4 (lower 4) (upper 4))
    (affineCoordinate 5 (lower 5) (upper 5)) data.rho data.supportSlope data.slack y
    (values 0) (values 1) (values 2) (values 3) (values 4) (values 5)
    (hcoordinate 0) (hcoordinate 1) (hcoordinate 2) (hcoordinate 3) (hcoordinate 4)
    (hcoordinate 5) hsideP hsideW hrho

end WeightedMixedPolynomial

end Bescovitch
