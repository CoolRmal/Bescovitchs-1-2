/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedEqualityLocalData
public import Bescovitch.SixPoint.WeightedMixedEqualityCalculus
public import Bescovitch.SixPoint.WeightedChart
import Bescovitch.Certificates.EndpointTightBounds
import Mathlib.Analysis.Convex.Deriv

/-!
# Antisymmetric concavity on the exceptional mixed-chart face

An exact interval Hessian certificate and ordinary one-variable calculus move the mixed score
to the diagonal of the upper lens face.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Bescovitch.WeightedMixedEqualityLocal

private def geometricScoreVectors (p₁ p₂ w₁ w₂ : EuclideanSpace ℝ (Fin 2)) :
    Fin 10 → EuclideanSpace ℝ (Fin 2)
  | 0 => !₂[1, 0] - p₁ - w₁
  | 1 => !₂[1, 0] - p₂ - w₂
  | 2 => !₂[1, 0] - p₁
  | 3 => !₂[1, 0] - w₁
  | 4 => !₂[1, 0] - p₁ - w₂
  | 5 => !₂[1, 0] - w₁ - p₂
  | 6 => p₁
  | 7 => w₁
  | 8 => p₂
  | 9 => w₂

private def geometricScoreWeights (c lambda mu : ℝ) : Fin 10 → ℝ :=
  ![1 + lambda, 1, mu / 2, mu / 2, mu / 2, mu / 2,
    -weightedFirstPenalty c lambda mu / 2,
    -weightedFirstPenalty c lambda mu / 2,
    -weightedSecondPenalty c lambda mu / 2,
    -weightedSecondPenalty c lambda mu / 2]

/-- Longitudinal coordinate of the upper unit-circle face in stereographic coordinates. -/
def topFaceLongitudinal (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)

/-- Height of the upper unit-circle face in stereographic coordinates. -/
def topFaceHeight (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

private def faceInput (c lambda mu tP zP tW zW : ℝ) : Fin 7 → ℝ :=
  ![c, lambda, mu, tP, zP, tW, zW]

private def faceScore (c lambda mu tP zP tW zW : ℝ) : ℝ :=
  weightedPairScore !₂[1, 0] c lambda mu
    (chordChartFirst (-1) (topFaceLongitudinal tP) (topFaceHeight tP) zP)
    (chordChartSecond (-1) c (topFaceLongitudinal tP) (topFaceHeight tP) zP)
    (chordChartFirst (-1) (topFaceLongitudinal tW) (topFaceHeight tW) zW)
    (chordChartSecond (-1) c (topFaceLongitudinal tW) (topFaceHeight tW) zW)

private lemma faceVectors_eval (c lambda mu tP zP tW zW : ℝ) (i : Fin 10) :
    (faceVectors i).eval (faceInput c lambda mu tP zP tW zW) =
      geometricScoreVectors
        (chordChartFirst (-1) (topFaceLongitudinal tP) (topFaceHeight tP) zP)
        (chordChartSecond (-1) c (topFaceLongitudinal tP) (topFaceHeight tP) zP)
        (chordChartFirst (-1) (topFaceLongitudinal tW) (topFaceHeight tW) zW)
        (chordChartSecond (-1) c (topFaceLongitudinal tW) (topFaceHeight tW) zW) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [geometricScoreVectors, Vector.eval, RationalExpression.eval, faceInput,
      topFaceLongitudinal, topFaceHeight, chordChartFirst, chordChartSecond,
      stereographicDirection, quarterTurn] <;>
    ring

private lemma faceWeights_eval (c lambda mu tP zP tW zW : ℝ) (i : Fin 10) :
    (scoreWeights (.var 0) (.var 1) (.var 2) i).eval
        (faceInput c lambda mu tP zP tW zW) =
      geometricScoreWeights c lambda mu i := by
  fin_cases i <;>
    simp [geometricScoreWeights, faceInput, RationalExpression.eval,
      weightedFirstPenalty, weightedSecondPenalty] <;>
    ring

private lemma faceScore_eq_sum (c lambda mu tP zP tW zW : ℝ) :
    faceScore c lambda mu tP zP tW zW =
      (∑ i, geometricScoreWeights c lambda mu i *
        ‖(faceVectors i).eval (faceInput c lambda mu tP zP tW zW)‖) -
        weightedConstantTerm c lambda mu := by
  simp [faceScore, Fin.sum_univ_succ, faceVectors_eval, geometricScoreVectors,
    geometricScoreWeights, weightedPairScore]
  ring

private def faceDirection (dT dZ : ℝ) : Fin 7 → ℝ :=
  ![0, 0, 0, dT, dZ, -dT, -dZ]

private def faceVectorDerivative (v : Vector 7) (x : Fin 7 → ℝ) (dT dZ : ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  dT • (antiDerivative 3 5 v).eval x + dZ • (antiDerivative 4 6 v).eval x

private def faceVectorSecondDerivative (v : Vector 7) (x : Fin 7 → ℝ)
    (dT dZ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  dT ^ 2 • (antiSecondDerivative 3 5 3 5 v).eval x +
    (dT * dZ) • (antiSecondDerivative 3 5 4 6 v).eval x +
    (dZ * dT) • (antiSecondDerivative 4 6 3 5 v).eval x +
    dZ ^ 2 • (antiSecondDerivative 4 6 4 6 v).eval x

private lemma affineDerivative_faceDirection (v : Vector 7) (x : Fin 7 → ℝ)
    (dT dZ : ℝ) :
    Vector.affineDerivative v x (faceDirection dT dZ) =
      faceVectorDerivative v x dT dZ := by
  ext j
  fin_cases j <;>
    simp [Vector.affineDerivative, faceDirection, faceVectorDerivative, Vector.eval,
      Fin.sum_univ_succ] <;>
    ring

private lemma faceVectorDerivative_anti_t (v : Vector 7) (x : Fin 7 → ℝ)
    (dT dZ : ℝ) :
    faceVectorDerivative (antiDerivative 3 5 v) x dT dZ =
      dT • (antiSecondDerivative 3 5 3 5 v).eval x +
        dZ • (antiSecondDerivative 3 5 4 6 v).eval x := by
  ext j
  fin_cases j <;>
    simp [faceVectorDerivative, Vector.eval] <;>
    ring

private lemma faceVectorDerivative_anti_z (v : Vector 7) (x : Fin 7 → ℝ)
    (dT dZ : ℝ) :
    faceVectorDerivative (antiDerivative 4 6 v) x dT dZ =
      dT • (antiSecondDerivative 4 6 3 5 v).eval x +
        dZ • (antiSecondDerivative 4 6 4 6 v).eval x := by
  ext j
  fin_cases j <;>
    simp [faceVectorDerivative, Vector.eval] <;>
    ring

private theorem hasDerivAt_faceVector (v : Vector 7) (x : Fin 7 → ℝ)
    (dT dZ s : ℝ)
    (hregular : Vector.RegularAt v
      (Expression.affineInput x (faceDirection dT dZ) s)) :
    HasDerivAt
      (fun u ↦ v.eval (Expression.affineInput x (faceDirection dT dZ) u))
      (faceVectorDerivative v
        (Expression.affineInput x (faceDirection dT dZ) s) dT dZ) s := by
  convert! Vector.hasDerivAt_affine v x (faceDirection dT dZ) s hregular using 1
  exact (affineDerivative_faceDirection v _ dT dZ).symm

private theorem hasDerivAt_faceVectorDerivative (v : Vector 7) (x : Fin 7 → ℝ)
    (dT dZ s : ℝ)
    (hregularT : Vector.RegularAt (antiDerivative 3 5 v)
      (Expression.affineInput x (faceDirection dT dZ) s))
    (hregularZ : Vector.RegularAt (antiDerivative 4 6 v)
      (Expression.affineInput x (faceDirection dT dZ) s)) :
    HasDerivAt
      (fun u ↦ faceVectorDerivative v
        (Expression.affineInput x (faceDirection dT dZ) u) dT dZ)
      (faceVectorSecondDerivative v
        (Expression.affineInput x (faceDirection dT dZ) s) dT dZ) s := by
  have ht := (hasDerivAt_faceVector (antiDerivative 3 5 v) x dT dZ s hregularT).const_smul dT
  have hz := (hasDerivAt_faceVector (antiDerivative 4 6 v) x dT dZ s hregularZ).const_smul dZ
  convert! ht.add hz using 1
  rw [faceVectorDerivative_anti_t, faceVectorDerivative_anti_z]
  simp [faceVectorSecondDerivative]
  module

private theorem face_vector_regular (i : Fin 10) (c lambda mu tP zP tW zW : ℝ) :
    Vector.RegularAt (faceVectors i) (faceInput c lambda mu tP zP tW zW) := by
  have htP : 1 + tP * tP ≠ 0 := by nlinarith [sq_nonneg tP]
  have hzP : 1 + zP * zP ≠ 0 := by nlinarith [sq_nonneg zP]
  have htW : 1 + tW * tW ≠ 0 := by nlinarith [sq_nonneg tW]
  have hzW : 1 + zW * zW ≠ 0 := by nlinarith [sq_nonneg zW]
  fin_cases i <;>
    simp [Vector.RegularAt, Expression.RegularAt, RationalExpression.eval, faceInput] <;>
    aesop

private theorem face_anti_regular (i : Fin 10) (c lambda mu tP zP tW zW : ℝ)
    (j j' : Fin 7) :
    Vector.RegularAt (antiDerivative j j' (faceVectors i))
      (faceInput c lambda mu tP zP tW zW) := by
  exact Vector.RegularAt.sub
    ((faceVectors i).partialDerivative j) ((faceVectors i).partialDerivative j') _
    (Vector.regularAt_partialDerivative (faceVectors i) j _
      (face_vector_regular i c lambda mu tP zP tW zW))
    (Vector.regularAt_partialDerivative (faceVectors i) j' _
      (face_vector_regular i c lambda mu tP zP tW zW))

private def faceNormFirstDerivative (v : Vector 7) (x : Fin 7 → ℝ) (dT dZ : ℝ) : ℝ :=
  ⟪v.eval x, faceVectorDerivative v x dT dZ⟫_ℝ / ‖v.eval x‖

private def faceNormSecondDerivative (v : Vector 7) (x : Fin 7 → ℝ) (dT dZ : ℝ) : ℝ :=
  (⟪faceVectorDerivative v x dT dZ, faceVectorDerivative v x dT dZ⟫_ℝ +
      ⟪v.eval x, faceVectorSecondDerivative v x dT dZ⟫_ℝ) / ‖v.eval x‖ -
    ⟪v.eval x, faceVectorDerivative v x dT dZ⟫_ℝ ^ 2 / ‖v.eval x‖ ^ 3

private theorem hasDerivAt_faceNorm (v : Vector 7) (x : Fin 7 → ℝ)
    (dT dZ s : ℝ)
    (hregular : Vector.RegularAt v
      (Expression.affineInput x (faceDirection dT dZ) s))
    (hnorm : 0 < ‖v.eval (Expression.affineInput x (faceDirection dT dZ) s)‖) :
    HasDerivAt
      (fun u ↦ ‖v.eval (Expression.affineInput x (faceDirection dT dZ) u)‖)
      (faceNormFirstDerivative v
        (Expression.affineInput x (faceDirection dT dZ) s) dT dZ) s := by
  exact HasDerivAt.norm_of_ne_zero (hasDerivAt_faceVector v x dT dZ s hregular)
    (norm_ne_zero_iff.mp hnorm.ne')

private theorem hasDerivAt_faceNormFirstDerivative (v : Vector 7) (x : Fin 7 → ℝ)
    (dT dZ s : ℝ)
    (hregular : Vector.RegularAt v
      (Expression.affineInput x (faceDirection dT dZ) s))
    (hregularT : Vector.RegularAt (antiDerivative 3 5 v)
      (Expression.affineInput x (faceDirection dT dZ) s))
    (hregularZ : Vector.RegularAt (antiDerivative 4 6 v)
      (Expression.affineInput x (faceDirection dT dZ) s))
    (hnorm : 0 < ‖v.eval (Expression.affineInput x (faceDirection dT dZ) s)‖) :
    HasDerivAt
      (fun u ↦ faceNormFirstDerivative v
        (Expression.affineInput x (faceDirection dT dZ) u) dT dZ)
      (faceNormSecondDerivative v
        (Expression.affineInput x (faceDirection dT dZ) s) dT dZ) s := by
  exact HasDerivAt.norm_first_derivative
    (hasDerivAt_faceVector v x dT dZ s hregular)
    (hasDerivAt_faceVectorDerivative v x dT dZ s hregularT hregularZ)
    (norm_ne_zero_iff.mp hnorm.ne')

private def faceScoreFirstDerivative (c lambda mu : ℝ) (x : Fin 7 → ℝ)
    (dT dZ : ℝ) : ℝ :=
  ∑ i, geometricScoreWeights c lambda mu i *
    faceNormFirstDerivative (faceVectors i) x dT dZ

private def faceScoreSecondDerivative (c lambda mu : ℝ) (x : Fin 7 → ℝ)
    (dT dZ : ℝ) : ℝ :=
  ∑ i, geometricScoreWeights c lambda mu i *
    faceNormSecondDerivative (faceVectors i) x dT dZ

private lemma face_affine_input (c lambda mu tP zP tW zW dT dZ s : ℝ) :
    Expression.affineInput (faceInput c lambda mu tP zP tW zW)
        (faceDirection dT dZ) s =
      faceInput c lambda mu (tP + s * dT) (zP + s * dZ)
        (tW - s * dT) (zW - s * dZ) := by
  funext i
  fin_cases i <;> simp [Expression.affineInput, faceInput, faceDirection] <;> ring

private theorem hasDerivAt_faceScoreAlong
    (c lambda mu tP zP tW zW dT dZ s : ℝ)
    (hnorm : ∀ i, 0 < ‖(faceVectors i).eval
      (faceInput c lambda mu (tP + s * dT) (zP + s * dZ)
        (tW - s * dT) (zW - s * dZ))‖) :
    HasDerivAt
      (fun u ↦ faceScore c lambda mu (tP + u * dT) (zP + u * dZ)
        (tW - u * dT) (zW - u * dZ))
      (faceScoreFirstDerivative c lambda mu
        (faceInput c lambda mu (tP + s * dT) (zP + s * dZ)
          (tW - s * dT) (zW - s * dZ)) dT dZ) s := by
  let x := faceInput c lambda mu tP zP tW zW
  have haffine (u : ℝ) : Expression.affineInput x (faceDirection dT dZ) u =
      faceInput c lambda mu (tP + u * dT) (zP + u * dZ)
        (tW - u * dT) (zW - u * dZ) := face_affine_input ..
  have hnormDeriv (i : Fin 10) := hasDerivAt_faceNorm (faceVectors i) x dT dZ s
    (by rw [haffine]; exact face_vector_regular i ..) (by rw [haffine]; exact hnorm i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    (hasDerivAt_const s (geometricScoreWeights c lambda mu i)).mul (hnormDeriv i)
  have hsum' : HasDerivAt
      (fun u ↦ ∑ i, geometricScoreWeights c lambda mu i *
        ‖(faceVectors i).eval
          (faceInput c lambda mu (tP + u * dT) (zP + u * dZ)
            (tW - u * dT) (zW - u * dZ))‖)
      (faceScoreFirstDerivative c lambda mu
        (faceInput c lambda mu (tP + s * dT) (zP + s * dZ)
          (tW - s * dT) (zW - s * dZ)) dT dZ) s := by
    rw [← haffine s]
    convert! hsum using 1 <;> simp [faceScoreFirstDerivative, haffine]
  have hscore := hsum'.sub_const (weightedConstantTerm c lambda mu)
  convert! hscore using 1
  funext u
  rw [faceScore_eq_sum]

private theorem hasDerivAt_faceScoreFirstDerivativeAlong
    (c lambda mu tP zP tW zW dT dZ s : ℝ)
    (hnorm : ∀ i, 0 < ‖(faceVectors i).eval
      (faceInput c lambda mu (tP + s * dT) (zP + s * dZ)
        (tW - s * dT) (zW - s * dZ))‖) :
    HasDerivAt
      (fun u ↦ faceScoreFirstDerivative c lambda mu
        (faceInput c lambda mu (tP + u * dT) (zP + u * dZ)
          (tW - u * dT) (zW - u * dZ)) dT dZ)
      (faceScoreSecondDerivative c lambda mu
        (faceInput c lambda mu (tP + s * dT) (zP + s * dZ)
          (tW - s * dT) (zW - s * dZ)) dT dZ) s := by
  let x := faceInput c lambda mu tP zP tW zW
  have haffine (u : ℝ) : Expression.affineInput x (faceDirection dT dZ) u =
      faceInput c lambda mu (tP + u * dT) (zP + u * dZ)
        (tW - u * dT) (zW - u * dZ) := face_affine_input ..
  have hnormSecond (i : Fin 10) := hasDerivAt_faceNormFirstDerivative
    (faceVectors i) x dT dZ s
    (by rw [haffine]; exact face_vector_regular i ..)
    (by
      rw [haffine]
      exact face_anti_regular i c lambda mu (tP + s * dT) (zP + s * dZ)
        (tW - s * dT) (zW - s * dZ) 3 5)
    (by
      rw [haffine]
      exact face_anti_regular i c lambda mu (tP + s * dT) (zP + s * dZ)
        (tW - s * dT) (zW - s * dZ) 4 6)
    (by rw [haffine]; exact hnorm i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    (hasDerivAt_const s (geometricScoreWeights c lambda mu i)).mul (hnormSecond i)
  rw [← haffine s]
  convert! hsum using 1 <;>
    simp [faceScoreFirstDerivative, faceScoreSecondDerivative, haffine]

private def faceLiftInput (c lambda mu tP zP tW zW : ℝ) (y : Fin 10 → ℝ) : Fin 17 → ℝ :=
  fun i ↦ Fin.addCases (motive := fun _ ↦ ℝ) (faceInput c lambda mu tP zP tW zW) y i

@[simp] private lemma faceLiftInput_castAdd (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) (i : Fin 7) :
    faceLiftInput c lambda mu tP zP tW zW y (Fin.castAdd 10 i) =
      faceInput c lambda mu tP zP tW zW i := by
  simp [faceLiftInput]

@[simp] private lemma faceLiftInput_natAdd (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) (i : Fin 10) :
    faceLiftInput c lambda mu tP zP tW zW y (Fin.natAdd 7 i) = y i := by
  simp [faceLiftInput]

@[simp] private lemma faceLiftInput_zero (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) : faceLiftInput c lambda mu tP zP tW zW y 0 = c := by
  simpa [faceInput] using faceLiftInput_castAdd c lambda mu tP zP tW zW y (0 : Fin 7)

@[simp] private lemma faceLiftInput_one (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) : faceLiftInput c lambda mu tP zP tW zW y 1 = lambda := by
  simpa [faceInput] using faceLiftInput_castAdd c lambda mu tP zP tW zW y (1 : Fin 7)

@[simp] private lemma faceLiftInput_two (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) : faceLiftInput c lambda mu tP zP tW zW y 2 = mu := by
  simpa [faceInput] using faceLiftInput_castAdd c lambda mu tP zP tW zW y (2 : Fin 7)

@[simp] private lemma faceLiftInput_three (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) : faceLiftInput c lambda mu tP zP tW zW y 3 = tP := by
  simpa [faceInput] using faceLiftInput_castAdd c lambda mu tP zP tW zW y (3 : Fin 7)

@[simp] private lemma faceLiftInput_four (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) : faceLiftInput c lambda mu tP zP tW zW y 4 = zP := by
  simpa [faceInput] using faceLiftInput_castAdd c lambda mu tP zP tW zW y (4 : Fin 7)

@[simp] private lemma faceLiftInput_five (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) : faceLiftInput c lambda mu tP zP tW zW y 5 = tW := by
  simpa [faceInput] using faceLiftInput_castAdd c lambda mu tP zP tW zW y (5 : Fin 7)

@[simp] private lemma faceLiftInput_six (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) : faceLiftInput c lambda mu tP zP tW zW y 6 = zW := by
  simpa [faceInput] using faceLiftInput_castAdd c lambda mu tP zP tW zW y (6 : Fin 7)

private def faceExtendedInput (c lambda mu tP zP tW zW : ℝ) : Fin 17 → ℝ :=
  faceLiftInput c lambda mu tP zP tW zW
    (fun i ↦ ‖(faceVectors i).eval (faceInput c lambda mu tP zP tW zW)‖)

@[simp] private lemma faceExtendedInput_natAdd
    (c lambda mu tP zP tW zW : ℝ) (i : Fin 10) :
    faceExtendedInput c lambda mu tP zP tW zW (Fin.natAdd 7 i) =
      ‖(faceVectors i).eval (faceInput c lambda mu tP zP tW zW)‖ := by
  simp [faceExtendedInput]

private lemma faceExtendedInput_castAdd (c lambda mu tP zP tW zW : ℝ) (i : Fin 7) :
    faceExtendedInput c lambda mu tP zP tW zW (Fin.castAdd 10 i) =
      faceInput c lambda mu tP zP tW zW i := by
  simp [faceExtendedInput]

@[simp] private lemma faceExtendedInput_zero (c lambda mu tP zP tW zW : ℝ) :
    faceExtendedInput c lambda mu tP zP tW zW 0 = c := by
  simpa [faceInput] using faceExtendedInput_castAdd c lambda mu tP zP tW zW (0 : Fin 7)

@[simp] private lemma faceExtendedInput_one (c lambda mu tP zP tW zW : ℝ) :
    faceExtendedInput c lambda mu tP zP tW zW 1 = lambda := by
  simpa [faceInput] using faceExtendedInput_castAdd c lambda mu tP zP tW zW (1 : Fin 7)

@[simp] private lemma faceExtendedInput_two (c lambda mu tP zP tW zW : ℝ) :
    faceExtendedInput c lambda mu tP zP tW zW 2 = mu := by
  simpa [faceInput] using faceExtendedInput_castAdd c lambda mu tP zP tW zW (2 : Fin 7)

@[simp] private lemma faceExtendedInput_three (c lambda mu tP zP tW zW : ℝ) :
    faceExtendedInput c lambda mu tP zP tW zW 3 = tP := by
  simpa [faceInput] using faceExtendedInput_castAdd c lambda mu tP zP tW zW (3 : Fin 7)

@[simp] private lemma faceExtendedInput_four (c lambda mu tP zP tW zW : ℝ) :
    faceExtendedInput c lambda mu tP zP tW zW 4 = zP := by
  simpa [faceInput] using faceExtendedInput_castAdd c lambda mu tP zP tW zW (4 : Fin 7)

@[simp] private lemma faceExtendedInput_five (c lambda mu tP zP tW zW : ℝ) :
    faceExtendedInput c lambda mu tP zP tW zW 5 = tW := by
  simpa [faceInput] using faceExtendedInput_castAdd c lambda mu tP zP tW zW (5 : Fin 7)

@[simp] private lemma faceExtendedInput_six (c lambda mu tP zP tW zW : ℝ) :
    faceExtendedInput c lambda mu tP zP tW zW 6 = zW := by
  simpa [faceInput] using faceExtendedInput_castAdd c lambda mu tP zP tW zW (6 : Fin 7)

set_option maxHeartbeats 2000000 in
private lemma faceHessianVectors_eval_lift (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) (i : Fin 10) :
    (faceHessianVectors i).eval (faceLiftInput c lambda mu tP zP tW zW y) =
      (faceVectors i).eval (faceInput c lambda mu tP zP tW zW) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [Vector.eval, RationalExpression.eval, faceInput]

private lemma faceHessianWeights_eval_lift (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) (i : Fin 10) :
    (faceHessianWeights i).eval (faceLiftInput c lambda mu tP zP tW zW y) =
      geometricScoreWeights c lambda mu i := by
  fin_cases i <;>
    simp [geometricScoreWeights, RationalExpression.eval, weightedFirstPenalty,
      weightedSecondPenalty] <;>
    ring

private lemma faceScore_eq_hessian_sum (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) :
    faceScore c lambda mu tP zP tW zW =
      (∑ i, (faceHessianWeights i).eval (faceLiftInput c lambda mu tP zP tW zW y) *
        ‖(faceHessianVectors i).eval (faceLiftInput c lambda mu tP zP tW zW y)‖) -
        weightedConstantTerm c lambda mu := by
  rw [faceScore_eq_sum]
  apply congrArg (fun q : ℝ ↦ q - weightedConstantTerm c lambda mu)
  apply Finset.sum_congr rfl
  intro i _
  rw [faceHessianWeights_eval_lift, faceHessianVectors_eval_lift]

private def faceHessianVectorDerivative (v : Vector 17) (x : Fin 17 → ℝ)
    (dT dZ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  dT • (antiDerivative 3 5 v).eval x + dZ • (antiDerivative 4 6 v).eval x

private def faceHessianVectorSecondDerivative (v : Vector 17) (x : Fin 17 → ℝ)
    (dT dZ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  dT ^ 2 • (antiSecondDerivative 3 5 3 5 v).eval x +
    (dT * dZ) • (antiSecondDerivative 3 5 4 6 v).eval x +
    (dZ * dT) • (antiSecondDerivative 4 6 3 5 v).eval x +
    dZ ^ 2 • (antiSecondDerivative 4 6 4 6 v).eval x

private def faceHessianNormSecondDerivative (v : Vector 17) (x : Fin 17 → ℝ)
    (dT dZ : ℝ) : ℝ :=
  (⟪faceHessianVectorDerivative v x dT dZ,
      faceHessianVectorDerivative v x dT dZ⟫_ℝ +
      ⟪v.eval x, faceHessianVectorSecondDerivative v x dT dZ⟫_ℝ) / ‖v.eval x‖ -
    ⟪v.eval x, faceHessianVectorDerivative v x dT dZ⟫_ℝ ^ 2 / ‖v.eval x‖ ^ 3
private def faceHessianNormFirstDerivative (v : Vector 17) (x : Fin 17 → ℝ)
    (dT dZ : ℝ) : ℝ :=
  ⟪v.eval x, faceHessianVectorDerivative v x dT dZ⟫_ℝ / ‖v.eval x‖
private def faceHessianScoreFirstDerivative (x : Fin 17 → ℝ)
    (dT dZ : ℝ) : ℝ :=
  ∑ i, (faceHessianWeights i).eval x *
    faceHessianNormFirstDerivative (faceHessianVectors i) x dT dZ

private def faceHessianScoreSecondDerivative (x : Fin 17 → ℝ)
    (dT dZ : ℝ) : ℝ :=
  ∑ i, (faceHessianWeights i).eval x *
    faceHessianNormSecondDerivative (faceHessianVectors i) x dT dZ
private def normSecondForm (v di dj dij : EuclideanSpace ℝ (Fin 2)) (r : ℝ) : ℝ :=
  (⟪di, dj⟫_ℝ + ⟪v, dij⟫_ℝ) / r - ⟪v, di⟫_ℝ * ⟪v, dj⟫_ℝ / r ^ 3

private lemma normAntiHessian_eval (v : Vector 17) (r : Expression 17)
    (i₁ i₂ j₁ j₂ : Fin 17) (x : Fin 17 → ℝ) :
    (normAntiHessian v r i₁ i₂ j₁ j₂).eval x =
      normSecondForm (v.eval x) ((antiDerivative i₁ i₂ v).eval x)
        ((antiDerivative j₁ j₂ v).eval x)
        ((antiSecondDerivative i₁ i₂ j₁ j₂ v).eval x) (r.eval x) := by
  change (((antiDerivative i₁ i₂ v).dot (antiDerivative j₁ j₂ v)).eval x +
          (v.dot (antiSecondDerivative i₁ i₂ j₁ j₂ v)).eval x) / r.eval x -
        ((v.dot (antiDerivative i₁ i₂ v)).eval x *
          (v.dot (antiDerivative j₁ j₂ v)).eval x) /
            (r.eval x * (r.eval x * r.eval x)) = _
  rw [Vector.eval_dot, Vector.eval_dot, Vector.eval_dot, Vector.eval_dot]
  simp only [normSecondForm]
  ring

private lemma antiSecondDerivative_comm_eval (v : Vector 17)
    (i₁ i₂ j₁ j₂ : Fin 17) (x : Fin 17 → ℝ) :
    (antiSecondDerivative i₁ i₂ j₁ j₂ v).eval x =
      (antiSecondDerivative j₁ j₂ i₁ i₂ v).eval x := by
  ext k
  fin_cases k <;>
    simp [Vector.eval, Expression.partialDerivative_comm_eval]
  all_goals ring

private lemma normAntiHessian_comm_eval (v : Vector 17) (r : Expression 17)
    (i₁ i₂ j₁ j₂ : Fin 17) (x : Fin 17 → ℝ) :
    (normAntiHessian v r i₁ i₂ j₁ j₂).eval x =
      (normAntiHessian v r j₁ j₂ i₁ i₂).eval x := by
  rw [normAntiHessian_eval, normAntiHessian_eval,
    antiSecondDerivative_comm_eval v i₁ i₂ j₁ j₂ x]
  simp only [normSecondForm]
  rw [real_inner_comm ((antiDerivative i₁ i₂ v).eval x)
    ((antiDerivative j₁ j₂ v).eval x)]
  ring

private lemma face_hessian_norm_second_eq_quadratic (v : Vector 17) (x : Fin 17 → ℝ)
    (r : Expression 17) (hr : r.eval x = ‖v.eval x‖) (dT dZ : ℝ) :
    faceHessianNormSecondDerivative v x dT dZ =
      dT ^ 2 * (normAntiHessian v r 3 5 3 5).eval x +
      dT * dZ * (normAntiHessian v r 3 5 4 6).eval x +
      dZ * dT * (normAntiHessian v r 4 6 3 5).eval x +
      dZ ^ 2 * (normAntiHessian v r 4 6 4 6).eval x := by
  rw [normAntiHessian_eval, normAntiHessian_eval, normAntiHessian_eval,
    normAntiHessian_eval, hr]
  rw [faceHessianNormSecondDerivative]
  simp only [faceHessianVectorDerivative, faceHessianVectorSecondDerivative,
    normSecondForm, inner_add_left, inner_add_right]
  simp only [inner_smul_left, inner_smul_right, conj_trivial]
  rw [real_inner_comm ((antiDerivative 4 6 v).eval x)
    ((antiDerivative 3 5 v).eval x)]
  ring

private lemma face_hessian_score_second_eq_negative_quadratic
    (c lambda mu tP zP tW zW dT dZ : ℝ) :
    faceHessianScoreSecondDerivative
        (faceExtendedInput c lambda mu tP zP tW zW) dT dZ =
      -(dT ^ 2 * faceNegativeHessian00.eval
          (faceExtendedInput c lambda mu tP zP tW zW) +
        dT * dZ * faceNegativeHessian01.eval
          (faceExtendedInput c lambda mu tP zP tW zW) +
        dZ * dT * faceNegativeHessian10.eval
          (faceExtendedInput c lambda mu tP zP tW zW) +
        dZ ^ 2 * faceNegativeHessian11.eval
          (faceExtendedInput c lambda mu tP zP tW zW)) := by
  let x := faceExtendedInput c lambda mu tP zP tW zW
  have hterm (i : Fin 10) :
      faceHessianNormSecondDerivative (faceHessianVectors i) x dT dZ =
        dT ^ 2 * (normAntiHessian (faceHessianVectors i)
            (.var (Fin.natAdd 7 i)) 3 5 3 5).eval x +
        dT * dZ * (normAntiHessian (faceHessianVectors i)
            (.var (Fin.natAdd 7 i)) 3 5 4 6).eval x +
        dZ * dT * (normAntiHessian (faceHessianVectors i)
            (.var (Fin.natAdd 7 i)) 4 6 3 5).eval x +
        dZ ^ 2 * (normAntiHessian (faceHessianVectors i)
            (.var (Fin.natAdd 7 i)) 4 6 4 6).eval x := by
    apply face_hessian_norm_second_eq_quadratic
    rw [RationalExpression.eval]
    dsimp only [x]
    rw [faceExtendedInput_natAdd]
    exact (congrArg norm (faceHessianVectors_eval_lift c lambda mu tP zP tW zW
      (fun j ↦ ‖(faceVectors j).eval (faceInput c lambda mu tP zP tW zW)‖) i)).symm
  dsimp only [x] at hterm
  rw [faceHessianScoreSecondDerivative]
  simp_rw [hterm]
  simp only [faceNegativeHessian00, faceNegativeHessian01, faceNegativeHessian10,
    faceNegativeHessian11, faceNegativeHessianEntry, if_true, if_false,
    Bool.false_eq_true, Expression.eval_neg]
  rw [Expression.eval_sum, Expression.eval_sum, Expression.eval_sum, Expression.eval_sum]
  simp_rw [Expression.eval_mul]
  ring_nf
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  ring_nf

private lemma face_negative_hessian_off_diagonal_eq (x : Fin 17 → ℝ) :
    faceNegativeHessian01.eval x = faceNegativeHessian10.eval x := by
  simp only [faceNegativeHessian01, faceNegativeHessian10, faceNegativeHessianEntry,
    Bool.false_eq_true, if_true, if_false, Expression.eval_neg]
  rw [Expression.eval_sum, Expression.eval_sum]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i _
  rw [Expression.eval_mul, Expression.eval_mul, normAntiHessian_comm_eval]

private theorem face_input_mem (tP zP tW zW : ℝ)
    (htP : 0.2745 ≤ tP ∧ tP ≤ 0.2754)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (htW : 0.2745 ≤ tW ∧ tW ≤ 0.2754)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655) :
    ∀ i, (exactFaceRootBox i).Contains
      (faceInput cStar endpointLambda endpointMu tP zP tW zW i) := by
  intro i
  fin_cases i
  · have hc : (13866128436518096 : ℝ) / 10 ^ 16 ≤ cStar ∧
        cStar ≤ 13866128436518100 / 10 ^ 16 :=
      ⟨cStar_mem_isolation_box.1.le, cStar_mem_isolation_box.2.le⟩
    norm_num [exactFaceRootBox, RationalInterval.Contains, faceInput] at hc ⊢
    exact hc
  · have h := endpointLambda_tight_bounds
    norm_num [exactFaceRootBox, RationalInterval.Contains, faceInput] at h ⊢
    exact h
  · have h := endpointMu_tight_bounds
    norm_num [exactFaceRootBox, RationalInterval.Contains, faceInput] at h ⊢
    exact h
  · norm_num [exactFaceRootBox, RationalInterval.Contains, faceInput] at htP ⊢
    exact htP
  · norm_num [exactFaceRootBox, RationalInterval.Contains, faceInput] at hzP ⊢
    exact hzP
  · norm_num [exactFaceRootBox, RationalInterval.Contains, faceInput] at htW ⊢
    exact htW
  · norm_num [exactFaceRootBox, RationalInterval.Contains, faceInput] at hzW ⊢
    exact hzW

private theorem face_hessian_certificate_sound (tP zP tW zW : ℝ)
    (htP : 0.2745 ≤ tP ∧ tP ≤ 0.2754)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (htW : 0.2745 ≤ tW ∧ tW ≤ 0.2754)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655) :
    0 < faceNegativeHessian00.eval
        (faceExtendedInput cStar endpointLambda endpointMu tP zP tW zW) ∧
      0 < faceNegativeHessianDeterminant.eval
        (faceExtendedInput cStar endpointLambda endpointMu tP zP tW zW) ∧
      ∀ i, 0 < ‖(faceVectors i).eval
        (faceInput cStar endpointLambda endpointMu tP zP tW zW)‖ := by
  have hmem := face_input_mem tP zP tW zW htP hzP htW hzW
  have hpivot := exact_local_tree_sound faceVectors faceNegativeHessian00
    faceHessianCertificateTree exactFaceRootBox face_hessian_pivot_tree_exact
    (faceInput cStar endpointLambda endpointMu tP zP tW zW) hmem
  have hdet := exact_local_tree_sound faceVectors faceNegativeHessianDeterminant
    faceHessianCertificateTree exactFaceRootBox face_hessian_determinant_tree_exact
    (faceInput cStar endpointLambda endpointMu tP zP tW zW) hmem
  have hext : faceExtendedInput cStar endpointLambda endpointMu tP zP tW zW =
      fun i ↦ Fin.addCases (faceInput cStar endpointLambda endpointMu tP zP tW zW)
        (fun j ↦ ‖(faceVectors j).eval
          (faceInput cStar endpointLambda endpointMu tP zP tW zW)‖) i := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hext]
    exact hpivot.1
  · rw [hext]
    exact hdet.1
  · exact hpivot.2

private theorem face_hessian_score_second_nonpos (tP zP tW zW dT dZ : ℝ)
    (htP : 0.2745 ≤ tP ∧ tP ≤ 0.2754)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (htW : 0.2745 ≤ tW ∧ tW ≤ 0.2754)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655) :
    faceHessianScoreSecondDerivative
      (faceExtendedInput cStar endpointLambda endpointMu tP zP tW zW) dT dZ ≤ 0 := by
  let x := faceExtendedInput cStar endpointLambda endpointMu tP zP tW zW
  let A := faceNegativeHessian00.eval x
  let B := faceNegativeHessian01.eval x
  let C := faceNegativeHessian10.eval x
  let D := faceNegativeHessian11.eval x
  let delta := faceNegativeHessianDeterminant.eval x
  have hcertificate := face_hessian_certificate_sound tP zP tW zW htP hzP htW hzW
  have hA : 0 < A := hcertificate.1
  have hdelta : 0 < delta := hcertificate.2.1
  have hBC : B = C := face_negative_hessian_off_diagonal_eq x
  have hdeltaEq : delta = A * D - B * C := by
    simp [delta, A, B, C, D]
  have hidentity :
      A * (dT ^ 2 * A + dT * dZ * B + dZ * dT * C + dZ ^ 2 * D) =
        (A * dT + B * dZ) ^ 2 + delta * dZ ^ 2 := by
    rw [hdeltaEq, hBC]
    ring
  have hproduct :
      0 ≤ A * (dT ^ 2 * A + dT * dZ * B + dZ * dT * C + dZ ^ 2 * D) := by
    rw [hidentity]
    positivity
  have hquadratic :
      0 ≤ dT ^ 2 * A + dT * dZ * B + dZ * dT * C + dZ ^ 2 * D := by
    exact nonneg_of_mul_nonneg_right hproduct hA
  rw [face_hessian_score_second_eq_negative_quadratic]
  exact neg_nonpos.mpr hquadratic

set_option maxHeartbeats 2000000 in
private lemma faceHessianVectorDerivative_eval_lift (c lambda mu tP zP tW zW : ℝ)
    (y : Fin 10 → ℝ) (i : Fin 10) (dT dZ : ℝ) :
    faceHessianVectorDerivative (faceHessianVectors i)
        (faceLiftInput c lambda mu tP zP tW zW y) dT dZ =
      faceVectorDerivative (faceVectors i) (faceInput c lambda mu tP zP tW zW) dT dZ := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [faceHessianVectorDerivative, faceVectorDerivative, Vector.eval,
      Expression.partialDerivative, RationalExpression.eval, faceInput]

set_option maxHeartbeats 4000000 in
private lemma faceHessianVectorSecondDerivative_eval_lift
    (c lambda mu tP zP tW zW : ℝ) (y : Fin 10 → ℝ) (i : Fin 10) (dT dZ : ℝ) :
    faceHessianVectorSecondDerivative (faceHessianVectors i)
        (faceLiftInput c lambda mu tP zP tW zW y) dT dZ =
      faceVectorSecondDerivative (faceVectors i)
        (faceInput c lambda mu tP zP tW zW) dT dZ := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [faceHessianVectorSecondDerivative, faceVectorSecondDerivative, Vector.eval,
      Expression.partialDerivative, RationalExpression.eval, faceInput]

private lemma faceHessianScoreFirstDerivative_eval_lift
    (c lambda mu tP zP tW zW : ℝ) (y : Fin 10 → ℝ) (dT dZ : ℝ) :
    faceHessianScoreFirstDerivative
        (faceLiftInput c lambda mu tP zP tW zW y) dT dZ =
      faceScoreFirstDerivative c lambda mu (faceInput c lambda mu tP zP tW zW) dT dZ := by
  rw [faceHessianScoreFirstDerivative, faceScoreFirstDerivative]
  apply Finset.sum_congr rfl
  intro i _
  rw [faceHessianWeights_eval_lift]
  simp only [faceHessianNormFirstDerivative, faceNormFirstDerivative]
  rw [faceHessianVectors_eval_lift, faceHessianVectorDerivative_eval_lift]

private lemma faceHessianScoreSecondDerivative_eval_lift
    (c lambda mu tP zP tW zW : ℝ) (y : Fin 10 → ℝ) (dT dZ : ℝ) :
    faceHessianScoreSecondDerivative
        (faceLiftInput c lambda mu tP zP tW zW y) dT dZ =
      faceScoreSecondDerivative c lambda mu (faceInput c lambda mu tP zP tW zW) dT dZ := by
  rw [faceHessianScoreSecondDerivative, faceScoreSecondDerivative]
  apply Finset.sum_congr rfl
  intro i _
  rw [faceHessianWeights_eval_lift]
  simp only [faceHessianNormSecondDerivative, faceNormSecondDerivative]
  rw [faceHessianVectors_eval_lift, faceHessianVectorDerivative_eval_lift,
    faceHessianVectorSecondDerivative_eval_lift]

private theorem face_score_second_nonpos (tP zP tW zW dT dZ : ℝ)
    (htP : 0.2745 ≤ tP ∧ tP ≤ 0.2754)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (htW : 0.2745 ≤ tW ∧ tW ≤ 0.2754)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655) :
    faceScoreSecondDerivative cStar endpointLambda endpointMu
      (faceInput cStar endpointLambda endpointMu tP zP tW zW) dT dZ ≤ 0 := by
  rw [← faceHessianScoreSecondDerivative_eval_lift cStar endpointLambda endpointMu
    tP zP tW zW
    (fun i ↦ ‖(faceVectors i).eval
      (faceInput cStar endpointLambda endpointMu tP zP tW zW)‖)]
  change faceHessianScoreSecondDerivative
    (faceExtendedInput cStar endpointLambda endpointMu tP zP tW zW) dT dZ ≤ 0
  exact face_hessian_score_second_nonpos tP zP tW zW dT dZ htP hzP htW hzW

private lemma swap_path_mem (tP zP tW zW s : ℝ)
    (htP : 0.2745 ≤ tP ∧ tP ≤ 0.2754)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (htW : 0.2745 ≤ tW ∧ tW ≤ 0.2754)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655)
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    let midT := (tP + tW) / 2
    let midZ := (zP + zW) / 2
    let dT := (tP - tW) / 2
    let dZ := (zP - zW) / 2
    (0.2745 ≤ midT + s * dT ∧ midT + s * dT ≤ 0.2754) ∧
      (0.649 ≤ midZ + s * dZ ∧ midZ + s * dZ ≤ 0.655) ∧
      (0.2745 ≤ midT - s * dT ∧ midT - s * dT ≤ 0.2754) ∧
      (0.649 ≤ midZ - s * dZ ∧ midZ - s * dZ ≤ 0.655) := by
  dsimp
  rcases htP with ⟨htP0, htP1⟩
  rcases hzP with ⟨hzP0, hzP1⟩
  rcases htW with ⟨htW0, htW1⟩
  rcases hzW with ⟨hzW0, hzW1⟩
  rcases hs with ⟨hs0, hs1⟩
  constructor
  · constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hs0) (sub_nonneg.mpr htP0),
      mul_nonneg (sub_nonneg.mpr hs0) (sub_nonneg.mpr htW0),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr htP0),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr htW0)]
  constructor
  · constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hs0) (sub_nonneg.mpr hzP0),
      mul_nonneg (sub_nonneg.mpr hs0) (sub_nonneg.mpr hzW0),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hzP0),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hzW0)]
  constructor
  · constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hs0) (sub_nonneg.mpr htP0),
      mul_nonneg (sub_nonneg.mpr hs0) (sub_nonneg.mpr htW0),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr htP0),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr htW0)]
  · constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hs0) (sub_nonneg.mpr hzP0),
      mul_nonneg (sub_nonneg.mpr hs0) (sub_nonneg.mpr hzW0),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hzP0),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hzW0)]

private theorem face_score_concaveOn_swap_path (tP zP tW zW : ℝ)
    (htP : 0.2745 ≤ tP ∧ tP ≤ 0.2754)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (htW : 0.2745 ≤ tW ∧ tW ≤ 0.2754)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655) :
    let midT := (tP + tW) / 2
    let midZ := (zP + zW) / 2
    let dT := (tP - tW) / 2
    let dZ := (zP - zW) / 2
    ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1)
      (fun s ↦ faceScore cStar endpointLambda endpointMu
        (midT + s * dT) (midZ + s * dZ) (midT - s * dT) (midZ - s * dZ)) := by
  dsimp only
  let midT := (tP + tW) / 2
  let midZ := (zP + zW) / 2
  let dT := (tP - tW) / 2
  let dZ := (zP - zW) / 2
  let f := fun s ↦ faceScore cStar endpointLambda endpointMu
    (midT + s * dT) (midZ + s * dZ) (midT - s * dT) (midZ - s * dZ)
  let f' := fun s ↦ faceScoreFirstDerivative cStar endpointLambda endpointMu
    (faceInput cStar endpointLambda endpointMu
      (midT + s * dT) (midZ + s * dZ) (midT - s * dT) (midZ - s * dZ)) dT dZ
  let f'' := fun s ↦ faceScoreSecondDerivative cStar endpointLambda endpointMu
    (faceInput cStar endpointLambda endpointMu
      (midT + s * dT) (midZ + s * dZ) (midT - s * dT) (midZ - s * dZ)) dT dZ
  have hdata (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
      let tPs := midT + s * dT
      let zPs := midZ + s * dZ
      let tWs := midT - s * dT
      let zWs := midZ - s * dZ
      (0.2745 ≤ tPs ∧ tPs ≤ 0.2754) ∧
        (0.649 ≤ zPs ∧ zPs ≤ 0.655) ∧
        (0.2745 ≤ tWs ∧ tWs ≤ 0.2754) ∧
        (0.649 ≤ zWs ∧ zWs ≤ 0.655) := by
    simpa only [midT, midZ, dT, dZ] using swap_path_mem tP zP tW zW s
      htP hzP htW hzW hs
  have hfirst (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) : HasDerivAt f (f' s) s := by
    rcases hdata s hs with ⟨htPs, hzPs, htWs, hzWs⟩
    have hnorm := (face_hessian_certificate_sound
      (midT + s * dT) (midZ + s * dZ) (midT - s * dT) (midZ - s * dZ)
      htPs hzPs htWs hzWs).2.2
    exact hasDerivAt_faceScoreAlong cStar endpointLambda endpointMu midT midZ midT midZ
      dT dZ s hnorm
  have hsecond (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) : HasDerivAt f' (f'' s) s := by
    rcases hdata s hs with ⟨htPs, hzPs, htWs, hzWs⟩
    have hnorm := (face_hessian_certificate_sound
      (midT + s * dT) (midZ + s * dZ) (midT - s * dT) (midZ - s * dZ)
      htPs hzPs htWs hzWs).2.2
    exact hasDerivAt_faceScoreFirstDerivativeAlong cStar endpointLambda endpointMu
      midT midZ midT midZ dT dZ s hnorm
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (-1 : ℝ) 1)
  · intro s hs
    exact (hfirst s hs).continuousAt.continuousWithinAt
  · intro s hs
    exact (hfirst s (interior_subset hs)).hasDerivWithinAt
  · intro s hs
    exact (hsecond s (interior_subset hs)).hasDerivWithinAt
  · intro s hs
    rcases hdata s (interior_subset hs) with ⟨htPs, hzPs, htWs, hzWs⟩
    exact face_score_second_nonpos
      (midT + s * dT) (midZ + s * dZ) (midT - s * dT) (midZ - s * dZ)
      dT dZ htPs hzPs htWs hzWs

private lemma face_score_swap (c lambda mu tP zP tW zW : ℝ) :
    faceScore c lambda mu tP zP tW zW = faceScore c lambda mu tW zW tP zP := by
  exact weightedPairScore_swap !₂[1, 0] c lambda mu
    (chordChartFirst (-1) (topFaceLongitudinal tP) (topFaceHeight tP) zP)
    (chordChartSecond (-1) c (topFaceLongitudinal tP) (topFaceHeight tP) zP)
    (chordChartFirst (-1) (topFaceLongitudinal tW) (topFaceHeight tW) zW)
    (chordChartSecond (-1) c (topFaceLongitudinal tW) (topFaceHeight tW) zW)

private theorem face_score_le_diagonal (tP zP tW zW : ℝ)
    (htP : 0.2745 ≤ tP ∧ tP ≤ 0.2754)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (htW : 0.2745 ≤ tW ∧ tW ≤ 0.2754)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655) :
    faceScore cStar endpointLambda endpointMu tP zP tW zW ≤
      faceScore cStar endpointLambda endpointMu
        ((tP + tW) / 2) ((zP + zW) / 2) ((tP + tW) / 2) ((zP + zW) / 2) := by
  let midT := (tP + tW) / 2
  let midZ := (zP + zW) / 2
  let dT := (tP - tW) / 2
  let dZ := (zP - zW) / 2
  let f := fun s ↦ faceScore cStar endpointLambda endpointMu
    (midT + s * dT) (midZ + s * dZ) (midT - s * dT) (midZ - s * dZ)
  have hconcave := face_score_concaveOn_swap_path tP zP tW zW htP hzP htW hzW
  change ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f at hconcave
  rcases hconcave with ⟨_, hjensenRule⟩
  have hjensen := hjensenRule (x := (-1 : ℝ)) (y := (1 : ℝ))
    (by norm_num) (by norm_num) (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hminus : f (-1) = faceScore cStar endpointLambda endpointMu tW zW tP zP := by
    simp [f, midT, midZ, dT, dZ]
    congr 4 <;> ring
  have hplus : f 1 = faceScore cStar endpointLambda endpointMu tP zP tW zW := by
    simp [f, midT, midZ, dT, dZ]
    congr 4 <;> ring
  have hzero : f 0 = faceScore cStar endpointLambda endpointMu midT midZ midT midZ := by
    simp [f]
  rw [show (1 / 2 : ℝ) • (-1 : ℝ) + (1 / 2 : ℝ) • (1 : ℝ) = 0 by norm_num,
    hminus, hplus, hzero, ← face_score_swap] at hjensen
  change faceScore cStar endpointLambda endpointMu tP zP tW zW ≤
    faceScore cStar endpointLambda endpointMu midT midZ midT midZ
  norm_num only [one_div, smul_eq_mul, invOf_eq_inv] at hjensen
  linarith


/-- On the certified endpoint face box, the mixed score is at most its diagonal midpoint. -/
theorem weighted_pair_score_top_face_le_diagonal (tP zP tW zW : ℝ)
    (htP : 0.2745 ≤ tP ∧ tP ≤ 0.2754)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (htW : 0.2745 ≤ tW ∧ tW ≤ 0.2754)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655) :
    weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
      (chordChartFirst (-1) (topFaceLongitudinal tP) (topFaceHeight tP) zP)
      (chordChartSecond (-1) cStar (topFaceLongitudinal tP) (topFaceHeight tP) zP)
      (chordChartFirst (-1) (topFaceLongitudinal tW) (topFaceHeight tW) zW)
      (chordChartSecond (-1) cStar (topFaceLongitudinal tW) (topFaceHeight tW) zW) ≤
    weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
      (chordChartFirst (-1) (topFaceLongitudinal ((tP + tW) / 2))
        (topFaceHeight ((tP + tW) / 2)) ((zP + zW) / 2))
      (chordChartSecond (-1) cStar (topFaceLongitudinal ((tP + tW) / 2))
        (topFaceHeight ((tP + tW) / 2)) ((zP + zW) / 2))
      (chordChartFirst (-1) (topFaceLongitudinal ((tP + tW) / 2))
        (topFaceHeight ((tP + tW) / 2)) ((zP + zW) / 2))
      (chordChartSecond (-1) cStar (topFaceLongitudinal ((tP + tW) / 2))
        (topFaceHeight ((tP + tW) / 2)) ((zP + zW) / 2)) := by
  simpa only [faceScore] using face_score_le_diagonal tP zP tW zW htP hzP htW hzW

end Bescovitch.WeightedMixedEqualityLocal
