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
# Transverse monotonicity in the exceptional mixed chart

An exact interval certificate proves that the mixed score increases toward the upper face of
the lens near the equality configuration.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Bescovitch.WeightedMixedEqualityLocal

private def input (c lambda mu aP hP zP aW hW zW : ℝ) : Fin 9 → ℝ :=
  ![c, lambda, mu, aP, hP, zP, aW, hW, zW]

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

private lemma lensPair_eval (c a h z : Expression 9) (x : Fin 9 → ℝ) :
    (lensPair c a h z).1.eval x = chordChartFirst (-1) (a.eval x) (h.eval x) (z.eval x) ∧
      (lensPair c a h z).2.eval x =
        chordChartSecond (-1) (c.eval x) (a.eval x) (h.eval x) (z.eval x) := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [Vector.eval, RationalExpression.eval, chordChartFirst, chordChartSecond,
      stereographicDirection, quarterTurn] <;>
    ring

private lemma transverseVectors_eval (c lambda mu aP hP zP aW hW zW : ℝ)
    (i : Fin 10) :
    (transverseVectors i).eval (input c lambda mu aP hP zP aW hW zW) =
      geometricScoreVectors
        (chordChartFirst (-1) aP hP zP) (chordChartSecond (-1) c aP hP zP)
        (chordChartFirst (-1) aW hW zW) (chordChartSecond (-1) c aW hW zW) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [geometricScoreVectors, Vector.eval, RationalExpression.eval, input,
      chordChartFirst, chordChartSecond,
      stereographicDirection, quarterTurn] <;>
    ring

private lemma scoreWeights_eval (c lambda mu aP hP zP aW hW zW : ℝ)
    (i : Fin 10) :
    (scoreWeights (.var 0) (.var 1) (.var 2) i).eval
        (input c lambda mu aP hP zP aW hW zW) =
      geometricScoreWeights c lambda mu i := by
  fin_cases i <;>
    simp [geometricScoreWeights, input, RationalExpression.eval,
      weightedFirstPenalty, weightedSecondPenalty] <;>
    ring

private lemma weightedPairScore_eq_sum (c lambda mu aP hP zP aW hW zW : ℝ) :
    weightedPairScore !₂[1, 0] c lambda mu
        (chordChartFirst (-1) aP hP zP) (chordChartSecond (-1) c aP hP zP)
        (chordChartFirst (-1) aW hW zW) (chordChartSecond (-1) c aW hW zW) =
      (∑ i, (scoreWeights (.var 0) (.var 1) (.var 2) i).eval
          (input c lambda mu aP hP zP aW hW zW) *
        ‖(transverseVectors i).eval (input c lambda mu aP hP zP aW hW zW)‖) -
        weightedConstantTerm c lambda mu := by
  simp [Fin.sum_univ_succ, scoreWeights_eval, transverseVectors_eval,
    geometricScoreVectors, geometricScoreWeights, weightedPairScore]
  ring

private def transverseExtendedInput (c lambda mu aP hP zP aW hW zW : ℝ) :
    Fin 19 → ℝ :=
  fun i ↦ Fin.addCases (motive := fun _ ↦ ℝ)
    (input c lambda mu aP hP zP aW hW zW)
    (fun j ↦ ‖(transverseVectors j).eval
      (input c lambda mu aP hP zP aW hW zW)‖) i

private lemma transverseExtendedInput_castAdd (c lambda mu aP hP zP aW hW zW : ℝ)
    (i : Fin 9) :
    transverseExtendedInput c lambda mu aP hP zP aW hW zW (Fin.castAdd 10 i) =
      input c lambda mu aP hP zP aW hW zW i := by
  simp [transverseExtendedInput]

@[simp] private lemma transverseExtendedInput_0 (c lambda mu aP hP zP aW hW zW : ℝ) :
    transverseExtendedInput c lambda mu aP hP zP aW hW zW 0 = c := by
  simpa [input] using
    transverseExtendedInput_castAdd c lambda mu aP hP zP aW hW zW (0 : Fin 9)

@[simp] private lemma transverseExtendedInput_1 (c lambda mu aP hP zP aW hW zW : ℝ) :
    transverseExtendedInput c lambda mu aP hP zP aW hW zW 1 = lambda := by
  simpa [input] using
    transverseExtendedInput_castAdd c lambda mu aP hP zP aW hW zW (1 : Fin 9)

@[simp] private lemma transverseExtendedInput_2 (c lambda mu aP hP zP aW hW zW : ℝ) :
    transverseExtendedInput c lambda mu aP hP zP aW hW zW 2 = mu := by
  simpa [input] using
    transverseExtendedInput_castAdd c lambda mu aP hP zP aW hW zW (2 : Fin 9)

@[simp] private lemma transverseExtendedInput_3 (c lambda mu aP hP zP aW hW zW : ℝ) :
    transverseExtendedInput c lambda mu aP hP zP aW hW zW 3 = aP := by
  simpa [input] using
    transverseExtendedInput_castAdd c lambda mu aP hP zP aW hW zW (3 : Fin 9)

@[simp] private lemma transverseExtendedInput_4 (c lambda mu aP hP zP aW hW zW : ℝ) :
    transverseExtendedInput c lambda mu aP hP zP aW hW zW 4 = hP := by
  simpa [input] using
    transverseExtendedInput_castAdd c lambda mu aP hP zP aW hW zW (4 : Fin 9)

@[simp] private lemma transverseExtendedInput_5 (c lambda mu aP hP zP aW hW zW : ℝ) :
    transverseExtendedInput c lambda mu aP hP zP aW hW zW 5 = zP := by
  simpa [input] using
    transverseExtendedInput_castAdd c lambda mu aP hP zP aW hW zW (5 : Fin 9)

@[simp] private lemma transverseExtendedInput_6 (c lambda mu aP hP zP aW hW zW : ℝ) :
    transverseExtendedInput c lambda mu aP hP zP aW hW zW 6 = aW := by
  simpa [input] using
    transverseExtendedInput_castAdd c lambda mu aP hP zP aW hW zW (6 : Fin 9)

@[simp] private lemma transverseExtendedInput_7 (c lambda mu aP hP zP aW hW zW : ℝ) :
    transverseExtendedInput c lambda mu aP hP zP aW hW zW 7 = hW := by
  simpa [input] using
    transverseExtendedInput_castAdd c lambda mu aP hP zP aW hW zW (7 : Fin 9)

@[simp] private lemma transverseExtendedInput_8 (c lambda mu aP hP zP aW hW zW : ℝ) :
    transverseExtendedInput c lambda mu aP hP zP aW hW zW 8 = zW := by
  simpa [input] using
    transverseExtendedInput_castAdd c lambda mu aP hP zP aW hW zW (8 : Fin 9)

@[simp] private lemma transverseExtendedInput_natAdd
    (c lambda mu aP hP zP aW hW zW : ℝ) (i : Fin 10) :
    transverseExtendedInput c lambda mu aP hP zP aW hW zW (Fin.natAdd 9 i) =
      ‖(transverseVectors i).eval (input c lambda mu aP hP zP aW hW zW)‖ := by
  simp [transverseExtendedInput]

private lemma transverseDerivativeWeights_eval (c lambda mu aP hP zP aW hW zW : ℝ)
    (i : Fin 10) :
    (transverseDerivativeWeights i).eval
        (transverseExtendedInput c lambda mu aP hP zP aW hW zW) =
      geometricScoreWeights c lambda mu i := by
  fin_cases i <;>
    simp [geometricScoreWeights, RationalExpression.eval,
      weightedFirstPenalty, weightedSecondPenalty] <;>
    ring

set_option maxHeartbeats 2000000 in
private lemma transverseDerivativeVectors_eval (c lambda mu aP hP zP aW hW zW : ℝ)
    (i : Fin 10) :
    (transverseDerivativeVectors i).eval
        (transverseExtendedInput c lambda mu aP hP zP aW hW zW) =
      (transverseVectors i).eval (input c lambda mu aP hP zP aW hW zW) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [Vector.eval, RationalExpression.eval, input]

set_option maxHeartbeats 2000000 in
private lemma transverseDerivativeVectorDerivatives_eval
    (c lambda mu aP hP zP aW hW zW : ℝ) (i : Fin 10) :
    ((transverseDerivativeVectors i).partialDerivative 4).eval
        (transverseExtendedInput c lambda mu aP hP zP aW hW zW) =
      ((transverseVectors i).partialDerivative 4).eval
        (input c lambda mu aP hP zP aW hW zW) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [Vector.eval, Expression.partialDerivative, RationalExpression.eval, input]

set_option maxHeartbeats 2000000 in
private theorem hasDerivAt_transverseScore (c lambda mu aP hP zP aW hW zW : ℝ)
    (hnorm : ∀ i, 0 < ‖(transverseVectors i).eval
      (input c lambda mu aP hP zP aW hW zW)‖) :
    HasDerivAt
      (fun h ↦ weightedPairScore !₂[1, 0] c lambda mu
        (chordChartFirst (-1) aP h zP) (chordChartSecond (-1) c aP h zP)
        (chordChartFirst (-1) aW hW zW) (chordChartSecond (-1) c aW hW zW))
      (transverseDerivativeExpression.eval
        (transverseExtendedInput c lambda mu aP hP zP aW hW zW)) hP := by
  let x := input c lambda mu aP hP zP aW hW zW
  have hupdate (h : ℝ) : Function.update x 4 h = input c lambda mu aP h zP aW hW zW := by
    funext i
    fin_cases i <;> simp [x, input, Function.update]
  have hvector (i : Fin 10) :
      HasDerivAt (fun h ↦ (transverseVectors i).eval (input c lambda mu aP h zP aW hW zW))
        (((transverseVectors i).partialDerivative 4).eval x) hP := by
    have hregular := show Vector.RegularAt (transverseVectors i) (Function.update x 4 hP) by
      rw [hupdate]
      exact_mod_cast (show Vector.RegularAt (transverseVectors i)
        (input c lambda mu aP hP zP aW hW zW) from by
          have hzP : 1 + zP * zP ≠ 0 := by nlinarith [sq_nonneg zP]
          have hzW : 1 + zW * zW ≠ 0 := by nlinarith [sq_nonneg zW]
          fin_cases i <;>
            simp [Vector.RegularAt, Expression.RegularAt, RationalExpression.eval, input] <;>
            aesop)
    convert! Vector.hasDerivAt_update (transverseVectors i) 4 x hP hregular using 1
    · funext h
      rw [hupdate]
    · rw [hupdate]
  have hnormDeriv (i : Fin 10) :
      HasDerivAt
        (fun h ↦ ‖(transverseVectors i).eval (input c lambda mu aP h zP aW hW zW)‖)
        (⟪(transverseVectors i).eval x,
            ((transverseVectors i).partialDerivative 4).eval x⟫_ℝ /
          ‖(transverseVectors i).eval x‖) hP :=
    HasDerivAt.norm_of_ne_zero (hvector i) (norm_ne_zero_iff.mp (hnorm i).ne')
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    (hasDerivAt_const hP (geometricScoreWeights c lambda mu i)).mul (hnormDeriv i)
  have hsum' : HasDerivAt
      (fun h ↦ ∑ i, geometricScoreWeights c lambda mu i *
        ‖(transverseVectors i).eval (input c lambda mu aP h zP aW hW zW)‖)
      (∑ i, geometricScoreWeights c lambda mu i *
        (⟪(transverseVectors i).eval x,
            ((transverseVectors i).partialDerivative 4).eval x⟫_ℝ /
          ‖(transverseVectors i).eval x‖)) hP := by
    simpa using hsum
  have hscore := hsum'.sub_const (weightedConstantTerm c lambda mu)
  convert! hscore using 1
  · funext h
    rw [weightedPairScore_eq_sum]
    congr 2
    funext i
    rw [scoreWeights_eval]
  · dsimp only [x]
    simp only [transverseDerivativeExpression]
    rw [Expression.eval_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Expression.eval_div]
    have hnum :
        (RationalExpression.mul (transverseDerivativeWeights i)
          ((transverseDerivativeVectors i).dot
            ((transverseDerivativeVectors i).partialDerivative 4))).eval
            (transverseExtendedInput c lambda mu aP hP zP aW hW zW) =
          geometricScoreWeights c lambda mu i *
            ⟪(transverseVectors i).eval (input c lambda mu aP hP zP aW hW zW),
              ((transverseVectors i).partialDerivative 4).eval
                (input c lambda mu aP hP zP aW hW zW)⟫_ℝ := by
      rw [RationalExpression.eval, transverseDerivativeWeights_eval, Vector.eval_dot,
        transverseDerivativeVectors_eval, transverseDerivativeVectorDerivatives_eval]
    have hden :
        (RationalExpression.var (Fin.natAdd 9 i) : Expression 19).eval
            (transverseExtendedInput c lambda mu aP hP zP aW hW zW) =
          ‖(transverseVectors i).eval (input c lambda mu aP hP zP aW hW zW)‖ := by
      rw [RationalExpression.eval, transverseExtendedInput_natAdd]
    rw [hnum, hden]
    ring

private theorem transverse_input_mem (aP hP zP aW hW zW : ℝ)
    (haP : 0.85902 ≤ aP ∧ aP ≤ 0.85984)
    (hhP : -0.513 ≤ hP ∧ hP ≤ 0.513)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (haW : 0.85902 ≤ aW ∧ aW ≤ 0.85984)
    (hhW : -0.513 ≤ hW ∧ hW ≤ 0.513)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655) :
    ∀ i, (exactTransverseRootBox i).Contains
      (input cStar endpointLambda endpointMu aP hP zP aW hW zW i) := by
  intro i
  fin_cases i
  · have hc : (13866128436518096 : ℝ) / 10 ^ 16 ≤ cStar ∧
        cStar ≤ 13866128436518100 / 10 ^ 16 :=
      ⟨cStar_mem_isolation_box.1.le, cStar_mem_isolation_box.2.le⟩
    norm_num [exactTransverseRootBox, RationalInterval.Contains, input] at hc ⊢
    exact hc
  · have h := endpointLambda_tight_bounds
    norm_num [exactTransverseRootBox, RationalInterval.Contains, input] at h ⊢
    exact h
  · have h := endpointMu_tight_bounds
    norm_num [exactTransverseRootBox, RationalInterval.Contains, input] at h ⊢
    exact h
  · norm_num [exactTransverseRootBox, RationalInterval.Contains, input] at haP ⊢
    exact haP
  · norm_num [exactTransverseRootBox, RationalInterval.Contains, input] at hhP ⊢
    exact hhP
  · norm_num [exactTransverseRootBox, RationalInterval.Contains, input] at hzP ⊢
    exact hzP
  · norm_num [exactTransverseRootBox, RationalInterval.Contains, input] at haW ⊢
    exact haW
  · norm_num [exactTransverseRootBox, RationalInterval.Contains, input] at hhW ⊢
    exact hhW
  · norm_num [exactTransverseRootBox, RationalInterval.Contains, input] at hzW ⊢
    exact hzW

private theorem transverse_certificate_sound (aP hP zP aW hW zW : ℝ)
    (haP : 0.85902 ≤ aP ∧ aP ≤ 0.85984)
    (hhP : -0.513 ≤ hP ∧ hP ≤ 0.513)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (haW : 0.85902 ≤ aW ∧ aW ≤ 0.85984)
    (hhW : -0.513 ≤ hW ∧ hW ≤ 0.513)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655) :
    0 < transverseDerivativeExpression.eval
        (transverseExtendedInput cStar endpointLambda endpointMu aP hP zP aW hW zW) ∧
      ∀ i, 0 < ‖(transverseVectors i).eval
        (input cStar endpointLambda endpointMu aP hP zP aW hW zW)‖ :=
  exact_local_tree_sound transverseVectors transverseDerivativeExpression
    transverseCertificateTree exactTransverseRootBox transverse_certificate_tree_exact
    (input cStar endpointLambda endpointMu aP hP zP aW hW zW)
    (transverse_input_mem aP hP zP aW hW zW haP hhP hzP haW hhW hzW)

/-- On the certified endpoint box, the mixed score strictly increases with the first
transverse coordinate. -/
theorem transverse_score_strict_mono_on (aP zP aW hW zW : ℝ)
    (haP : 0.85902 ≤ aP ∧ aP ≤ 0.85984)
    (hzP : 0.649 ≤ zP ∧ zP ≤ 0.655)
    (haW : 0.85902 ≤ aW ∧ aW ≤ 0.85984)
    (hhW : -0.513 ≤ hW ∧ hW ≤ 0.513)
    (hzW : 0.649 ≤ zW ∧ zW ≤ 0.655) :
    StrictMonoOn
      (fun h ↦ weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
        (chordChartFirst (-1) aP h zP) (chordChartSecond (-1) cStar aP h zP)
        (chordChartFirst (-1) aW hW zW) (chordChartSecond (-1) cStar aW hW zW))
      (Set.Icc (-0.513) 0.513) := by
  let f := fun h ↦ weightedPairScore !₂[1, 0] cStar endpointLambda endpointMu
    (chordChartFirst (-1) aP h zP) (chordChartSecond (-1) cStar aP h zP)
    (chordChartFirst (-1) aW hW zW) (chordChartSecond (-1) cStar aW hW zW)
  let f' := fun h ↦ transverseDerivativeExpression.eval
    (transverseExtendedInput cStar endpointLambda endpointMu aP h zP aW hW zW)
  have hderiv (h : ℝ) (hh : h ∈ Set.Icc (-0.513) 0.513) :
      HasDerivAt f (f' h) h ∧ 0 < f' h := by
    have hcertificate := transverse_certificate_sound aP h zP aW hW zW
      haP hh hzP haW hhW hzW
    exact ⟨hasDerivAt_transverseScore cStar endpointLambda endpointMu
      aP h zP aW hW zW hcertificate.2, hcertificate.1⟩
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (-0.513) 0.513)
  · intro h hh
    exact (hderiv h hh).1.continuousAt.continuousWithinAt
  · intro h hh
    have hh' : h ∈ Set.Icc (-0.513) 0.513 := interior_subset hh
    exact (hderiv h hh').1.hasDerivWithinAt
  · intro h hh
    have hh' : h ∈ Set.Icc (-0.513) 0.513 := interior_subset hh
    exact (hderiv h hh').2

end Bescovitch.WeightedMixedEqualityLocal
