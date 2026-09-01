/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.DyadicIntervalPolynomial
public import Bescovitch.Certificates.IntervalBernstein

/-!
# Bernstein certificates over fixed-precision dyadic intervals

This module performs the fixed `(12, 12, 4)` Bernstein conversion and adaptive dyadic
subdivision with outward-rounded dyadic intervals.  Its soundness theorem supplies the exact
rational interval certificate used by the analytic layer.
-/

@[expose] public section

namespace Bescovitch

variable {precision : ℕ}

namespace DyadicInterval

/-- Add a finite family of dyadic intervals in increasing `Fin` order. -/
def finSum (precision : ℕ) : (N : ℕ) → (Fin N → DyadicInterval precision) →
    DyadicInterval precision
  | 0, _ => ofRat precision 0
  | n + 1, f => (f 0).add (finSum precision n fun i ↦ f i.succ)

/-- Dyadic finite sums preserve widening of exact interval sums. -/
theorem finSum_widens (precision : ℕ) {N : ℕ}
    {D : Fin N → DyadicInterval precision} {I : Fin N → RationalInterval}
    (h : ∀ i, (D i).Widens (I i)) :
    (finSum precision N D).Widens (RationalInterval.finSum N I) := by
  induction N with
  | zero => exact ofInterval_widens precision (.singleton 0)
  | succ N ih => exact add_widens (h 0) (ih fun i ↦ h i.succ)

end DyadicInterval

/-- Convert one dyadic interval power vector to the Bernstein basis. -/
def dyadicIntervalPowerToBernstein (precision degree : ℕ)
    (a : Fin (degree + 1) → DyadicInterval precision)
    (i : Fin (degree + 1)) : DyadicInterval precision :=
  DyadicInterval.finSum precision (degree + 1) fun j ↦ if (j : ℕ) ≤ i then
    (a j).mul (DyadicInterval.ofRat precision
      (Nat.choose (i : ℕ) (j : ℕ) / Nat.choose degree (j : ℕ)))
  else DyadicInterval.ofRat precision 0

/-- Dyadic power-to-Bernstein conversion widens exact interval conversion. -/
theorem dyadicIntervalPowerToBernstein_widens (precision degree : ℕ)
    {D : Fin (degree + 1) → DyadicInterval precision}
    {I : Fin (degree + 1) → RationalInterval}
    (h : ∀ i, (D i).Widens (I i)) (i : Fin (degree + 1)) :
    (dyadicIntervalPowerToBernstein precision degree D i).Widens
      (intervalPowerToBernstein degree I i) := by
  apply DyadicInterval.finSum_widens
  intro j
  split_ifs with hj
  · exact DyadicInterval.mul_widens (h j)
      (DyadicInterval.ofInterval_widens precision (.singleton _))
  · exact DyadicInterval.ofInterval_widens precision (.singleton 0)

/-- The fixed dyadic interval tensor used by weighted-self certificates. -/
abbrev DyadicIntervalTensor (precision : ℕ) :=
  Fin 13 → Fin 13 → Fin 5 → DyadicInterval precision

private abbrev ExactIntervalTensor :=
  Fin 13 → Fin 13 → Fin 5 → RationalInterval

private def exactIntervalPowerTensor (p : IntervalTrivariate) : ExactIntervalTensor :=
  fun i j k ↦ p.coefficient i j k

private def exactIntervalBernsteinFirst (a : ExactIntervalTensor) : ExactIntervalTensor :=
  fun i j k ↦ intervalPowerToBernstein 12 (fun i' ↦ a i' j k) i

private def exactIntervalBernsteinSecond (a : ExactIntervalTensor) : ExactIntervalTensor :=
  fun i j k ↦ intervalPowerToBernstein 12 (fun j' ↦ a i j' k) j

private def exactIntervalBernsteinThird (a : ExactIntervalTensor) : ExactIntervalTensor :=
  fun i j k ↦ intervalPowerToBernstein 4 (fun k' ↦ a i j k') k

private theorem exactIntervalBernstein_passes (p : IntervalTrivariate) :
    exactIntervalBernsteinThird
        (exactIntervalBernsteinSecond
          (exactIntervalBernsteinFirst (exactIntervalPowerTensor p))) =
      p.bernsteinCoefficients :=
  rfl

namespace DyadicIntervalTensor

/-- Coefficientwise widening of an exact rational interval tensor. -/
def Widens (D : DyadicIntervalTensor precision)
    (I : Fin 13 → Fin 13 → Fin 5 → RationalInterval) : Prop :=
  ∀ i j k, (D i j k).Widens (I i j k)

end DyadicIntervalTensor

/-- Read padded dyadic polynomial coefficients as a fixed tensor. -/
def DyadicIntervalTrivariate.powerTensor
    (p : DyadicIntervalTrivariate precision) : DyadicIntervalTensor precision :=
  fun i j k ↦ p.coefficient i j k

/-- Widening polynomials have widening padded power tensors. -/
private theorem DyadicIntervalTrivariate.powerTensor_widens
    {P : DyadicIntervalTrivariate precision} {p : IntervalTrivariate}
    (h : P.Widens p) : P.powerTensor.Widens (exactIntervalPowerTensor p) :=
  fun i j k ↦ DyadicIntervalTrivariate.coefficient_widens h i j k

/-- Change the first tensor coordinate to the Bernstein basis. -/
def dyadicIntervalTensorBernsteinFirst
    (a : DyadicIntervalTensor precision) : DyadicIntervalTensor precision :=
  fun i j k ↦ dyadicIntervalPowerToBernstein precision 12 (fun i' ↦ a i' j k) i

/-- Change the second tensor coordinate to the Bernstein basis. -/
def dyadicIntervalTensorBernsteinSecond
    (a : DyadicIntervalTensor precision) : DyadicIntervalTensor precision :=
  fun i j k ↦ dyadicIntervalPowerToBernstein precision 12 (fun j' ↦ a i j' k) j

/-- Change the third tensor coordinate to the Bernstein basis. -/
def dyadicIntervalTensorBernsteinThird
    (a : DyadicIntervalTensor precision) : DyadicIntervalTensor precision :=
  fun i j k ↦ dyadicIntervalPowerToBernstein precision 4 (fun k' ↦ a i j k') k

/-- The first dyadic Bernstein pass preserves tensor widening. -/
private theorem dyadicIntervalTensorBernsteinFirst_widens
    {D : DyadicIntervalTensor precision} {I : ExactIntervalTensor} (h : D.Widens I) :
    (dyadicIntervalTensorBernsteinFirst D).Widens (exactIntervalBernsteinFirst I) :=
  fun i j k ↦ dyadicIntervalPowerToBernstein_widens precision 12
    (fun i' ↦ h i' j k) i

/-- The second dyadic Bernstein pass preserves tensor widening. -/
private theorem dyadicIntervalTensorBernsteinSecond_widens
    {D : DyadicIntervalTensor precision} {I : ExactIntervalTensor} (h : D.Widens I) :
    (dyadicIntervalTensorBernsteinSecond D).Widens (exactIntervalBernsteinSecond I) :=
  fun i j k ↦ dyadicIntervalPowerToBernstein_widens precision 12
    (fun j' ↦ h i j' k) j

/-- The third dyadic Bernstein pass preserves tensor widening. -/
private theorem dyadicIntervalTensorBernsteinThird_widens
    {D : DyadicIntervalTensor precision} {I : ExactIntervalTensor} (h : D.Widens I) :
    (dyadicIntervalTensorBernsteinThird D).Widens (exactIntervalBernsteinThird I) :=
  fun i j k ↦ dyadicIntervalPowerToBernstein_widens precision 4
    (fun k' ↦ h i j k') k

/-- Left-half dyadic de Casteljau coefficients in degree twelve. -/
def dyadicBernsteinLeftTwelve (a : Fin 13 → DyadicInterval precision)
    (i : Fin 13) : DyadicInterval precision :=
  DyadicInterval.finSum precision 13 fun j ↦ if (j : ℕ) ≤ i then
    (a j).mul (DyadicInterval.ofRat precision
      (Nat.choose (i : ℕ) (j : ℕ) / 2 ^ (i : ℕ)))
  else DyadicInterval.ofRat precision 0

/-- Right-half dyadic de Casteljau coefficients in degree twelve. -/
def dyadicBernsteinRightTwelve (a : Fin 13 → DyadicInterval precision)
    (i : Fin 13) : DyadicInterval precision :=
  DyadicInterval.finSum precision 13 fun j ↦ if h : (j : ℕ) ≤ 12 - (i : ℕ) then
    (a ⟨(i : ℕ) + j, by omega⟩).mul (DyadicInterval.ofRat precision
      (Nat.choose (12 - (i : ℕ)) (j : ℕ) / 2 ^ (12 - (i : ℕ))))
  else DyadicInterval.ofRat precision 0

/-- Left-half dyadic de Casteljau coefficients in degree four. -/
def dyadicBernsteinLeftFour (a : Fin 5 → DyadicInterval precision)
    (i : Fin 5) : DyadicInterval precision :=
  DyadicInterval.finSum precision 5 fun j ↦ if (j : ℕ) ≤ i then
    (a j).mul (DyadicInterval.ofRat precision
      (Nat.choose (i : ℕ) (j : ℕ) / 2 ^ (i : ℕ)))
  else DyadicInterval.ofRat precision 0

/-- Right-half dyadic de Casteljau coefficients in degree four. -/
def dyadicBernsteinRightFour (a : Fin 5 → DyadicInterval precision)
    (i : Fin 5) : DyadicInterval precision :=
  DyadicInterval.finSum precision 5 fun j ↦ if h : (j : ℕ) ≤ 4 - (i : ℕ) then
    (a ⟨(i : ℕ) + j, by omega⟩).mul (DyadicInterval.ofRat precision
      (Nat.choose (4 - (i : ℕ)) (j : ℕ) / 2 ^ (4 - (i : ℕ))))
  else DyadicInterval.ofRat precision 0

private theorem dyadicBernsteinLeftTwelve_widens
    {D : Fin 13 → DyadicInterval precision} {I : Fin 13 → RationalInterval}
    (h : ∀ i, (D i).Widens (I i)) (i : Fin 13) :
    (dyadicBernsteinLeftTwelve D i).Widens (intervalBernsteinLeftTwelve I i) := by
  apply DyadicInterval.finSum_widens
  intro j
  split_ifs with hj
  · exact DyadicInterval.mul_widens (h j)
      (DyadicInterval.ofInterval_widens precision (.singleton _))
  · exact DyadicInterval.ofInterval_widens precision (.singleton 0)

private theorem dyadicBernsteinRightTwelve_widens
    {D : Fin 13 → DyadicInterval precision} {I : Fin 13 → RationalInterval}
    (h : ∀ i, (D i).Widens (I i)) (i : Fin 13) :
    (dyadicBernsteinRightTwelve D i).Widens (intervalBernsteinRightTwelve I i) := by
  apply DyadicInterval.finSum_widens
  intro j
  split_ifs with hj
  · exact DyadicInterval.mul_widens (h ⟨(i : ℕ) + j, by omega⟩)
      (DyadicInterval.ofInterval_widens precision (.singleton _))
  · exact DyadicInterval.ofInterval_widens precision (.singleton 0)

private theorem dyadicBernsteinLeftFour_widens
    {D : Fin 5 → DyadicInterval precision} {I : Fin 5 → RationalInterval}
    (h : ∀ i, (D i).Widens (I i)) (i : Fin 5) :
    (dyadicBernsteinLeftFour D i).Widens (intervalBernsteinLeftFour I i) := by
  apply DyadicInterval.finSum_widens
  intro j
  split_ifs with hj
  · exact DyadicInterval.mul_widens (h j)
      (DyadicInterval.ofInterval_widens precision (.singleton _))
  · exact DyadicInterval.ofInterval_widens precision (.singleton 0)

private theorem dyadicBernsteinRightFour_widens
    {D : Fin 5 → DyadicInterval precision} {I : Fin 5 → RationalInterval}
    (h : ∀ i, (D i).Widens (I i)) (i : Fin 5) :
    (dyadicBernsteinRightFour D i).Widens (intervalBernsteinRightFour I i) := by
  apply DyadicInterval.finSum_widens
  intro j
  split_ifs with hj
  · exact DyadicInterval.mul_widens (h ⟨(i : ℕ) + j, by omega⟩)
      (DyadicInterval.ofInterval_widens precision (.singleton _))
  · exact DyadicInterval.ofInterval_widens precision (.singleton 0)

/-- Restrict a dyadic tensor to the left half of its first coordinate. -/
def dyadicSplitFirstLeft (a : DyadicIntervalTensor precision) :
    DyadicIntervalTensor precision :=
  fun i j k ↦ dyadicBernsteinLeftTwelve (fun h ↦ a h j k) i

/-- Restrict a dyadic tensor to the right half of its first coordinate. -/
def dyadicSplitFirstRight (a : DyadicIntervalTensor precision) :
    DyadicIntervalTensor precision :=
  fun i j k ↦ dyadicBernsteinRightTwelve (fun h ↦ a h j k) i

/-- Restrict a dyadic tensor to the left half of its second coordinate. -/
def dyadicSplitSecondLeft (a : DyadicIntervalTensor precision) :
    DyadicIntervalTensor precision :=
  fun i j k ↦ dyadicBernsteinLeftTwelve (fun h ↦ a i h k) j

/-- Restrict a dyadic tensor to the right half of its second coordinate. -/
def dyadicSplitSecondRight (a : DyadicIntervalTensor precision) :
    DyadicIntervalTensor precision :=
  fun i j k ↦ dyadicBernsteinRightTwelve (fun h ↦ a i h k) j

/-- Restrict a dyadic tensor to the left half of its third coordinate. -/
def dyadicSplitThirdLeft (a : DyadicIntervalTensor precision) :
    DyadicIntervalTensor precision :=
  fun i j k ↦ dyadicBernsteinLeftFour (fun h ↦ a i j h) k

/-- Restrict a dyadic tensor to the right half of its third coordinate. -/
def dyadicSplitThirdRight (a : DyadicIntervalTensor precision) :
    DyadicIntervalTensor precision :=
  fun i j k ↦ dyadicBernsteinRightFour (fun h ↦ a i j h) k

private theorem dyadicSplitFirstLeft_widens
    {D : DyadicIntervalTensor precision} {I : ExactIntervalTensor} (h : D.Widens I) :
    (dyadicSplitFirstLeft D).Widens (intervalSplitFirstLeft I) :=
  fun i j k ↦ dyadicBernsteinLeftTwelve_widens (fun i' ↦ h i' j k) i

private theorem dyadicSplitFirstRight_widens
    {D : DyadicIntervalTensor precision} {I : ExactIntervalTensor} (h : D.Widens I) :
    (dyadicSplitFirstRight D).Widens (intervalSplitFirstRight I) :=
  fun i j k ↦ dyadicBernsteinRightTwelve_widens (fun i' ↦ h i' j k) i

private theorem dyadicSplitSecondLeft_widens
    {D : DyadicIntervalTensor precision} {I : ExactIntervalTensor} (h : D.Widens I) :
    (dyadicSplitSecondLeft D).Widens (intervalSplitSecondLeft I) :=
  fun i j k ↦ dyadicBernsteinLeftTwelve_widens (fun j' ↦ h i j' k) j

private theorem dyadicSplitSecondRight_widens
    {D : DyadicIntervalTensor precision} {I : ExactIntervalTensor} (h : D.Widens I) :
    (dyadicSplitSecondRight D).Widens (intervalSplitSecondRight I) :=
  fun i j k ↦ dyadicBernsteinRightTwelve_widens (fun j' ↦ h i j' k) j

private theorem dyadicSplitThirdLeft_widens
    {D : DyadicIntervalTensor precision} {I : ExactIntervalTensor} (h : D.Widens I) :
    (dyadicSplitThirdLeft D).Widens (intervalSplitThirdLeft I) :=
  fun i j k ↦ dyadicBernsteinLeftFour_widens (fun k' ↦ h i j k') k

private theorem dyadicSplitThirdRight_widens
    {D : DyadicIntervalTensor precision} {I : ExactIntervalTensor} (h : D.Widens I) :
    (dyadicSplitThirdRight D).Widens (intervalSplitThirdRight I) :=
  fun i j k ↦ dyadicBernsteinRightFour_widens (fun k' ↦ h i j k') k

/-- Check nonnegative lower endpoints after prescribed dyadic subdivision. -/
def dyadicIntervalTensorSubdivisionCertifiesNonnegative :
    TensorSubdivision → DyadicIntervalTensor precision → Bool
  | .leaf, a => decide (∀ i j k, (a i j k).lowerNonnegative = true)
  | .splitFirst left right, a =>
      dyadicIntervalTensorSubdivisionCertifiesNonnegative left
          (dyadicSplitFirstLeft a) &&
        dyadicIntervalTensorSubdivisionCertifiesNonnegative right
          (dyadicSplitFirstRight a)
  | .splitSecond left right, a =>
      dyadicIntervalTensorSubdivisionCertifiesNonnegative left
          (dyadicSplitSecondLeft a) &&
        dyadicIntervalTensorSubdivisionCertifiesNonnegative right
          (dyadicSplitSecondRight a)
  | .splitThird left right, a =>
      dyadicIntervalTensorSubdivisionCertifiesNonnegative left
          (dyadicSplitThirdLeft a) &&
        dyadicIntervalTensorSubdivisionCertifiesNonnegative right
          (dyadicSplitThirdRight a)

/-- A successful dyadic tree check supplies the exact interval tree certificate. -/
theorem dyadicIntervalTensorSubdivision_sound (tree : TensorSubdivision)
    {D : DyadicIntervalTensor precision}
    {I : Fin 13 → Fin 13 → Fin 5 → RationalInterval}
    (hwide : D.Widens I)
    (hcheck : dyadicIntervalTensorSubdivisionCertifiesNonnegative tree D = true) :
    intervalTensorSubdivisionCertifiesNonnegative tree I = true := by
  induction tree generalizing D I with
  | leaf =>
      simp only [dyadicIntervalTensorSubdivisionCertifiesNonnegative,
        decide_eq_true_eq] at hcheck
      simp only [intervalTensorSubdivisionCertifiesNonnegative,
        intervalTensorCoefficientsNonnegative, decide_eq_true_eq]
      intro i j k
      exact DyadicInterval.nonnegative_of_lowerNonnegative (hcheck i j k) (hwide i j k).1
  | splitFirst left right ihLeft ihRight =>
      simp only [dyadicIntervalTensorSubdivisionCertifiesNonnegative,
        Bool.and_eq_true] at hcheck
      simp only [intervalTensorSubdivisionCertifiesNonnegative, Bool.and_eq_true]
      exact ⟨ihLeft (dyadicSplitFirstLeft_widens hwide) hcheck.1,
        ihRight (dyadicSplitFirstRight_widens hwide) hcheck.2⟩
  | splitSecond left right ihLeft ihRight =>
      simp only [dyadicIntervalTensorSubdivisionCertifiesNonnegative,
        Bool.and_eq_true] at hcheck
      simp only [intervalTensorSubdivisionCertifiesNonnegative, Bool.and_eq_true]
      exact ⟨ihLeft (dyadicSplitSecondLeft_widens hwide) hcheck.1,
        ihRight (dyadicSplitSecondRight_widens hwide) hcheck.2⟩
  | splitThird left right ihLeft ihRight =>
      simp only [dyadicIntervalTensorSubdivisionCertifiesNonnegative,
        Bool.and_eq_true] at hcheck
      simp only [intervalTensorSubdivisionCertifiesNonnegative, Bool.and_eq_true]
      exact ⟨ihLeft (dyadicSplitThirdLeft_widens hwide) hcheck.1,
        ihRight (dyadicSplitThirdRight_widens hwide) hcheck.2⟩

/-- A direct dyadic Bernstein computation certifies an exact interval polynomial. -/
theorem dyadicIntervalPolynomialCertificate_sound
    {D : DyadicIntervalTrivariate precision} {I : IntervalTrivariate}
    (hwide : D.Widens I) (tree : TensorSubdivision)
    (hcheck : dyadicIntervalTensorSubdivisionCertifiesNonnegative tree
      (dyadicIntervalTensorBernsteinThird
        (dyadicIntervalTensorBernsteinSecond
          (dyadicIntervalTensorBernsteinFirst D.powerTensor))) = true) :
    intervalTensorSubdivisionCertifiesNonnegative tree I.bernsteinCoefficients = true := by
  have hwide' := dyadicIntervalTensorBernsteinThird_widens
    (dyadicIntervalTensorBernsteinSecond_widens
      (dyadicIntervalTensorBernsteinFirst_widens
        (DyadicIntervalTrivariate.powerTensor_widens hwide)))
  rw [exactIntervalBernstein_passes] at hwide'
  exact dyadicIntervalTensorSubdivision_sound tree hwide' hcheck

end Bescovitch
