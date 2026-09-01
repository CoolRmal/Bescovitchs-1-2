/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfExceptionalCertificate

/-!
# The hybrid certificate for the exceptional weighted-self bin

The discriminant certificate on the radius bin `[7 / 10, 4 / 5]` has one tight leaf.
Ordinary Bernstein coefficients settle every other leaf, while the tight leaf is handled by the
endpoint Hessian argument. This file combines those two mechanisms without leaving a geometric
case as an assumption.
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace Bescovitch

open Set

/-- An adaptive tensor subdivision with ordinary and analytic terminal leaves. -/
inductive HybridTensorSubdivision where
  | certified
  | analytic
  | splitFirst (left right : HybridTensorSubdivision)
  | splitSecond (left right : HybridTensorSubdivision)
  | splitThird (left right : HybridTensorSubdivision)

namespace HybridTensorSubdivision

/-- A point follows the route to an analytic leaf of a hybrid subdivision. -/
def ExceptionalAt : HybridTensorSubdivision → I → I → I → Prop
  | .certified, _, _, _ => False
  | .analytic, _, _, _ => True
  | .splitFirst left right, x, y, z =>
      (∃ u, x = unitIntervalLeftHalf u ∧ left.ExceptionalAt u y z) ∨
        ∃ u, x = unitIntervalRightHalf u ∧ right.ExceptionalAt u y z
  | .splitSecond left right, x, y, z =>
      (∃ u, y = unitIntervalLeftHalf u ∧ left.ExceptionalAt x u z) ∨
        ∃ u, y = unitIntervalRightHalf u ∧ right.ExceptionalAt x u z
  | .splitThird left right, x, y, z =>
      (∃ u, z = unitIntervalLeftHalf u ∧ left.ExceptionalAt x y u) ∨
        ∃ u, z = unitIntervalRightHalf u ∧ right.ExceptionalAt x y u

end HybridTensorSubdivision

/-- Check every ordinary leaf of a hybrid interval Bernstein subdivision. -/
def hybridIntervalTensorSubdivisionCertifiesNonnegative :
    HybridTensorSubdivision → (Fin 13 → Fin 13 → Fin 5 → RationalInterval) → Bool
  | .certified, coefficients => intervalTensorCoefficientsNonnegative coefficients
  | .analytic, _ => true
  | .splitFirst left right, coefficients =>
      hybridIntervalTensorSubdivisionCertifiesNonnegative left
          (intervalSplitFirstLeft coefficients) &&
        hybridIntervalTensorSubdivisionCertifiesNonnegative right
          (intervalSplitFirstRight coefficients)
  | .splitSecond left right, coefficients =>
      hybridIntervalTensorSubdivisionCertifiesNonnegative left
          (intervalSplitSecondLeft coefficients) &&
        hybridIntervalTensorSubdivisionCertifiesNonnegative right
          (intervalSplitSecondRight coefficients)
  | .splitThird left right, coefficients =>
      hybridIntervalTensorSubdivisionCertifiesNonnegative left
          (intervalSplitThirdLeft coefficients) &&
        hybridIntervalTensorSubdivisionCertifiesNonnegative right
          (intervalSplitThirdRight coefficients)

private theorem tensorBernstein_nonneg_or_exceptional_of_hybrid_certificate
    (tree : HybridTensorSubdivision)
    (intervals : Fin 13 → Fin 13 → Fin 5 → RationalInterval)
    (values : Fin 13 → Fin 13 → Fin 5 → ℝ)
    (hcontains : ∀ i j k, (intervals i j k).Contains (values i j k))
    (hcertificate : hybridIntervalTensorSubdivisionCertifiesNonnegative tree intervals = true)
    (x y z : I) :
    0 ≤ tensorBernstein values x y z ∨ tree.ExceptionalAt x y z := by
  induction tree generalizing intervals values x y z with
  | certified =>
      left
      apply tensorBernstein_nonneg
      intro i j k
      have hlower : 0 ≤ (intervals i j k).lower := by
        exact of_decide_eq_true hcertificate i j k
      exact (show (0 : ℝ) ≤ (intervals i j k).lower by exact_mod_cast hlower).trans
        (hcontains i j k).1
  | analytic => exact Or.inr trivial
  | splitFirst left right ihLeft ihRight =>
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases exists_unitInterval_half_chart x with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · rw [tensorBernstein_splitFirstLeft]
        rcases ihLeft (intervalSplitFirstLeft intervals) (splitFirstLeft values)
          (intervalSplitFirstLeft_contains hcontains) hparts.1 u y z with h | h
        · exact Or.inl h
        · exact Or.inr <| Or.inl ⟨u, rfl, h⟩
      · rw [tensorBernstein_splitFirstRight]
        rcases ihRight (intervalSplitFirstRight intervals) (splitFirstRight values)
          (intervalSplitFirstRight_contains hcontains) hparts.2 u y z with h | h
        · exact Or.inl h
        · exact Or.inr <| Or.inr ⟨u, rfl, h⟩
  | splitSecond left right ihLeft ihRight =>
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases exists_unitInterval_half_chart y with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · rw [tensorBernstein_splitSecondLeft]
        rcases ihLeft (intervalSplitSecondLeft intervals) (splitSecondLeft values)
          (intervalSplitSecondLeft_contains hcontains) hparts.1 x u z with h | h
        · exact Or.inl h
        · exact Or.inr <| Or.inl ⟨u, rfl, h⟩
      · rw [tensorBernstein_splitSecondRight]
        rcases ihRight (intervalSplitSecondRight intervals) (splitSecondRight values)
          (intervalSplitSecondRight_contains hcontains) hparts.2 x u z with h | h
        · exact Or.inl h
        · exact Or.inr <| Or.inr ⟨u, rfl, h⟩
  | splitThird left right ihLeft ihRight =>
      have hparts := Bool.and_eq_true_iff.mp hcertificate
      rcases exists_unitInterval_half_chart z with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · rw [tensorBernstein_splitThirdLeft]
        rcases ihLeft (intervalSplitThirdLeft intervals) (splitThirdLeft values)
          (intervalSplitThirdLeft_contains hcontains) hparts.1 x y u with h | h
        · exact Or.inl h
        · exact Or.inr <| Or.inl ⟨u, rfl, h⟩
      · rw [tensorBernstein_splitThirdRight]
        rcases ihRight (intervalSplitThirdRight intervals) (splitThirdRight values)
          (intervalSplitThirdRight_contains hcontains) hparts.2 x y u with h | h
        · exact Or.inl h
        · exact Or.inr <| Or.inr ⟨u, rfl, h⟩

/-- Ordinary interval leaves and an analytic exceptional case cover a fitted polynomial. -/
theorem RadicalTrivariate.nonneg_of_hybrid_interval_bernstein_certificate {n : ℕ}
    (p : RadicalTrivariate n) (hfits : p.Fits 12 12 4)
    (P : IntervalTrivariate) (input : Fin n → ℝ) (hcontains : P.Contains input p)
    (tree : HybridTensorSubdivision)
    (hcertificate : hybridIntervalTensorSubdivisionCertifiesNonnegative tree
      P.bernsteinCoefficients = true)
    (hexceptional : ∀ x y z : I, tree.ExceptionalAt x y z → 0 ≤ p.eval input x y z)
    (x y z : I) : 0 ≤ p.eval input x y z := by
  rw [p.eval_eq_tensorBernstein hfits]
  rcases tensorBernstein_nonneg_or_exceptional_of_hybrid_certificate tree
    P.bernsteinCoefficients (fun i j k ↦ (p.bernsteinCoefficients i j k).eval input)
    (fun i j k ↦ P.bernsteinCoefficients_contains hcontains i j k)
    hcertificate x y z with h | h
  · exact h
  · rw [← p.eval_eq_tensorBernstein hfits]
    exact hexceptional x y z h

private inductive HybridHalfStep where
  | firstLeft
  | firstRight
  | secondLeft
  | secondRight
  | thirdLeft
  | thirdRight

private structure UnitCubePoint where
  first : I
  second : I
  third : I

private def HybridTensorSubdivision.ofOrdinary :
    TensorSubdivision → HybridTensorSubdivision
  | .leaf => .certified
  | .splitFirst left right => .splitFirst (ofOrdinary left) (ofOrdinary right)
  | .splitSecond left right => .splitSecond (ofOrdinary left) (ofOrdinary right)
  | .splitThird left right => .splitThird (ofOrdinary left) (ofOrdinary right)

private theorem HybridTensorSubdivision.ofOrdinary_not_exceptional
    (tree : TensorSubdivision) (x y z : I) :
    ¬ (HybridTensorSubdivision.ofOrdinary tree).ExceptionalAt x y z := by
  induction tree generalizing x y z with
  | leaf => simp [HybridTensorSubdivision.ofOrdinary,
      HybridTensorSubdivision.ExceptionalAt]
  | splitFirst left right ihLeft ihRight =>
      intro h
      rcases h with ⟨u, _, hu⟩ | ⟨u, _, hu⟩
      · exact ihLeft u y z hu
      · exact ihRight u y z hu
  | splitSecond left right ihLeft ihRight =>
      intro h
      rcases h with ⟨u, _, hu⟩ | ⟨u, _, hu⟩
      · exact ihLeft x u z hu
      · exact ihRight x u z hu
  | splitThird left right ihLeft ihRight =>
      intro h
      rcases h with ⟨u, _, hu⟩ | ⟨u, _, hu⟩
      · exact ihLeft x y u hu
      · exact ihRight x y u hu

private def HybridHalfStep.graft (step : HybridHalfStep)
    (ordinarySibling : TensorSubdivision) (continuation : HybridTensorSubdivision) :
    HybridTensorSubdivision :=
  match step with
  | .firstLeft => .splitFirst continuation (.ofOrdinary ordinarySibling)
  | .firstRight => .splitFirst (.ofOrdinary ordinarySibling) continuation
  | .secondLeft => .splitSecond continuation (.ofOrdinary ordinarySibling)
  | .secondRight => .splitSecond (.ofOrdinary ordinarySibling) continuation
  | .thirdLeft => .splitThird continuation (.ofOrdinary ordinarySibling)
  | .thirdRight => .splitThird (.ofOrdinary ordinarySibling) continuation

private def HybridHalfStep.embed (step : HybridHalfStep)
    (point : UnitCubePoint) : UnitCubePoint :=
  match step with
  | .firstLeft => ⟨unitIntervalLeftHalf point.first, point.second, point.third⟩
  | .firstRight => ⟨unitIntervalRightHalf point.first, point.second, point.third⟩
  | .secondLeft => ⟨point.first, unitIntervalLeftHalf point.second, point.third⟩
  | .secondRight => ⟨point.first, unitIntervalRightHalf point.second, point.third⟩
  | .thirdLeft => ⟨point.first, point.second, unitIntervalLeftHalf point.third⟩
  | .thirdRight => ⟨point.first, point.second, unitIntervalRightHalf point.third⟩

private def hybridTreeOfRoute :
    List (HybridHalfStep × TensorSubdivision) → HybridTensorSubdivision
  | [] => .analytic
  | (step, sibling) :: route => step.graft sibling (hybridTreeOfRoute route)

private def embedHybridRoute :
    List (HybridHalfStep × TensorSubdivision) → UnitCubePoint → UnitCubePoint
  | [], point => point
  | (step, _) :: route, point => step.embed (embedHybridRoute route point)

set_option maxHeartbeats 1000000 in
private theorem hybridTreeOfRoute_exceptionalAt_iff
    (route : List (HybridHalfStep × TensorSubdivision)) (x y z : I) :
    (hybridTreeOfRoute route).ExceptionalAt x y z ↔
      ∃ point, x = (embedHybridRoute route point).first ∧
        y = (embedHybridRoute route point).second ∧
        z = (embedHybridRoute route point).third := by
  induction route generalizing x y z with
  | nil =>
      constructor
      · intro _
        exact ⟨⟨x, y, z⟩, rfl, rfl, rfl⟩
      · intro _
        trivial
  | cons head route ih =>
      obtain ⟨step, sibling⟩ := head
      cases step <;> simp only [hybridTreeOfRoute, HybridHalfStep.graft,
          HybridTensorSubdivision.ExceptionalAt,
          HybridTensorSubdivision.ofOrdinary_not_exceptional, ih,
          embedHybridRoute, HybridHalfStep.embed] <;>
        constructor <;> aesop

private def weightedSelfBin5TenLeafSibling : TensorSubdivision :=
  .splitFirst .leaf <| .splitThird
    (.splitFirst .leaf <| .splitFirst .leaf <| .splitThird
      (.splitFirst .leaf <| .splitFirst .leaf <| .splitThird
        (.splitSecond .leaf .leaf) .leaf)
      .leaf)
    .leaf

private def weightedSelfBin5ThreeLeafSibling : TensorSubdivision :=
  .splitFirst .leaf (.splitSecond .leaf .leaf)

private def weightedSelfBin5ExceptionalRoute :
    List (HybridHalfStep × TensorSubdivision) := [
  (.thirdLeft, .leaf),
  (.thirdLeft, .leaf),
  (.thirdLeft, .leaf),
  (.firstRight, .leaf),
  (.firstRight, .leaf),
  (.thirdRight, .leaf),
  (.firstRight, .leaf),
  (.firstRight, .leaf),
  (.thirdLeft, weightedSelfBin5TenLeafSibling),
  (.firstRight, .leaf),
  (.thirdRight, .leaf),
  (.firstRight, .leaf),
  (.firstRight, .leaf),
  (.firstRight, .leaf),
  (.thirdRight, .leaf),
  (.firstRight, .leaf),
  (.secondLeft, .leaf),
  (.thirdRight, .leaf),
  (.firstRight, .leaf),
  (.firstRight, .leaf),
  (.firstRight, .leaf),
  (.thirdRight, weightedSelfBin5ThreeLeafSibling),
  (.secondRight, .leaf),
  (.firstRight, .leaf)]

/-- The 35 ordinary leaves and one analytic leaf in the tight discriminant tree. -/
def weightedSelfBin5DiscriminantTree : HybridTensorSubdivision :=
  .splitThird
    (.splitThird
      (.splitThird
        (.splitFirst
          (.certified)
          (.splitFirst
            (.certified)
            (.splitThird
              (.certified)
              (.splitFirst
                (.certified)
                (.splitFirst
                  (.certified)
                  (.splitThird
                    (.splitFirst
                      (.certified)
                      (.splitThird
                        (.certified)
                        (.splitFirst
                          (.certified)
                          (.splitFirst
                            (.certified)
                            (.splitFirst
                              (.certified)
                              (.splitThird
                                (.certified)
                                (.splitFirst
                                  (.certified)
                                  (.splitSecond
                                    (.splitThird
                                      (.certified)
                                      (.splitFirst
                                        (.certified)
                                        (.splitFirst
                                          (.certified)
                                          (.splitFirst
                                            (.certified)
                                            (.splitThird
                                              (.splitFirst
                                                (.certified)
                                                (.splitSecond
                                                  (.certified)
                                                  (.certified)))
                                              (.splitSecond
                                                (.certified)
                                                (.splitFirst
                                                  (.certified)
                                                  (.analytic))))))))
                                    (.certified)))))))))
                    (.splitFirst
                      (.certified)
                      (.splitThird
                        (.splitFirst
                          (.certified)
                          (.splitFirst
                            (.certified)
                            (.splitThird
                              (.splitFirst
                                (.certified)
                                (.splitFirst
                                  (.certified)
                                  (.splitThird
                                    (.splitSecond
                                      (.certified)
                                      (.certified))
                                    (.certified))))
                              (.certified))))
                        (.certified)))))))))
        (.certified))
      (.certified))
    (.certified)

private theorem weightedSelfBin5DiscriminantTree_eq_route :
    weightedSelfBin5DiscriminantTree =
      hybridTreeOfRoute weightedSelfBin5ExceptionalRoute := rfl

private theorem weightedSelfBin5ExceptionalRoute_embed (point : UnitCubePoint) :
    ((embedHybridRoute weightedSelfBin5ExceptionalRoute point).first : ℝ) =
        8191 / 8192 + (point.first : ℝ) / 8192 ∧
      ((embedHybridRoute weightedSelfBin5ExceptionalRoute point).second : ℝ) =
        1 / 4 + (point.second : ℝ) / 4 ∧
      ((embedHybridRoute weightedSelfBin5ExceptionalRoute point).third : ℝ) =
        47 / 512 + (point.third : ℝ) / 512 := by
  norm_num [weightedSelfBin5ExceptionalRoute, embedHybridRoute, HybridHalfStep.embed,
    unitIntervalLeftHalf, unitIntervalRightHalf]
  constructor
  · ring
  constructor <;> ring

/-- The analytic leaf is precisely contained in the exceptional dyadic coordinate box. -/
theorem weightedSelfBin5DiscriminantTree_exceptional_bounds {x y z : I}
    (h : weightedSelfBin5DiscriminantTree.ExceptionalAt x y z) :
    (8191 : ℝ) / 8192 ≤ x ∧ (x : ℝ) ≤ 1 ∧
      (1 : ℝ) / 4 ≤ y ∧ (y : ℝ) ≤ 1 / 2 ∧
      (47 : ℝ) / 512 ≤ z ∧ (z : ℝ) ≤ 3 / 32 := by
  rw [weightedSelfBin5DiscriminantTree_eq_route,
    hybridTreeOfRoute_exceptionalAt_iff] at h
  obtain ⟨point, hx, hy, hz⟩ := h
  obtain ⟨hxValue, hyValue, hzValue⟩ := weightedSelfBin5ExceptionalRoute_embed point
  rw [hx, hy, hz, hxValue, hyValue, hzValue]
  exact ⟨by nlinarith [point.first.2.1], by nlinarith [point.first.2.2],
    by nlinarith [point.second.2.1], by nlinarith [point.second.2.2],
    by nlinarith [point.third.2.1], by nlinarith [point.third.2.2]⟩

private def weightedSelfRadicalChart (lower upper : ℚ) :
    WeightedSelfChart (RadicalTrivariate 18) :=
  let coefficient i := RadicalTrivariate.constant (.var i)
  let rational q := RadicalTrivariate.constant (.constant q)
  let sub p q := RadicalTrivariate.add p (RadicalTrivariate.neg q)
  let b := RadicalTrivariate.add (rational lower)
    (RadicalTrivariate.mul (rational (upper - lower)) .second)
  let r := RadicalTrivariate.add (sub (coefficient 0) b)
    (RadicalTrivariate.mul
      (RadicalTrivariate.add (sub (rational 1) (coefficient 0)) b) .first)
  let t := RadicalTrivariate.add (rational (-1))
    (RadicalTrivariate.mul (rational 2) .third)
  ⟨r, b, t⟩

private def weightedSelfRadicalFormula (lower upper : ℚ) :
    WeightedSelfFormula (RadicalTrivariate 18) :=
  let chart := weightedSelfRadicalChart lower upper
  weightedSelfFormula radicalPolynomialOperations
    (fun i ↦ .constant (.var i)) chart.r chart.b chart.t

private def weightedSelfRadicalNegativeP (lower upper : ℚ) : RadicalTrivariate 18 :=
  RadicalTrivariate.neg (weightedSelfRadicalFormula lower upper).p

private def weightedSelfRadicalDiscriminant (lower upper : ℚ) : RadicalTrivariate 18 :=
  let formula := weightedSelfRadicalFormula lower upper
  RadicalTrivariate.add
    (RadicalTrivariate.mul formula.p formula.p)
    (RadicalTrivariate.neg
      (RadicalTrivariate.mul
        (RadicalTrivariate.mul formula.q formula.q) formula.radicand))

private theorem weightedSelfIntervalChart_contains (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) (input : Fin 18 → ℝ)
    (hinput : ∀ i, (box i).Contains (input i)) :
    let intervalChart := weightedSelfIntervalChart lower upper box
    let exactChart := weightedSelfRadicalChart lower upper
    intervalChart.r.Contains input exactChart.r ∧
      intervalChart.b.Contains input exactChart.b ∧
      intervalChart.t.Contains input exactChart.t := by
  let intervalChart := weightedSelfIntervalChart lower upper box
  let exactChart := weightedSelfRadicalChart lower upper
  change intervalChart.r.Contains input exactChart.r ∧
    intervalChart.b.Contains input exactChart.b ∧
    intervalChart.t.Contains input exactChart.t
  dsimp only [intervalChart, exactChart, weightedSelfIntervalChart,
    weightedSelfRadicalChart]
  constructor
  · apply IntervalTrivariate.contains_add
    · apply IntervalTrivariate.contains_add
      · exact IntervalTrivariate.contains_constant (hinput 0)
      · exact IntervalTrivariate.contains_neg <|
          IntervalTrivariate.contains_add
            (IntervalTrivariate.contains_constant
              (RationalInterval.singleton_contains lower))
            (IntervalTrivariate.contains_mul
              (IntervalTrivariate.contains_constant
                (RationalInterval.singleton_contains (upper - lower)))
              (IntervalTrivariate.contains_second input))
    · apply IntervalTrivariate.contains_mul
      · apply IntervalTrivariate.contains_add
        · apply IntervalTrivariate.contains_add
          · exact IntervalTrivariate.contains_constant
              (RationalInterval.singleton_contains 1)
          · exact IntervalTrivariate.contains_neg <|
              IntervalTrivariate.contains_constant (hinput 0)
        · exact IntervalTrivariate.contains_add
            (IntervalTrivariate.contains_constant
              (RationalInterval.singleton_contains lower))
            (IntervalTrivariate.contains_mul
              (IntervalTrivariate.contains_constant
                (RationalInterval.singleton_contains (upper - lower)))
              (IntervalTrivariate.contains_second input))
      · exact IntervalTrivariate.contains_first input
  · constructor
    · exact IntervalTrivariate.contains_add
        (IntervalTrivariate.contains_constant
          (RationalInterval.singleton_contains lower))
        (IntervalTrivariate.contains_mul
          (IntervalTrivariate.contains_constant
            (RationalInterval.singleton_contains (upper - lower)))
          (IntervalTrivariate.contains_second input))
    · exact IntervalTrivariate.contains_add
        (IntervalTrivariate.contains_constant
          (RationalInterval.singleton_contains (-1)))
        (IntervalTrivariate.contains_mul
          (IntervalTrivariate.contains_constant
            (RationalInterval.singleton_contains 2))
          (IntervalTrivariate.contains_third input))

private theorem weightedSelfIntervalFormula_contains (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) (input : Fin 18 → ℝ)
    (hinput : ∀ i, (box i).Contains (input i)) :
    let intervalFormula := weightedSelfIntervalFormula lower upper box
    let exactFormula := weightedSelfRadicalFormula lower upper
    intervalFormula.p.Contains input exactFormula.p ∧
      intervalFormula.q.Contains input exactFormula.q ∧
      intervalFormula.radicand.Contains input exactFormula.radicand := by
  obtain ⟨hr, hb, ht⟩ := weightedSelfIntervalChart_contains lower upper box input hinput
  exact weightedSelfFormula_rel intervalPolynomialOperations radicalPolynomialOperations
    (IntervalTrivariate.Contains input)
    (fun q ↦ IntervalTrivariate.contains_constant
      (RationalInterval.singleton_contains q))
    (fun ha hb ↦ IntervalTrivariate.contains_add ha hb)
    (fun ha ↦ IntervalTrivariate.contains_neg ha)
    (fun ha hb ↦ IntervalTrivariate.contains_mul ha hb)
    (fun ha n ↦ IntervalTrivariate.contains_pow ha n)
    (fun i ↦ IntervalTrivariate.contains_constant (hinput i)) hr hb ht

private theorem weightedSelfNegativePInterval_contains (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) (input : Fin 18 → ℝ)
    (hinput : ∀ i, (box i).Contains (input i)) :
    (weightedSelfNegativePIntervalPolynomial lower upper box).Contains input
      (weightedSelfRadicalNegativeP lower upper) := by
  exact IntervalTrivariate.contains_neg
    (weightedSelfIntervalFormula_contains lower upper box input hinput).1

private theorem weightedSelfQInterval_contains (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) (input : Fin 18 → ℝ)
    (hinput : ∀ i, (box i).Contains (input i)) :
    (weightedSelfQIntervalPolynomial lower upper box).Contains input
      (weightedSelfRadicalFormula lower upper).q :=
  (weightedSelfIntervalFormula_contains lower upper box input hinput).2.1

private theorem weightedSelfDiscriminantInterval_contains (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) (input : Fin 18 → ℝ)
    (hinput : ∀ i, (box i).Contains (input i)) :
    (weightedSelfDiscriminantIntervalPolynomial lower upper box).Contains input
      (weightedSelfRadicalDiscriminant lower upper) := by
  obtain ⟨hp, hq, hR⟩ := weightedSelfIntervalFormula_contains
    lower upper box input hinput
  exact IntervalTrivariate.contains_add
    (IntervalTrivariate.contains_mul hp hp)
    (IntervalTrivariate.contains_neg
      (IntervalTrivariate.contains_mul
        (IntervalTrivariate.contains_mul hq hq) hR))

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
private theorem weightedSelfRadicalPolynomials_fits (lower upper : ℚ) :
    (weightedSelfRadicalNegativeP lower upper).Fits 12 12 4 ∧
      (weightedSelfRadicalFormula lower upper).q.Fits 12 12 4 ∧
      (weightedSelfRadicalDiscriminant lower upper).Fits 12 12 4 := by
  simp (config := { maxSteps := 1000000 })
    [weightedSelfRadicalNegativeP, weightedSelfRadicalDiscriminant,
    weightedSelfRadicalFormula, weightedSelfRadicalChart, weightedSelfFormula,
    radicalPolynomialOperations,
    RadicalTrivariate.Fits, RadicalTrivariate.add, RadicalTrivariate.neg,
    RadicalTrivariate.mul, RadicalTrivariate.scaleSlice, RadicalTrivariate.constant,
    RadicalTrivariate.first, RadicalTrivariate.second, RadicalTrivariate.third,
    RadicalTrivariate.pow, RadicalBivariate.add, RadicalBivariate.neg,
    RadicalBivariate.mul, RadicalBivariate.scaleRow,
    RadicalUnivariate.add, RadicalUnivariate.neg, RadicalUnivariate.mul,
    RadicalUnivariate.scale]

private noncomputable def hybridSecondRadius (lower upper y : ℝ) : ℝ :=
  lower + (upper - lower) * y

private noncomputable def hybridFirstRadius (lower upper x y : ℝ) : ℝ :=
  let b := hybridSecondRadius lower upper y
  cStar - b + (1 - cStar + b) * x

private noncomputable def hybridProjection (z : ℝ) : ℝ :=
  -1 + 2 * z

private theorem weightedSelfRadicalChart_eval (lower upper : ℚ)
    (input : Fin 18 → ℝ) (hzero : input 0 = cStar) (x y z : ℝ) :
    let chart := weightedSelfRadicalChart lower upper
    chart.r.eval input x y z = hybridFirstRadius lower upper x y ∧
      chart.b.eval input x y z = hybridSecondRadius lower upper y ∧
      chart.t.eval input x y z = hybridProjection z := by
  dsimp only [weightedSelfRadicalChart]
  simp only [RadicalTrivariate.eval_add, RadicalTrivariate.eval_neg,
    RadicalTrivariate.eval_mul, RadicalTrivariate.eval_constant,
    RadicalTrivariate.eval_first, RadicalTrivariate.eval_second,
    RadicalTrivariate.eval_third, RadicalExpression.eval]
  rw [hzero]
  norm_num [hybridFirstRadius, hybridSecondRadius, hybridProjection]
  ring

private theorem weightedSelfRadicalFormula_eval (lower upper : ℚ) (x y z : ℝ)
    (hr : hybridFirstRadius lower upper x y ≠ 0) :
    let input := weightedSelfCoefficientInput (upper : ℝ)
    let formula := weightedSelfRadicalFormula lower upper
    formula.p.eval input x y z = weightedSelfPolynomialP
        (hybridFirstRadius lower upper x y) (hybridSecondRadius lower upper y)
        (hybridProjection z) upper ∧
      formula.q.eval input x y z = weightedSelfPolynomialQ
        (hybridFirstRadius lower upper x y) (hybridSecondRadius lower upper y)
        (hybridProjection z) upper ∧
      formula.radicand.eval input x y z = chordProjectionRadicand cStar
        (hybridFirstRadius lower upper x y) (hybridSecondRadius lower upper y)
        (hybridProjection z) := by
  let input := weightedSelfCoefficientInput (upper : ℝ)
  let chart := weightedSelfRadicalChart lower upper
  let formula := weightedSelfRadicalFormula lower upper
  let evaluate := fun p : RadicalTrivariate 18 ↦ p.eval input x y z
  have hmap := weightedSelfFormula_map radicalPolynomialOperations
    weightedSelfRealFormulaOperations evaluate
    (fun q ↦ by simp [evaluate, radicalPolynomialOperations,
      weightedSelfRealFormulaOperations, RadicalExpression.eval])
    (fun p q ↦ RadicalTrivariate.eval_add p q input x y z)
    (fun p ↦ RadicalTrivariate.eval_neg p input x y z)
    (fun p q ↦ RadicalTrivariate.eval_mul p q input x y z)
    (fun p n ↦ RadicalTrivariate.eval_pow p n input x y z)
    (fun i ↦ RadicalTrivariate.constant (.var i)) chart.r chart.b chart.t
  have hatom : evaluate ∘ (fun i ↦ RadicalTrivariate.constant (.var i)) = input := by
    funext i
    simp [evaluate, RadicalExpression.eval]
  have hchart := weightedSelfRadicalChart_eval lower upper input
    (by simp [input, weightedSelfCoefficientInput]) x y z
  dsimp only at hmap hchart
  change evaluate chart.r = hybridFirstRadius lower upper x y ∧
    evaluate chart.b = hybridSecondRadius lower upper y ∧
    evaluate chart.t = hybridProjection z at hchart
  rw [hatom, hchart.1, hchart.2.1, hchart.2.2] at hmap
  change evaluate formula.p = _ ∧ evaluate formula.q = _ ∧
    evaluate formula.radicand = _
  have hformula := weightedSelfRealFormula_eq_weightedSelf
    (hybridFirstRadius lower upper x y) (hybridSecondRadius lower upper y)
    (hybridProjection z) upper hr
  simpa only [formula, weightedSelfRadicalFormula, chart, input,
    weightedSelfRealFormula] using
      And.intro (hmap.1.trans hformula.1)
        (And.intro (hmap.2.1.trans hformula.2.1)
          (hmap.2.2.trans hformula.2.2))

private theorem weightedSelfRadicalDiscriminant_eval (lower upper : ℚ) (x y z : ℝ)
    (hr : hybridFirstRadius lower upper x y ≠ 0) :
    (weightedSelfRadicalDiscriminant lower upper).eval
        (weightedSelfCoefficientInput (upper : ℝ)) x y z =
      weightedSelfDiscriminant (hybridFirstRadius lower upper x y)
        (hybridSecondRadius lower upper y) (hybridProjection z) upper := by
  obtain ⟨hp, hq, hR⟩ := weightedSelfRadicalFormula_eval lower upper x y z hr
  simp only [weightedSelfRadicalDiscriminant, RadicalTrivariate.eval_add,
    RadicalTrivariate.eval_mul, RadicalTrivariate.eval_neg]
  rw [hp, hq, hR, weightedSelfDiscriminant]
  ring

private theorem hybridBin5_exceptional_discriminant_nonneg
    (kappaDBox kappaCBox : RationalInterval)
    (hD : (weightedSelfCoefficientExpression (4 / 5) 10).certifiesWithin
      weightedSelfEndpointBox kappaDBox = true)
    (hC : (weightedSelfCoefficientExpression (4 / 5) 14).certifiesWithin
      weightedSelfEndpointBox kappaCBox = true)
    (radialTree faceBBTree determinantTree : TensorSubdivision)
    (hradialCertificate : intervalPolynomialSubdivisionCertifiesNonnegative radialTree
      (weightedSelfExceptionalNegativeRadialIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      weightedSelfExceptionalRadiusInterval
      weightedSelfExceptionalSecondRadiusInterval
      weightedSelfExceptionalProjectionInterval = true)
    (hfaceBBCertificate : intervalPolynomialSubdivisionCertifiesNonnegative faceBBTree
      (weightedSelfExceptionalFaceBBMarginIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (.singleton 1) weightedSelfExceptionalSecondRadiusInterval
      weightedSelfExceptionalProjectionInterval = true)
    (hdeterminantCertificate : intervalPolynomialSubdivisionCertifiesNonnegative
      determinantTree
      (weightedSelfExceptionalFaceDeterminantIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (.singleton 1) weightedSelfExceptionalSecondRadiusInterval
      weightedSelfExceptionalProjectionInterval = true)
    (x y z : I) (hexceptional : weightedSelfBin5DiscriminantTree.ExceptionalAt x y z) :
    0 ≤ (weightedSelfRadicalDiscriminant (7 / 10) (4 / 5)).eval
      (weightedSelfCoefficientInput (4 / 5)) x y z := by
  obtain ⟨hxLower, hxUpper, hyLower, hyUpper, hzLower, hzUpper⟩ :=
    weightedSelfBin5DiscriminantTree_exceptional_bounds hexceptional
  let b := hybridSecondRadius (7 / 10) (4 / 5) y
  let r := hybridFirstRadius (7 / 10) (4 / 5) x y
  let t := hybridProjection z
  have hbLower : (29 : ℝ) / 40 ≤ b := by
    dsimp [b, hybridSecondRadius]
    norm_num
    nlinarith
  have hbUpper : b ≤ 3 / 4 := by
    dsimp [b, hybridSecondRadius]
    norm_num
    nlinarith
  have htLower : (-209 : ℝ) / 256 ≤ t := by
    dsimp [t, hybridProjection]
    nlinarith
  have htUpper : t ≤ -13 / 16 := by
    dsimp [t, hybridProjection]
    nlinarith
  have hfactor : 0 ≤ 1 - cStar + b := by
    nlinarith [cStar_mem_isolation_box.2.le]
  have hrLower : weightedSelfExceptionalRadialLower b ≤ r := by
    rw [weightedSelfExceptionalRadialLower]
    dsimp [r, hybridFirstRadius]
    change cStar - b + (1 - cStar + b) * (8191 / 8192) ≤
      cStar - b + (1 - cStar + b) * (x : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hxLower hfactor]
  have hrUpper : r ≤ 1 := by
    dsimp [r, hybridFirstRadius]
    nlinarith
  have hrPositive : 0 < r := by
    dsimp [r, hybridFirstRadius]
    nlinarith [one_lt_cStar_and_cStar_lt_two.1]
  have hrPositive' : 0 < hybridFirstRadius ((7 / 10 : ℚ) : ℝ)
      ((4 / 5 : ℚ) : ℝ) x y := by
    convert hrPositive using 1
    norm_num [r]
  have htarget :
      0 ≤ (weightedSelfRadicalDiscriminant (7 / 10) (4 / 5)).eval
        (weightedSelfCoefficientInput ((4 / 5 : ℚ) : ℝ)) x y z := by
    rw [weightedSelfRadicalDiscriminant_eval
      (7 / 10) (4 / 5) x y z hrPositive'.ne']
    convert
      weightedSelfDiscriminant_nonneg_on_exceptionalBox_of_interval_certificates
        kappaDBox kappaCBox hD hC radialTree faceBBTree determinantTree
        hradialCertificate hfaceBBCertificate hdeterminantCertificate
        hrLower hrUpper hbLower hbUpper htLower htUpper using 1
    norm_num [r, b, t]
  convert htarget using 1
  norm_num

private theorem exists_hybridFirstRadius_chart {r b : ℝ}
    (hb : cStar - 1 ≤ b) (hrLower : cStar - b ≤ r) (hrUpper : r ≤ 1) :
    ∃ x : I, cStar - b + (1 - cStar + b) * x = r := by
  have hden : 0 ≤ 1 - cStar + b := by linarith
  by_cases hzero : 1 - cStar + b = 0
  · have hr : r = 1 := by linarith
    refine ⟨⟨0, by constructor <;> norm_num⟩, ?_⟩
    simp [hzero, hr]
    linarith
  · have hdenPositive : 0 < 1 - cStar + b := lt_of_le_of_ne hden (Ne.symm hzero)
    let x : ℝ := (r - (cStar - b)) / (1 - cStar + b)
    have hx : x ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hrLower) hden
      · rw [div_le_one hdenPositive]
        linarith
    refine ⟨⟨x, hx⟩, ?_⟩
    dsimp [x]
    field_simp [hzero]
    ring

private theorem exists_hybridSecondRadius_chart {lower upper b : ℝ}
    (hwidth : lower < upper) (hbLower : lower ≤ b) (hbUpper : b ≤ upper) :
    ∃ y : I, hybridSecondRadius lower upper y = b := by
  have hden : 0 < upper - lower := sub_pos.mpr hwidth
  let y : ℝ := (b - lower) / (upper - lower)
  have hy : y ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hbLower) hden.le
    · rw [div_le_one hden]
      linarith
  refine ⟨⟨y, hy⟩, ?_⟩
  dsimp [y, hybridSecondRadius]
  field_simp [hden.ne']
  ring

private theorem exists_hybridProjection_chart {t : ℝ}
    (htLower : -1 ≤ t) (htUpper : t ≤ 1) :
    ∃ z : I, hybridProjection z = t := by
  let z : ℝ := (t + 1) / 2
  have hz : z ∈ Icc (0 : ℝ) 1 := by
    constructor <;> dsimp [z] <;> linarith
  refine ⟨⟨z, hz⟩, ?_⟩
  dsimp [z, hybridProjection]
  ring

set_option maxHeartbeats 10000000 in
/-- The ordinary leaves and the endpoint argument prove the tight fifth radius bin. -/
theorem weightedSelfBin5RadiusBound_of_hybrid_interval_certificates
    (kappaDBox kappaCBox : RationalInterval)
    (hD : (weightedSelfCoefficientExpression (4 / 5) 10).certifiesWithin
      weightedSelfEndpointBox kappaDBox = true)
    (hC : (weightedSelfCoefficientExpression (4 / 5) 14).certifiesWithin
      weightedSelfEndpointBox kappaCBox = true)
    (negativePTree qTree : TensorSubdivision)
    (hnegativeP : intervalTensorSubdivisionCertifiesNonnegative negativePTree
      (weightedSelfNegativePIntervalPolynomial (7 / 10) (4 / 5)
        (weightedSelfCoefficientBox kappaDBox kappaCBox)).bernsteinCoefficients = true)
    (hq : intervalTensorSubdivisionCertifiesNonnegative qTree
      (weightedSelfQIntervalPolynomial (7 / 10) (4 / 5)
        (weightedSelfCoefficientBox kappaDBox kappaCBox)).bernsteinCoefficients = true)
    (hdiscriminant : hybridIntervalTensorSubdivisionCertifiesNonnegative
      weightedSelfBin5DiscriminantTree
      (weightedSelfDiscriminantIntervalPolynomial (7 / 10) (4 / 5)
        (weightedSelfCoefficientBox kappaDBox kappaCBox)).bernsteinCoefficients = true)
    (radialTree faceBBTree determinantTree : TensorSubdivision)
    (hradialCertificate : intervalPolynomialSubdivisionCertifiesNonnegative radialTree
      (weightedSelfExceptionalNegativeRadialIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      weightedSelfExceptionalRadiusInterval
      weightedSelfExceptionalSecondRadiusInterval
      weightedSelfExceptionalProjectionInterval = true)
    (hfaceBBCertificate : intervalPolynomialSubdivisionCertifiesNonnegative faceBBTree
      (weightedSelfExceptionalFaceBBMarginIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (.singleton 1) weightedSelfExceptionalSecondRadiusInterval
      weightedSelfExceptionalProjectionInterval = true)
    (hdeterminantCertificate : intervalPolynomialSubdivisionCertifiesNonnegative
      determinantTree
      (weightedSelfExceptionalFaceDeterminantIntervalPolynomial
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      (.singleton 1) weightedSelfExceptionalSecondRadiusInterval
      weightedSelfExceptionalProjectionInterval = true) :
    WeightedSelfRadiusBinBound (7 / 10) (4 / 5) := by
  let box := weightedSelfCoefficientBox kappaDBox kappaCBox
  let input := weightedSelfCoefficientInput ((4 / 5 : ℚ) : ℝ)
  have hinput : ∀ i, (box i).Contains (input i) := by
    exact weightedSelfCoefficientInput_mem (4 / 5) kappaDBox kappaCBox hD hC
  obtain ⟨hnegativePFits, hqFits, hdiscriminantFits⟩ :=
    weightedSelfRadicalPolynomials_fits (7 / 10) (4 / 5)
  have hnegativePValues (x y z : I) :
      0 ≤ (weightedSelfRadicalNegativeP (7 / 10) (4 / 5)).eval input x y z := by
    exact RadicalTrivariate.nonneg_of_interval_bernstein_certificate
      (weightedSelfRadicalNegativeP (7 / 10) (4 / 5)) hnegativePFits
      (weightedSelfNegativePIntervalPolynomial (7 / 10) (4 / 5) box) input
      (weightedSelfNegativePInterval_contains (7 / 10) (4 / 5) box input hinput)
      negativePTree hnegativeP x y z
  have hqValues (x y z : I) :
      0 ≤ (weightedSelfRadicalFormula (7 / 10) (4 / 5)).q.eval input x y z := by
    exact RadicalTrivariate.nonneg_of_interval_bernstein_certificate
      (weightedSelfRadicalFormula (7 / 10) (4 / 5)).q hqFits
      (weightedSelfQIntervalPolynomial (7 / 10) (4 / 5) box) input
      (weightedSelfQInterval_contains (7 / 10) (4 / 5) box input hinput)
      qTree hq x y z
  have hdiscriminantValues (x y z : I) :
      0 ≤ (weightedSelfRadicalDiscriminant (7 / 10) (4 / 5)).eval input x y z := by
    apply RadicalTrivariate.nonneg_of_hybrid_interval_bernstein_certificate
      (weightedSelfRadicalDiscriminant (7 / 10) (4 / 5)) hdiscriminantFits
      (weightedSelfDiscriminantIntervalPolynomial (7 / 10) (4 / 5) box) input
      (weightedSelfDiscriminantInterval_contains (7 / 10) (4 / 5) box input hinput)
      weightedSelfBin5DiscriminantTree hdiscriminant
    intro x' y' z' hexceptional
    convert hybridBin5_exceptional_discriminant_nonneg
      kappaDBox kappaCBox hD hC radialTree faceBBTree determinantTree
      hradialCertificate hfaceBBCertificate hdeterminantCertificate
      x' y' z' hexceptional using 1
    norm_num [input]
  intro r b t hbLower hbUpper hrLower hrUpper htLower htUpper
  have hbPhysical : cStar - 1 ≤ b := by linarith
  obtain ⟨x, hx⟩ := exists_hybridFirstRadius_chart hbPhysical hrLower hrUpper
  obtain ⟨y, hy⟩ := exists_hybridSecondRadius_chart
    (lower := (7 : ℝ) / 10) (upper := 4 / 5) (by norm_num) hbLower hbUpper
  obtain ⟨z, hz⟩ := exists_hybridProjection_chart htLower htUpper
  have hchartB : hybridSecondRadius ((7 / 10 : ℚ) : ℝ)
      ((4 / 5 : ℚ) : ℝ) y = b := by
    convert hy using 1
    norm_num
  have hchartR : hybridFirstRadius ((7 / 10 : ℚ) : ℝ)
      ((4 / 5 : ℚ) : ℝ) x y = r := by
    dsimp [hybridFirstRadius]
    rw [hchartB]
    exact hx
  have hrPositive : 0 < r := by
    nlinarith [one_lt_cStar_and_cStar_lt_two.1]
  have hrChart : 0 < hybridFirstRadius ((7 / 10 : ℚ) : ℝ)
      ((4 / 5 : ℚ) : ℝ) x y := by rwa [hchartR]
  obtain ⟨hpValue, hqValue, _⟩ := weightedSelfRadicalFormula_eval
    (7 / 10) (4 / 5) x y z hrChart.ne'
  rw [hchartR, hchartB, hz] at hpValue hqValue
  have hp : weightedSelfPolynomialP r b t (4 / 5) ≤ 0 := by
    have hvalue := hnegativePValues x y z
    rw [weightedSelfRadicalNegativeP, RadicalTrivariate.eval_neg, hpValue] at hvalue
    convert (show weightedSelfPolynomialP r b t (((4 / 5 : ℚ) : ℝ)) ≤ 0 by linarith)
      using 1
    norm_num
  have hqValue' : 0 ≤ weightedSelfPolynomialQ r b t (4 / 5) := by
    have hvalue := hqValues x y z
    rw [hqValue] at hvalue
    convert hvalue using 1
    norm_num
  have hdiscriminantValue : 0 ≤ weightedSelfDiscriminant r b t (4 / 5) := by
    have hvalue := hdiscriminantValues x y z
    rw [weightedSelfRadicalDiscriminant_eval
      (7 / 10) (4 / 5) x y z hrChart.ne', hchartR, hchartB, hz] at hvalue
    convert hvalue using 1
    norm_num
  exact weightedSelfCoordinateMajorant_nonpos_of_polynomial_signs hrPositive
    (chordProjectionRadicand_nonneg_of_bounds hrLower hrUpper
      (hbUpper.trans (by norm_num)) htLower htUpper)
    hp hqValue' hdiscriminantValue

end Bescovitch
