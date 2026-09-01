/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.RationalEndpointData
public import Bescovitch.Certificates.RationalInterval
public import Bescovitch.SixPoint.WeightedMixedPolynomial

/-!
# Soundness of the adaptive mixed-certificate trees

The generated trees repeatedly bisect exact rational boxes.  Certified leaves are checked by
the dense Bernstein verifier, while discarded leaves must exactly exclude one of the four unit
disk constraints.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

open WeightedMixedPolynomial

/-- The least possible squared distance from an interval to a rational centre. -/
def intervalSquaredDistance (center : ℚ) (I : RationalInterval) : ℚ :=
  if I.upper < center then (I.upper - center) ^ 2
  else if center < I.lower then (I.lower - center) ^ 2 else 0

/-- Whether a rational rectangle is disjoint from a closed unit disk. -/
def unitDiskExcluded (center : ℚ) (longitudinal transverse : RationalInterval) : Bool :=
  decide (1 < intervalSquaredDistance center longitudinal + intervalSquaredDistance 0 transverse)

/-- The four unit-disk constraints for the two rational chord charts. -/
def WeightedMixedDiskConstraints (x : Fin 6 → ℝ) : Prop :=
  x 0 ^ 2 + x 1 ^ 2 ≤ 1 ∧
    (x 0 - (3467 / 2500 : ℚ)) ^ 2 + x 1 ^ 2 ≤ 1 ∧
    x 3 ^ 2 + x 4 ^ 2 ≤ 1 ∧
    (x 3 - (3467 / 2500 : ℚ)) ^ 2 + x 4 ^ 2 ≤ 1

/-- Exact test that a six-dimensional box violates a unit-disk constraint. -/
def weightedMixedOutside (box : Fin 6 → RationalInterval) : Bool :=
  unitDiskExcluded 0 (box 0) (box 1) ||
    unitDiskExcluded (3467 / 2500) (box 0) (box 1) ||
    unitDiskExcluded 0 (box 3) (box 4) ||
    unitDiskExcluded (3467 / 2500) (box 3) (box 4)

/-- Coordinate bisected at a given tree depth. -/
def weightedMixedSplitCoordinate (depth : ℕ) : Fin 6 :=
  ⟨depth % 6, Nat.mod_lt depth (by norm_num)⟩

/-- The lower half of a rational box at a given tree depth. -/
def weightedMixedLowerHalf (depth : ℕ) (box : Fin 6 → RationalInterval) :
    Fin 6 → RationalInterval :=
  let i := weightedMixedSplitCoordinate depth
  Function.update box i
    ⟨(box i).lower, ((box i).lower + (box i).upper) / 2, by
      linarith [(box i).lower_le_upper]⟩

/-- The upper half of a rational box at a given tree depth. -/
def weightedMixedUpperHalf (depth : ℕ) (box : Fin 6 → RationalInterval) :
    Fin 6 → RationalInterval :=
  let i := weightedMixedSplitCoordinate depth
  Function.update box i
    ⟨((box i).lower + (box i).upper) / 2, (box i).upper, by
      linarith [(box i).lower_le_upper]⟩

/-- Exact Bernstein check for one certified mixed-certificate leaf. -/
def weightedMixedLeafCheck (sideP sideW : ℚ) (box : Fin 6 → RationalInterval)
    (data : WeightedMixedLeaf) : Bool :=
  decide (∀ i, 0 < data.rhoNumerator i) &&
    MultivariateDensePolynomial.allNonpositive
      (MultivariateDensePolynomial.centeredBernstein degreeProfile
        (polynomialOfLeaf sideP sideW (fun i ↦ (box i).lower)
          (fun i ↦ (box i).upper) data))

/-- The exact checker for one adaptive mixed-certificate tree. -/
def weightedMixedTreeCheck (sideP sideW : ℚ) (depth : ℕ)
    (box : Fin 6 → RationalInterval) : WeightedMixedTree → Bool
  | .outside => weightedMixedOutside box
  | .certified data => weightedMixedLeafCheck sideP sideW box data
  | .split left right =>
      weightedMixedTreeCheck sideP sideW (depth + 1) (weightedMixedLowerHalf depth box) left &&
        weightedMixedTreeCheck sideP sideW (depth + 1) (weightedMixedUpperHalf depth box) right

/-- The exact root box for a pair of cap choices; `false` denotes cap zero. -/
def weightedMixedRootBox (capP capW : Bool) : Fin 6 → RationalInterval
  | 0 => if capP then
      ⟨3467 / 2500 / 2, 1, by norm_num⟩
    else
      ⟨3467 / 2500 - 1, 13868000000000001 / 10 ^ 16 / 2, by
        norm_num⟩
  | 1 => ⟨-720643 / 10 ^ 6, 720643 / 10 ^ 6, by norm_num⟩
  | 2 => ⟨0, 1, by norm_num⟩
  | 3 => if capW then
      ⟨3467 / 2500 / 2, 1, by norm_num⟩
    else
      ⟨3467 / 2500 - 1, 13868000000000001 / 10 ^ 16 / 2, by
        norm_num⟩
  | 4 => ⟨-720643 / 10 ^ 6, 720643 / 10 ^ 6, by norm_num⟩
  | 5 => ⟨-1, 1, by norm_num⟩

namespace RationalInterval

/-- The centered-cube coordinate of a point in a rational interval. -/
def centeredCoordinate (I : RationalInterval) (x : ℝ) : ℝ :=
  if I.lower = I.upper then 0
  else (2 * x - I.lower - I.upper) / (I.upper - I.lower)

/-- Centering sends interval members into `[-1, 1]`. -/
theorem abs_centered_coordinate_le_one {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    |I.centeredCoordinate x| ≤ 1 := by
  by_cases h : I.lower = I.upper
  · simp [centeredCoordinate, h]
  · have hlt : I.lower < I.upper := lt_of_le_of_ne I.lower_le_upper h
    have hltReal : (I.lower : ℝ) < I.upper := by exact_mod_cast hlt
    rw [centeredCoordinate, if_neg h, abs_le]
    constructor
    · apply (le_div_iff₀ (sub_pos.mpr hltReal)).2
      norm_num [Contains] at hx
      linarith
    · apply (div_le_iff₀ (sub_pos.mpr hltReal)).2
      norm_num [Contains] at hx
      linarith

/-- Affine rescaling sends the centered coordinate back to the original point. -/
theorem midpoint_add_half_width_mul_centered_coordinate {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) :
    ((I.lower + I.upper : ℚ) : ℝ) / 2 + ((I.upper - I.lower : ℚ) : ℝ) / 2 *
        I.centeredCoordinate x = x := by
  by_cases h : I.lower = I.upper
  · norm_num [centeredCoordinate, h, Contains] at hx ⊢
    linarith
  · have hlt : I.lower < I.upper := lt_of_le_of_ne I.lower_le_upper h
    have hne : (I.upper : ℝ) - I.lower ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hlt))
    rw [centeredCoordinate, if_neg h]
    norm_num only [Rat.cast_add, Rat.cast_sub]
    field_simp [hne]
    ring

end RationalInterval

/-- Evaluating an affine coordinate at the centered box point recovers the original point. -/
theorem eval_affine_coordinate_centered_coordinate (box : Fin 6 → RationalInterval)
    (x : Fin 6 → ℝ) (hx : ∀ i, (box i).Contains (x i)) (i : Fin 6) :
    MultivariateDensePolynomial.eval
        (affineCoordinate i (box i).lower (box i).upper)
        (fun j ↦ (box j).centeredCoordinate (x j)) = x i := by
  rw [eval_affine_coordinate]
  simpa only [Rat.cast_add, Rat.cast_sub] using
    (box i).midpoint_add_half_width_mul_centered_coordinate (hx i)

private theorem interval_squared_distance_le_sq {center : ℚ} {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) : (intervalSquaredDistance center I : ℝ) ≤ (x - center) ^ 2 := by
  rw [intervalSquaredDistance]
  split_ifs with hupper hlower
  · norm_num only [Rat.cast_pow, Rat.cast_sub]
    have hupperReal : (I.upper : ℝ) < center := by exact_mod_cast hupper
    have hxUpper : x ≤ (I.upper : ℝ) := hx.2
    have hproduct : 0 ≤ (x - I.upper) * (x + I.upper - 2 * center) :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxUpper) (by linarith)
    nlinarith
  · norm_num only [Rat.cast_pow, Rat.cast_sub]
    have hlowerReal : (center : ℝ) < I.lower := by exact_mod_cast hlower
    have hxLower : (I.lower : ℝ) ≤ x := hx.1
    have hproduct : 0 ≤ (x - I.lower) * (x + I.lower - 2 * center) :=
      mul_nonneg (sub_nonneg.mpr hxLower) (by linarith)
    nlinarith
  · norm_num
    positivity

private theorem unit_disk_excluded_eq_false_of_mem {center : ℚ}
    {longitudinal transverse : RationalInterval} {x y : ℝ}
    (hx : longitudinal.Contains x) (hy : transverse.Contains y)
    (hdisk : (x - center) ^ 2 + y ^ 2 ≤ 1) :
    unitDiskExcluded center longitudinal transverse = false := by
  rw [unitDiskExcluded, decide_eq_false_iff_not]
  intro hexcluded
  have hlong := interval_squared_distance_le_sq (center := center) hx
  have htrans := interval_squared_distance_le_sq (center := (0 : ℚ)) hy
  have hexcludedReal : (1 : ℝ) <
      intervalSquaredDistance center longitudinal + intervalSquaredDistance 0 transverse := by
    exact_mod_cast hexcluded
  norm_num at htrans
  linarith

/-- A box containing a point satisfying all four disk constraints is not an outside box. -/
theorem weighted_mixed_outside_eq_false_of_constraints
    {box : Fin 6 → RationalInterval} {x : Fin 6 → ℝ}
    (hx : ∀ i, (box i).Contains (x i)) (hdisk : WeightedMixedDiskConstraints x) :
    weightedMixedOutside box = false := by
  have hPFirst := unit_disk_excluded_eq_false_of_mem (center := (0 : ℚ))
    (hx 0) (hx 1) (by simpa using hdisk.1)
  have hPSecond := unit_disk_excluded_eq_false_of_mem
    (center := (3467 / 2500 : ℚ)) (hx 0) (hx 1) hdisk.2.1
  have hWFirst := unit_disk_excluded_eq_false_of_mem (center := (0 : ℚ))
    (hx 3) (hx 4) (by simpa using hdisk.2.2.1)
  have hWSecond := unit_disk_excluded_eq_false_of_mem
    (center := (3467 / 2500 : ℚ)) (hx 3) (hx 4) hdisk.2.2.2
  simp [weightedMixedOutside, hPFirst, hPSecond, hWFirst, hWSecond]

private theorem mem_weighted_mixed_lower_half {depth : ℕ} {box : Fin 6 → RationalInterval}
    {x : Fin 6 → ℝ} (hx : ∀ i, (box i).Contains (x i))
    (hside : x (weightedMixedSplitCoordinate depth) ≤
      (((box (weightedMixedSplitCoordinate depth)).lower +
        (box (weightedMixedSplitCoordinate depth)).upper) / 2 : ℚ)) :
    ∀ i, (weightedMixedLowerHalf depth box i).Contains (x i) := by
  intro i
  by_cases hi : i = weightedMixedSplitCoordinate depth
  · subst i
    rw [weightedMixedLowerHalf, Function.update_self]
    exact ⟨(hx _).1, hside⟩
  · simpa [weightedMixedLowerHalf, hi] using hx i

private theorem mem_weighted_mixed_upper_half {depth : ℕ} {box : Fin 6 → RationalInterval}
    {x : Fin 6 → ℝ} (hx : ∀ i, (box i).Contains (x i))
    (hside : (((box (weightedMixedSplitCoordinate depth)).lower +
        (box (weightedMixedSplitCoordinate depth)).upper) / 2 : ℚ) ≤
      x (weightedMixedSplitCoordinate depth)) :
    ∀ i, (weightedMixedUpperHalf depth box i).Contains (x i) := by
  intro i
  by_cases hi : i = weightedMixedSplitCoordinate depth
  · subst i
    rw [weightedMixedUpperHalf, Function.update_self]
    exact ⟨hside, (hx _).2⟩
  · simpa [weightedMixedUpperHalf, hi] using hx i

/-- A successful tree check supplies a certified leaf for every feasible point in its box. -/
theorem exists_certified_leaf_of_weighted_mixed_tree_check
    (sideP sideW : ℚ) (tree : WeightedMixedTree) (depth : ℕ)
    (box : Fin 6 → RationalInterval) (x : Fin 6 → ℝ)
    (hcheck : weightedMixedTreeCheck sideP sideW depth box tree = true)
    (hx : ∀ i, (box i).Contains (x i)) (hdisk : WeightedMixedDiskConstraints x) :
    ∃ (leafBox : Fin 6 → RationalInterval) (data : WeightedMixedLeaf),
      (∀ i, 0 < data.rhoNumerator i) ∧
      (∀ i, (leafBox i).Contains (x i)) ∧
      MultivariateDensePolynomial.eval
          (polynomialOfLeaf sideP sideW (fun i ↦ (leafBox i).lower)
            (fun i ↦ (leafBox i).upper) data)
          (fun i ↦ (leafBox i).centeredCoordinate (x i)) ≤ 0 := by
  induction tree generalizing depth box with
  | outside =>
      rw [weightedMixedTreeCheck,
        weighted_mixed_outside_eq_false_of_constraints hx hdisk] at hcheck
      contradiction
  | certified data =>
      rw [weightedMixedTreeCheck, weightedMixedLeafCheck, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      refine ⟨box, data, hcheck.1, hx, ?_⟩
      exact MultivariateDensePolynomial.eval_nonpos_of_centeredBernstein_check_of_degree_bound
        degreeProfile _ (polynomial_of_leaf_degree_bound sideP sideW _ _ data) hcheck.2 _
        (fun i ↦ (box i).abs_centered_coordinate_le_one (hx i))
  | split left right ihLeft ihRight =>
      rw [weightedMixedTreeCheck, Bool.and_eq_true] at hcheck
      by_cases hside : x (weightedMixedSplitCoordinate depth) ≤
          ((((box (weightedMixedSplitCoordinate depth)).lower +
            (box (weightedMixedSplitCoordinate depth)).upper) / 2 : ℚ) : ℝ)
      · exact ihLeft (depth + 1) (weightedMixedLowerHalf depth box) hcheck.1
          (mem_weighted_mixed_lower_half hx hside)
      · exact ihRight (depth + 1) (weightedMixedUpperHalf depth box) hcheck.2
          (mem_weighted_mixed_upper_half hx (le_of_not_ge hside))

end Bescovitch
