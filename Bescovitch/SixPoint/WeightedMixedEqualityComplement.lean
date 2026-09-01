/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedEqualityPartition
public import Bescovitch.SixPoint.WeightedMixedStrictCertificate
import Bescovitch.SixPoint.WeightedMixedRootCover

/-!
# Semantic core for the equality-chart complement certificate

After the exact face partition, every noncentral cell is covered by a binary midpoint tree.
Outside leaves are disjoint from the feasible disk region, while certified leaves are discharged
by an abstract exact leaf checker supplied by the polynomial certificate layer.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- A midpoint tree covering one noncentral equality-partition cell. -/
inductive WeightedMixedEqualityComplementTree where
  /-- A box proved disjoint from the feasible disk region. -/
  | outside
  /-- A box discharged by the exact polynomial leaf checker. -/
  | certified (data : WeightedMixedLeaf)
  /-- Bisect one coordinate at its exact rational midpoint. -/
  | split (axis : Fin 6) (left right : WeightedMixedEqualityComplementTree)

/-- The lower midpoint half of one coordinate of a rational box. -/
def weightedMixedEqualityLowerHalf (axis : Fin 6) (box : Fin 6 → RationalInterval) :
    Fin 6 → RationalInterval :=
  Function.update box axis
    ⟨(box axis).lower, ((box axis).lower + (box axis).upper) / 2, by
      linarith [(box axis).lower_le_upper]⟩

/-- The upper midpoint half of one coordinate of a rational box. -/
def weightedMixedEqualityUpperHalf (axis : Fin 6) (box : Fin 6 → RationalInterval) :
    Fin 6 → RationalInterval :=
  Function.update box axis
    ⟨((box axis).lower + (box axis).upper) / 2, (box axis).upper, by
      linarith [(box axis).lower_le_upper]⟩

/-- Check an equality-complement tree using an exact checker at certified leaves. -/
def weightedMixedEqualityComplementCheck
    (leafCheck : (Fin 6 → RationalInterval) → WeightedMixedLeaf → Bool) :
    (Fin 6 → RationalInterval) → WeightedMixedEqualityComplementTree → Bool
  | box, .outside => weightedMixedOutside box
  | box, .certified data => leafCheck box data
  | box, .split axis left right =>
      weightedMixedEqualityComplementCheck leafCheck
          (weightedMixedEqualityLowerHalf axis box) left &&
        weightedMixedEqualityComplementCheck leafCheck
          (weightedMixedEqualityUpperHalf axis box) right

private theorem certificate_disk_constraints {x : Fin 6 → ℝ}
    (hPFirst : x 0 ^ 2 + x 1 ^ 2 ≤ 1)
    (hPSecond : (x 0 - cStar) ^ 2 + x 1 ^ 2 ≤ 1)
    (hWFirst : x 3 ^ 2 + x 4 ^ 2 ≤ 1)
    (hWSecond : (x 3 - cStar) ^ 2 + x 4 ^ 2 ≤ 1) :
    WeightedMixedDiskConstraints x := by
  have hPSecondCertificate := second_disk_constraint_at_certificate_chord hPFirst hPSecond
  have hWSecondCertificate := second_disk_constraint_at_certificate_chord hWFirst hWSecond
  refine ⟨hPFirst, ?_, hWFirst, ?_⟩
  · norm_num [certificateChord] at hPSecondCertificate ⊢
    exact hPSecondCertificate
  · norm_num [certificateChord] at hWSecondCertificate ⊢
    exact hWSecondCertificate

private theorem mem_weighted_mixed_equality_lower_half {axis : Fin 6}
    {box : Fin 6 → RationalInterval} {x : Fin 6 → ℝ}
    (hx : ∀ i, (box i).Contains (x i))
    (hside : x axis ≤ (((box axis).lower + (box axis).upper) / 2 : ℚ)) :
    ∀ i, (weightedMixedEqualityLowerHalf axis box i).Contains (x i) := by
  intro i
  by_cases hi : i = axis
  · subst i
    rw [weightedMixedEqualityLowerHalf, Function.update_self]
    exact ⟨(hx axis).1, hside⟩
  · simpa [weightedMixedEqualityLowerHalf, hi] using hx i

private theorem mem_weighted_mixed_equality_upper_half {axis : Fin 6}
    {box : Fin 6 → RationalInterval} {x : Fin 6 → ℝ}
    (hx : ∀ i, (box i).Contains (x i))
    (hside : ((((box axis).lower + (box axis).upper) / 2 : ℚ) : ℝ) ≤ x axis) :
    ∀ i, (weightedMixedEqualityUpperHalf axis box i).Contains (x i) := by
  intro i
  by_cases hi : i = axis
  · subst i
    rw [weightedMixedEqualityUpperHalf, Function.update_self]
    exact ⟨hside, (hx axis).2⟩
  · simpa [weightedMixedEqualityUpperHalf, hi] using hx i

/-- A successful complement-tree check bounds the mixed score on every feasible point of its box. -/
theorem weighted_mixed_equality_complement_sound
    (leafCheck : (Fin 6 → RationalInterval) → WeightedMixedLeaf → Bool)
    (leafSound : ∀ box data, leafCheck box data = true → ∀ x : Fin 6 → ℝ,
      (∀ i, (box i).Contains (x i)) →
      x 0 ^ 2 + x 1 ^ 2 ≤ 1 → (x 0 - cStar) ^ 2 + x 1 ^ 2 ≤ 1 →
      x 3 ^ 2 + x 4 ^ 2 ≤ 1 → (x 3 - cStar) ^ 2 + x 4 ^ 2 ≤ 1 →
      weightedMixedEqualityScore x ≤ 0)
    (tree : WeightedMixedEqualityComplementTree) (box : Fin 6 → RationalInterval)
    (hcheck : weightedMixedEqualityComplementCheck leafCheck box tree = true)
    (x : Fin 6 → ℝ) (hx : ∀ i, (box i).Contains (x i))
    (hPFirst : x 0 ^ 2 + x 1 ^ 2 ≤ 1)
    (hPSecond : (x 0 - cStar) ^ 2 + x 1 ^ 2 ≤ 1)
    (hWFirst : x 3 ^ 2 + x 4 ^ 2 ≤ 1)
    (hWSecond : (x 3 - cStar) ^ 2 + x 4 ^ 2 ≤ 1) :
    weightedMixedEqualityScore x ≤ 0 := by
  induction tree generalizing box with
  | outside =>
      rw [weightedMixedEqualityComplementCheck,
        weighted_mixed_outside_eq_false_of_constraints hx
          (certificate_disk_constraints hPFirst hPSecond hWFirst hWSecond)] at hcheck
      contradiction
  | certified data =>
      exact leafSound box data hcheck x hx hPFirst hPSecond hWFirst hWSecond
  | split axis left right ihLeft ihRight =>
      rw [weightedMixedEqualityComplementCheck, Bool.and_eq_true] at hcheck
      by_cases hside : x axis ≤
          (((box axis).lower + (box axis).upper) / 2 : ℚ)
      · exact ihLeft (weightedMixedEqualityLowerHalf axis box) hcheck.1
          (mem_weighted_mixed_equality_lower_half hx hside)
      · exact ihRight (weightedMixedEqualityUpperHalf axis box) hcheck.2
          (mem_weighted_mixed_equality_upper_half hx (le_of_not_ge hside))

/-- Exact trees for all noncentral cells prove the equality-complement bound. -/
theorem weightedMixedEqualityComplementBound_of_tree_checks
    (leafCheck : (Fin 6 → RationalInterval) → WeightedMixedLeaf → Bool)
    (leafSound : ∀ box data, leafCheck box data = true → ∀ x : Fin 6 → ℝ,
      (∀ i, (box i).Contains (x i)) →
      x 0 ^ 2 + x 1 ^ 2 ≤ 1 → (x 0 - cStar) ^ 2 + x 1 ^ 2 ≤ 1 →
      x 3 ^ 2 + x 4 ^ 2 ≤ 1 → (x 3 - cStar) ^ 2 + x 4 ^ 2 ≤ 1 →
      weightedMixedEqualityScore x ≤ 0)
    (tree : ∀ cell, cell ≠ weightedMixedEqualityLocalCell →
      WeightedMixedEqualityComplementTree)
    (hcheck : ∀ (cell) (hcell : cell ≠ weightedMixedEqualityLocalCell),
      weightedMixedEqualityComplementCheck leafCheck
        (weightedMixedEqualityCellBox cell) (tree cell hcell) = true) :
    WeightedMixedEqualityComplementBound := by
  rw [WeightedMixedEqualityComplementBound]
  intro cell hcell x hx hPFirst hPSecond hWFirst hWSecond
  exact weighted_mixed_equality_complement_sound leafCheck leafSound (tree cell hcell)
    (weightedMixedEqualityCellBox cell) (hcheck cell hcell) x hx
    hPFirst hPSecond hWFirst hWSecond

/-- Exact mixed-leaf checks on all noncentral trees prove the equality-complement bound. -/
theorem weightedMixedEqualityComplementBound_of_leaf_checks
    (tree : ∀ cell, cell ≠ weightedMixedEqualityLocalCell →
      WeightedMixedEqualityComplementTree)
    (hcheck : ∀ (cell) (hcell : cell ≠ weightedMixedEqualityLocalCell),
      weightedMixedEqualityComplementCheck (weightedMixedLeafCheck (-1) (-1))
        (weightedMixedEqualityCellBox cell) (tree cell hcell) = true) :
    WeightedMixedEqualityComplementBound := by
  apply weightedMixedEqualityComplementBound_of_tree_checks
    (weightedMixedLeafCheck (-1) (-1)) _ tree hcheck
  intro box data hdata x hx hPFirst hPSecond hWFirst hWSecond
  have hscore :=
    weighted_pair_score_nonpos_of_weighted_mixed_leaf_check (-1) (-1) box data x
      hdata hx (by norm_num) (by norm_num) hPFirst hPSecond hWFirst hWSecond
  norm_num only [Rat.cast_neg, Rat.cast_one] at hscore
  simpa only [weightedMixedEqualityScore] using hscore

end Bescovitch
