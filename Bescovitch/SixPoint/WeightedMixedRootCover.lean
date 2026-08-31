/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedTree

/-!
# Cover by the rational mixed-certificate root boxes

The two unit-disk inequalities confine each chord midpoint to one of two longitudinal caps and
to a short transverse interval.  Together with the stereographic ranges, these bounds place
every feasible lens chart in one of the sixteen exact rational root boxes.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

/-- Replacing `cStar` by the slightly smaller rational certificate chord preserves the second
unit-disk constraint. -/
theorem second_disk_constraint_at_certificate_chord {a h : ℝ}
    (hfirst : a ^ 2 + h ^ 2 ≤ 1) (hsecond : (a - cStar) ^ 2 + h ^ 2 ≤ 1) :
    (a - certificateChord) ^ 2 + h ^ 2 ≤ 1 := by
  have ha : a ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg h]
  have hc := cStar_certificateChord_distance.1
  have hcOne : 1 < certificateChord := by norm_num [certificateChord]
  have hlong : (a - certificateChord) ^ 2 ≤ (a - cStar) ^ 2 := by
    nlinarith [sq_nonneg (cStar - certificateChord)]
  linarith

private theorem longitudinal_bounds_of_disk_constraints {a h : ℝ}
    (hfirst : a ^ 2 + h ^ 2 ≤ 1)
    (hsecond : (a - cStar) ^ 2 + h ^ 2 ≤ 1) :
    certificateChord - 1 ≤ a ∧ a ≤ 1 := by
  have hsecondCertificate := second_disk_constraint_at_certificate_chord hfirst hsecond
  constructor <;> nlinarith [sq_nonneg h]

private theorem transverse_bounds_of_disk_constraints {a h : ℝ}
    (hfirst : a ^ 2 + h ^ 2 ≤ 1)
    (hsecond : (a - cStar) ^ 2 + h ^ 2 ≤ 1) :
    (-720643 / 10 ^ 6 : ℚ) ≤ h ∧ h ≤ (720643 / 10 ^ 6 : ℚ) := by
  have hsecondCertificate := second_disk_constraint_at_certificate_chord hfirst hsecond
  have hcentral : certificateChord ^ 2 + 4 * h ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (2 * a - certificateChord)]
  have hmargin : 4 < certificateChord ^ 2 + 4 * (720643 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [certificateChord]
  have hsquare : h ^ 2 ≤ (720643 / 10 ^ 6 : ℝ) ^ 2 := by linarith
  constructor <;> nlinarith

private theorem exists_longitudinal_cap {a : ℝ}
    (hlower : certificateChord - 1 ≤ a) (hupper : a ≤ 1) :
    ∃ cap : Bool,
      if cap then (certificateChord / 2 ≤ a ∧ a ≤ 1)
      else certificateChord - 1 ≤ a ∧
        a ≤ (13866128436518100 / 10 ^ 16 : ℝ) / 2 := by
  by_cases hcap : a ≤ certificateChord / 2
  · refine ⟨false, hlower, hcap.trans ?_⟩
    norm_num [certificateChord]
  · exact ⟨true, le_of_lt (lt_of_not_ge hcap), hupper⟩

/-- Every feasible pair of rational lens coordinates belongs to a mixed-certificate root box. -/
theorem exists_weighted_mixed_root_box
    (aP hP zP aW hW zW : ℝ)
    (hzP : 0 ≤ zP ∧ zP ≤ 1) (hzW : -1 ≤ zW ∧ zW ≤ 1)
    (hPFirst : aP ^ 2 + hP ^ 2 ≤ 1)
    (hPSecond : (aP - cStar) ^ 2 + hP ^ 2 ≤ 1)
    (hWFirst : aW ^ 2 + hW ^ 2 ≤ 1)
    (hWSecond : (aW - cStar) ^ 2 + hW ^ 2 ≤ 1) :
    ∃ capP capW : Bool, ∀ i,
      (weightedMixedRootBox capP capW i).Contains
        ((![aP, hP, zP, aW, hW, zW] : Fin 6 → ℝ) i) := by
  obtain ⟨capP, hcapP⟩ := exists_longitudinal_cap
    (longitudinal_bounds_of_disk_constraints hPFirst hPSecond).1
    (longitudinal_bounds_of_disk_constraints hPFirst hPSecond).2
  obtain ⟨capW, hcapW⟩ := exists_longitudinal_cap
    (longitudinal_bounds_of_disk_constraints hWFirst hWSecond).1
    (longitudinal_bounds_of_disk_constraints hWFirst hWSecond).2
  have hhP := transverse_bounds_of_disk_constraints hPFirst hPSecond
  have hhW := transverse_bounds_of_disk_constraints hWFirst hWSecond
  refine ⟨capP, capW, ?_⟩
  intro i
  fin_cases i
  · cases capP <;>
      simpa [weightedMixedRootBox, RationalInterval.Contains, certificateChord] using hcapP
  · simpa [weightedMixedRootBox, RationalInterval.Contains] using hhP
  · simpa [weightedMixedRootBox, RationalInterval.Contains] using hzP
  · cases capW <;>
      simpa [weightedMixedRootBox, RationalInterval.Contains, certificateChord] using hcapW
  · simpa [weightedMixedRootBox, RationalInterval.Contains] using hhW
  · simpa [weightedMixedRootBox, RationalInterval.Contains] using hzW

end Bescovitch
