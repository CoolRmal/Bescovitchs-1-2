/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Measure.UniformDensity
public import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Compact uniform-density pieces

An almost-everywhere strict lower-density bound can be made uniform on a compact subset,
while losing arbitrarily little Hausdorff measure.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace Bescovitch

/-- Increasing the scale index only weakens the defining radius restriction. -/
theorem monotone_uniformDensitySet (mu : Measure Plane) (A : Set Plane) (gamma : ℝ) :
    Monotone fun m ↦ uniformDensitySet mu A gamma m := by
  intro m n hmn x hx
  refine ⟨hx.1, fun q hq hq_small ↦ hx.2 q hq ?_⟩
  refine hq_small.trans_le <| one_div_le_one_div_of_le (by positivity) ?_
  exact_mod_cast Nat.add_le_add_right hmn 1

/-- Almost-everywhere density gives an arbitrarily small exceptional set at one uniform scale. -/
theorem exists_uniformDensitySet_measure_sdiff_lt {A : Set Plane} (hA : MeasurableSet A)
    {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hdensity : ∀ᵐ x ∂μH[1].restrict A,
      ENNReal.ofReal gamma < lowerOneDensity A x)
    (hfinite : μH[1] A ≠ ∞)
    {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, μH[1] (A \ uniformDensitySet (μH[1].restrict A) A gamma m) < epsilon := by
  letI : IsFiniteMeasure (μH[1].restrict A) := isFiniteMeasure_restrict.mpr hfinite
  let G : ℕ → Set Plane := fun m ↦ uniformDensitySet (μH[1].restrict A) A gamma m
  have hG_measurable (m : ℕ) : MeasurableSet (G m) :=
    measurableSet_uniformDensitySet _ hA _ _
  have hG_mono : Monotone G := monotone_uniformDensitySet _ _ _
  have hcovered : ∀ᵐ x ∂μH[1].restrict A, x ∈ ⋃ m, G m := by
    filter_upwards [ae_restrict_mem hA, hdensity] with x hxA hxDensity
    obtain ⟨m, hm⟩ :=
      exists_mem_uniformDensitySet_of_lt_lowerOneDensity hxA hgamma hxDensity
    exact mem_iUnion.2 ⟨m, hm⟩
  have hnull : μH[1] (⋂ m, A \ G m) = 0 := by
    have hnull_restrict : (μH[1].restrict A) (⋂ m, A \ G m) = 0 := by
      rw [← ae_eq_empty]
      refine eventuallyEq_set.2 ?_
      filter_upwards [hcovered] with x hx
      obtain ⟨m, hm⟩ := mem_iUnion.1 hx
      constructor
      · intro hx_inter
        have hxm : x ∈ A \ G m := mem_iInter.1 hx_inter m
        exact (hxm.2 hm).elim
      · simp
    rw [Measure.restrict_apply' hA] at hnull_restrict
    have hinter_subset : (⋂ m, A \ G m) ⊆ A := by
      intro x hx
      have hx0 : x ∈ A \ G 0 := mem_iInter.1 hx 0
      exact hx0.1
    simpa only [inter_eq_self_of_subset_left hinter_subset] using hnull_restrict
  have hanti : Antitone fun m ↦ A \ G m := by
    intro m n hmn x hx
    exact ⟨hx.1, fun hxG ↦ hx.2 (hG_mono hmn hxG)⟩
  have hmeasurable (m : ℕ) : NullMeasurableSet (A \ G m) μH[1] :=
    (hA.diff (hG_measurable m)).nullMeasurableSet
  have hfinite : ∃ m : ℕ, μH[1] (A \ G m) ≠ ∞ := by
    refine ⟨0, ?_⟩
    exact ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)
  have hinf : (⨅ m, μH[1] (A \ G m)) = 0 := by
    rw [← hanti.measure_iInter hmeasurable hfinite, hnull]
  by_contra h
  push Not at h
  have : epsilon ≤ (⨅ m, μH[1] (A \ G m)) := le_iInf h
  rw [hinf] at this
  exact (not_le_of_gt hepsilon) this

/-- A compact uniform-density piece can retain all but any prescribed positive mass. -/
theorem exists_compact_uniformDensitySet_measure_sdiff_lt {A : Set Plane}
    (hA : MeasurableSet A) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hdensity : ∀ᵐ x ∂μH[1].restrict A,
      ENNReal.ofReal gamma < lowerOneDensity A x)
    (hfinite : μH[1] A ≠ ∞) {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon) :
    ∃ (m : ℕ) (F : Set Plane), IsCompact F ∧
      F ⊆ uniformDensitySet (μH[1].restrict A) A gamma m ∧ μH[1] (A \ F) < epsilon := by
  letI : IsFiniteMeasure (μH[1].restrict A) := isFiniteMeasure_restrict.mpr hfinite
  have hhalf : 0 < epsilon / 2 := ENNReal.div_pos hepsilon.ne' (by norm_num)
  obtain ⟨m, hm⟩ :=
    exists_uniformDensitySet_measure_sdiff_lt hA hgamma hdensity hfinite hhalf
  let G := uniformDensitySet (μH[1].restrict A) A gamma m
  have hG : MeasurableSet G := measurableSet_uniformDensitySet _ hA _ _
  have hG_finite : μH[1] G ≠ ∞ :=
    ne_top_of_le_ne_top hfinite <| measure_mono fun _ hx ↦ hx.1
  obtain ⟨F, hFG, hF_compact, hGF⟩ :=
    hG.exists_isCompact_sdiff_lt hG_finite hhalf.ne'
  refine ⟨m, F, hF_compact, hFG, ?_⟩
  have hsubset : A \ F ⊆ (A \ G) ∪ (G \ F) := by
    intro x hx
    by_cases hxG : x ∈ G
    · exact Or.inr ⟨hxG, hx.2⟩
    · exact Or.inl ⟨hx.1, hxG⟩
  calc
    μH[1] (A \ F) ≤ μH[1] ((A \ G) ∪ (G \ F)) := measure_mono hsubset
    _ ≤ μH[1] (A \ G) + μH[1] (G \ F) := MeasureTheory.measure_union_le _ _
    _ < epsilon / 2 + epsilon / 2 := ENNReal.add_lt_add hm hGF
    _ = epsilon := ENNReal.add_halves epsilon

end Bescovitch
