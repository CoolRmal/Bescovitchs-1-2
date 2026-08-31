/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Geometry.PlaneCoordinates

/-!
# Rational charts for chords in the unit disk

A chord is described by its signed longitudinal and transverse coordinates relative to a unit
direction.  A stereographic parameter gives that direction without square roots.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Bescovitch

/-- A rational parametrization of either closed semicircle; `side` is `1` or `-1`. -/
def stereographicDirection (side z : ℝ) : Plane :=
  !₂[side * (1 - z ^ 2) / (1 + z ^ 2), 2 * z / (1 + z ^ 2)]

/-- The stereographic direction is a unit vector when the side is a sign. -/
@[simp]
theorem norm_stereographicDirection {side : ℝ} (z : ℝ) (hside : side ^ 2 = 1) :
    ‖stereographicDirection side z‖ = 1 := by
  have hden : 0 < 1 + z ^ 2 := by positivity
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [EuclideanSpace.real_norm_sq_eq, stereographicDirection, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hden.ne']
  nlinarith [sq_nonneg z, sq_nonneg (z ^ 2 - 1)]

/-- The two stereographic semicircles cover the unit circle with `z ∈ [-1,1]`. -/
theorem exists_stereographicDirection (n : Plane) (hn : ‖n‖ = 1) :
    ∃ side z : ℝ, (side = 1 ∨ side = -1) ∧ -1 ≤ z ∧ z ≤ 1 ∧
      stereographicDirection side z = n := by
  have hnSq : n 0 ^ 2 + n 1 ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ ↦ r ^ 2) hn
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using h
  by_cases hx : 0 ≤ n 0
  · let z := n 1 / (1 + n 0)
    have hxUpper : n 0 ≤ 1 := by nlinarith [sq_nonneg (n 1)]
    have hden : 0 < 1 + n 0 := by linarith
    have hzAbs : |n 1| ≤ 1 + n 0 := by
      apply (sq_le_sq₀ (abs_nonneg (n 1)) hden.le).1
      rw [sq_abs]
      nlinarith
    have hzLower : -1 ≤ z := by
      apply (le_div_iff₀ hden).2
      simpa using (abs_le.mp hzAbs).1
    have hzUpper : z ≤ 1 := by
      apply (div_le_iff₀ hden).2
      simpa using (abs_le.mp hzAbs).2
    have hcircleDen : (1 + n 0) ^ 2 + n 1 ^ 2 = 2 * (1 + n 0) := by
      nlinarith
    refine ⟨1, z, Or.inl rfl, hzLower, hzUpper, ?_⟩
    ext i
    fin_cases i <;> simp [stereographicDirection, z]
    · field_simp [hden.ne']
      nlinarith
    · field_simp [hden.ne']
      rw [hcircleDen]
      ring
  · have hxNeg : n 0 < 0 := lt_of_not_ge hx
    let z := n 1 / (1 - n 0)
    have hxLower : -1 ≤ n 0 := by nlinarith [sq_nonneg (n 1)]
    have hden : 0 < 1 - n 0 := by linarith
    have hzAbs : |n 1| ≤ 1 - n 0 := by
      apply (sq_le_sq₀ (abs_nonneg (n 1)) hden.le).1
      rw [sq_abs]
      nlinarith
    have hzLower : -1 ≤ z := by
      apply (le_div_iff₀ hden).2
      simpa using (abs_le.mp hzAbs).1
    have hzUpper : z ≤ 1 := by
      apply (div_le_iff₀ hden).2
      simpa using (abs_le.mp hzAbs).2
    have hcircleDen : (1 - n 0) ^ 2 + n 1 ^ 2 = 2 * (1 - n 0) := by
      nlinarith
    refine ⟨-1, z, Or.inr rfl, hzLower, hzUpper, ?_⟩
    ext i
    fin_cases i <;> simp [stereographicDirection, z]
    · field_simp [hden.ne']
      nlinarith
    · field_simp [hden.ne']
      rw [hcircleDen]
      ring

/-- On the upper half-circle, the stereographic parameter can be chosen in `[0,1]`. -/
theorem exists_stereographicDirection_nonnegative (n : Plane) (hn : ‖n‖ = 1)
    (hnUpper : 0 ≤ n 1) :
    ∃ side z : ℝ, (side = 1 ∨ side = -1) ∧ 0 ≤ z ∧ z ≤ 1 ∧
      stereographicDirection side z = n := by
  obtain ⟨side, z, hside, -, hzUpper, hz⟩ := exists_stereographicDirection n hn
  have hcomponent := congrArg (fun x : Plane ↦ x 1) hz
  simp only [stereographicDirection, Matrix.cons_val_one, Matrix.cons_val_zero] at hcomponent
  have hden : 0 < 1 + z ^ 2 := by positivity
  have hquotient : 0 ≤ 2 * z / (1 + z ^ 2) := by rw [hcomponent]; exact hnUpper
  have hproduct := mul_nonneg hquotient hden.le
  have hzZero : 0 ≤ z := by
    field_simp [hden.ne'] at hproduct
    nlinarith
  exact ⟨side, z, hside, hzZero, hzUpper, hz⟩

/-- The first endpoint of the chord with longitudinal coordinate `a` and transverse coordinate
`h`. -/
def chordChartFirst (side a h z : ℝ) : Plane :=
  a • stereographicDirection side z + h • quarterTurn (stereographicDirection side z)

/-- The second endpoint, a distance `c` backward along the chord direction. -/
def chordChartSecond (side c a h z : ℝ) : Plane :=
  (a - c) • stereographicDirection side z + h • quarterTurn (stereographicDirection side z)

/-- The first chart endpoint has squared radius `a² + h²`. -/
theorem norm_chordChartFirst_sq {side : ℝ} (a h z : ℝ) (hside : side ^ 2 = 1) :
    ‖chordChartFirst side a h z‖ ^ 2 = a ^ 2 + h ^ 2 := by
  let n := stereographicDirection side z
  have hn : ‖n‖ = 1 := norm_stereographicDirection z hside
  have horth : ⟪(a • n), (h • quarterTurn n)⟫_ℝ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right]
  change ‖a • n + h • quarterTurn n‖ ^ 2 = a ^ 2 + h ^ 2
  rw [pow_two,
    (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero _ _).2 horth]
  simp [n, hn, norm_smul]
  ring

/-- The second chart endpoint has squared radius `(a-c)² + h²`. -/
theorem norm_chordChartSecond_sq {side : ℝ} (c a h z : ℝ) (hside : side ^ 2 = 1) :
    ‖chordChartSecond side c a h z‖ ^ 2 = (a - c) ^ 2 + h ^ 2 := by
  let n := stereographicDirection side z
  have hn : ‖n‖ = 1 := norm_stereographicDirection z hside
  have horth : ⟪((a - c) • n), (h • quarterTurn n)⟫_ℝ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right]
  change ‖(a - c) • n + h • quarterTurn n‖ ^ 2 = (a - c) ^ 2 + h ^ 2
  rw [pow_two,
    (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero _ _).2 horth]
  simp [n, hn, norm_smul]
  ring

/-- The two chart endpoints differ by `c` times the chart direction. -/
theorem chordChartFirst_sub_second (side c a h z : ℝ) :
    chordChartFirst side a h z - chordChartSecond side c a h z =
      c • stereographicDirection side z := by
  simp only [chordChartFirst, chordChartSecond]
  module

/-- For positive `c`, the chart describes a chord of length exactly `c`. -/
theorem norm_chordChartFirst_sub_second {side c : ℝ} (a h z : ℝ)
    (hside : side ^ 2 = 1) (hc : 0 ≤ c) :
    ‖chordChartFirst side a h z - chordChartSecond side c a h z‖ = c := by
  rw [chordChartFirst_sub_second, norm_smul, norm_stereographicDirection z hside,
    mul_one, Real.norm_eq_abs, abs_of_nonneg hc]

/-- Every positive-length chord in the plane has stereographic chord coordinates. -/
theorem exists_chordChart {p q : Plane} {c : ℝ} (hc : 0 < c) (hpq : ‖p - q‖ = c) :
    ∃ side z a h : ℝ,
      (side = 1 ∨ side = -1) ∧ -1 ≤ z ∧ z ≤ 1 ∧
        p = chordChartFirst side a h z ∧ q = chordChartSecond side c a h z := by
  let n : Plane := c⁻¹ • (p - q)
  have hn : ‖n‖ = 1 := by
    dsimp only [n]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), hpq]
    field_simp [hc.ne']
  have hchord : p - q = c • n := by
    dsimp only [n]
    rw [← mul_smul]
    field_simp [hc.ne']
    simp
  obtain ⟨side, z, hside, hzLower, hzUpper, hnChart⟩ :=
    exists_stereographicDirection n hn
  let a := ⟪n, p⟫_ℝ
  let h := ⟪quarterTurn n, p⟫_ℝ
  have hp : p = a • n + h • quarterTurn n := by
    simpa [a, h] using plane_eq_inner_smul_add_inner_quarterTurn_smul n p hn
  refine ⟨side, z, a, h, hside, hzLower, hzUpper, ?_, ?_⟩
  · rw [chordChartFirst, hnChart]
    exact hp
  · rw [chordChartSecond, hnChart]
    calc
      q = p - (p - q) := by abel
      _ = p - c • n := by rw [hchord]
      _ = (a - c) • n + h • quarterTurn n := by rw [hp]; module

/-- A chord whose direction lies in the upper half-plane has a chart with `z ∈ [0,1]`. -/
theorem exists_chordChart_nonnegative {p q : Plane} {c : ℝ} (hc : 0 < c)
    (hpq : ‖p - q‖ = c) (hupper : 0 ≤ (c⁻¹ • (p - q) : Plane) 1) :
    ∃ side z a h : ℝ,
      (side = 1 ∨ side = -1) ∧ 0 ≤ z ∧ z ≤ 1 ∧
        p = chordChartFirst side a h z ∧ q = chordChartSecond side c a h z := by
  let n : Plane := c⁻¹ • (p - q)
  have hn : ‖n‖ = 1 := by
    dsimp only [n]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), hpq]
    field_simp [hc.ne']
  have hnUpper : 0 ≤ n 1 := by simpa [n] using hupper
  have hchord : p - q = c • n := by
    dsimp only [n]
    rw [← mul_smul]
    field_simp [hc.ne']
    simp
  obtain ⟨side, z, hside, hzLower, hzUpper, hnChart⟩ :=
    exists_stereographicDirection_nonnegative n hn hnUpper
  let a := ⟪n, p⟫_ℝ
  let h := ⟪quarterTurn n, p⟫_ℝ
  have hp : p = a • n + h • quarterTurn n := by
    simpa [a, h] using plane_eq_inner_smul_add_inner_quarterTurn_smul n p hn
  refine ⟨side, z, a, h, hside, hzLower, hzUpper, ?_, ?_⟩
  · rw [chordChartFirst, hnChart]
    exact hp
  · rw [chordChartSecond, hnChart]
    calc
      q = p - (p - q) := by abel
      _ = p - c • n := by rw [hchord]
      _ = (a - c) • n + h • quarterTurn n := by rw [hp]; module

end Bescovitch
