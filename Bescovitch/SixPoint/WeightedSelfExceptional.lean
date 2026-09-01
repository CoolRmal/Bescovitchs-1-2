/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelf
import Bescovitch.Certificates.EndpointTightBounds
import Bescovitch.SixPoint.EndpointExtremizer
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The exceptional weighted-self box

The tight radius bin meets the endpoint equality configuration.  Radial monotonicity reduces its
last box to the face `r = 1`; there, exact stationarity removes the constant and linear terms and a
positive quadratic remainder proves nonnegativity.  The finite polynomial sign certificates are
kept as hypotheses in this analytic module.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

open Set

/-- A nonpositive derivative makes a real function decrease across a closed interval. -/
theorem value_le_of_hasDerivAt_nonpos_on_Icc {f f' : ℝ → ℝ} {x y : ℝ}
    (hxy : x ≤ y)
    (hderiv : ∀ z ∈ Icc x y, HasDerivAt f (f' z) z)
    (hnonpos : ∀ z ∈ Icc x y, f' z ≤ 0) :
    f y ≤ f x := by
  have hcontinuous : ContinuousOn f (Icc x y) := by
    intro z hz
    exact (hderiv z hz).continuousAt.continuousWithinAt
  have hantitone : AntitoneOn f (Icc x y) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x y) hcontinuous
      (fun z hz ↦ (hderiv z (interior_subset hz)).hasDerivWithinAt)
      (fun z hz ↦ hnonpos z (interior_subset hz))
  exact hantitone (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

/-- A function with zero initial value and slope is nonnegative when its second derivative is. -/
theorem value_nonneg_of_hasDerivAt2_nonneg_on_unitInterval
    {f f' f'' : ℝ → ℝ}
    (hvalue : f 0 = 0) (hslope : f' 0 = 0)
    (hfirst : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' s) s)
    (hsecond : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' s) s)
    (hsecondNonneg : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ f'' s) :
    0 ≤ f 1 := by
  have hslopeContinuous : ContinuousOn f' (Icc (0 : ℝ) 1) := by
    intro s hs
    exact (hsecond s hs).continuousAt.continuousWithinAt
  have hslopeMonotone : MonotoneOn f' (Icc (0 : ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
      hslopeContinuous
      (fun s hs ↦ (hsecond s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs ↦ hsecondNonneg s (interior_subset hs))
  have hslopeNonneg : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ f' s := by
    intro s hs
    rw [← hslope]
    exact hslopeMonotone (left_mem_Icc.mpr zero_le_one) hs hs.1
  have hcontinuous : ContinuousOn f (Icc (0 : ℝ) 1) := by
    intro s hs
    exact (hfirst s hs).continuousAt.continuousWithinAt
  have hmonotone : MonotoneOn f (Icc (0 : ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1) hcontinuous
      (fun s hs ↦ (hfirst s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs ↦ hslopeNonneg s (interior_subset hs))
  rw [← hvalue]
  exact hmonotone (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one) zero_le_one

/-- A positive leading coefficient and nonnegative determinant make a binary quadratic nonnegative.
-/
theorem quadraticForm_nonneg_of_positive_leading {db dt A M C : ℝ}
    (hA : 0 < A) (hdeterminant : 0 ≤ 4 * A * C - M ^ 2) :
    0 ≤ db ^ 2 * A + db * dt * M + dt ^ 2 * C := by
  have hsquare : 0 ≤ (2 * A * db + M * dt) ^ 2 := sq_nonneg _
  have hdeterminant' : 0 ≤ (4 * A * C - M ^ 2) * dt ^ 2 :=
    mul_nonneg hdeterminant (sq_nonneg _)
  have hscaled :
      0 ≤ 4 * A * (db ^ 2 * A + db * dt * M + dt ^ 2 * C) := by
    nlinarith
  nlinarith

/-- A stationary point is a minimum along a segment whose Hessian is positive semidefinite. -/
theorem value_nonneg_of_hessian_on_segment
    {f fb ft fbb fbt ftt : ℝ → ℝ → ℝ} {b₀ t₀ b t : ℝ}
    (hvalue : f b₀ t₀ = 0) (hgradientB : fb b₀ t₀ = 0)
    (hgradientT : ft b₀ t₀ = 0)
    (hfirst : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt
        (fun u ↦ f (b₀ + u * (b - b₀)) (t₀ + u * (t - t₀)))
        ((b - b₀) * fb (b₀ + s * (b - b₀)) (t₀ + s * (t - t₀)) +
          (t - t₀) * ft (b₀ + s * (b - b₀)) (t₀ + s * (t - t₀))) s)
    (hsecond : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt
        (fun u ↦
          (b - b₀) * fb (b₀ + u * (b - b₀)) (t₀ + u * (t - t₀)) +
            (t - t₀) * ft (b₀ + u * (b - b₀)) (t₀ + u * (t - t₀)))
        ((b - b₀) ^ 2 * fbb (b₀ + s * (b - b₀)) (t₀ + s * (t - t₀)) +
          2 * (b - b₀) * (t - t₀) *
            fbt (b₀ + s * (b - b₀)) (t₀ + s * (t - t₀)) +
          (t - t₀) ^ 2 * ftt (b₀ + s * (b - b₀))
            (t₀ + s * (t - t₀))) s)
    (hbbPos : ∀ s ∈ Icc (0 : ℝ) 1,
      0 < fbb (b₀ + s * (b - b₀)) (t₀ + s * (t - t₀)))
    (hdeterminant : ∀ s ∈ Icc (0 : ℝ) 1,
      0 ≤ fbb (b₀ + s * (b - b₀)) (t₀ + s * (t - t₀)) *
          ftt (b₀ + s * (b - b₀)) (t₀ + s * (t - t₀)) -
        fbt (b₀ + s * (b - b₀)) (t₀ + s * (t - t₀)) ^ 2) :
    0 ≤ f b t := by
  let pathB := fun s : ℝ ↦ b₀ + s * (b - b₀)
  let pathT := fun s : ℝ ↦ t₀ + s * (t - t₀)
  let slope := fun s : ℝ ↦
    (b - b₀) * fb (pathB s) (pathT s) +
      (t - t₀) * ft (pathB s) (pathT s)
  let curvature := fun s : ℝ ↦
    (b - b₀) ^ 2 * fbb (pathB s) (pathT s) +
      2 * (b - b₀) * (t - t₀) * fbt (pathB s) (pathT s) +
      (t - t₀) ^ 2 * ftt (pathB s) (pathT s)
  have hcurvature : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ curvature s := by
    intro s hs
    change 0 ≤
      (b - b₀) ^ 2 * fbb (pathB s) (pathT s) +
        2 * (b - b₀) * (t - t₀) * fbt (pathB s) (pathT s) +
        (t - t₀) ^ 2 * ftt (pathB s) (pathT s)
    have hdet := hdeterminant s hs
    have hdet' : 0 ≤
        4 * fbb (pathB s) (pathT s) * ftt (pathB s) (pathT s) -
          (2 * fbt (pathB s) (pathT s)) ^ 2 := by
      dsimp only [pathB, pathT] at hdet ⊢
      nlinarith
    have hquadratic := quadraticForm_nonneg_of_positive_leading
      (db := b - b₀) (dt := t - t₀)
      (A := fbb (pathB s) (pathT s))
      (M := 2 * fbt (pathB s) (pathT s))
      (C := ftt (pathB s) (pathT s))
      (hbbPos s hs) hdet'
    nlinarith
  have hpath := value_nonneg_of_hasDerivAt2_nonneg_on_unitInterval
    (f := fun s ↦ f (pathB s) (pathT s)) (f' := slope) (f'' := curvature)
    (by simpa [pathB, pathT] using hvalue)
    (by simp [slope, pathB, pathT, hgradientB, hgradientT])
    (by simpa [pathB, pathT, slope] using hfirst)
    (by simpa [pathB, pathT, slope, curvature] using hsecond)
    hcurvature
  simpa [pathB, pathT] using hpath

private theorem affine_mem_Icc {lower upper x y s : ℝ}
    (hx : x ∈ Icc lower upper) (hy : y ∈ Icc lower upper)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    x + s * (y - x) ∈ Icc lower upper := by
  have hcombo := (convex_Icc lower upper) hx hy
    (sub_nonneg.mpr hs.2) hs.1 (by ring : 1 - s + s = (1 : ℝ))
  rw [show x + s * (y - x) = (1 - s) * x + s * y by ring]
  simpa only [smul_eq_mul] using hcombo

/-- The restriction of the weighted-self discriminant to its outer radial face. -/
def weightedSelfExceptionalFace (b t : ℝ) : ℝ :=
  weightedSelfDiscriminant 1 b t (4 / 5)

/-- The lower radial face of the unresolved exceptional chart box. -/
def weightedSelfExceptionalRadialLower (b : ℝ) : ℝ :=
  cStar - b + (1 - cStar + b) * (8191 / 8192 : ℝ)

/-- The sharp endpoint lies in the exceptional face rectangle. -/
theorem weightedSelfExceptional_endpoint_mem :
    (29 : ℝ) / 40 ≤ endpointOuterRadius cStar certifiedEndpointPair.2 ∧
      endpointOuterRadius cStar certifiedEndpointPair.2 ≤ 3 / 4 ∧
      (-209 : ℝ) / 256 ≤ endpointUnitAbscissa certifiedEndpointPair.2 ∧
      endpointUnitAbscissa certifiedEndpointPair.2 ≤ -13 / 16 := by
  have hbLower := endpointOuterRadius_tight_bounds.1
  have hbUpper := endpointOuterRadius_tight_bounds.2
  have hBLower := endpointB_tight_bounds.1
  have hBUpper := endpointB_tight_bounds.2
  rw [endpointUnitAbscissa]
  norm_num at hbLower hbUpper hBLower hBUpper ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> nlinarith

private theorem weightedSelfExceptional_radicand_eq_sq :
    chordProjectionRadicand cStar 1
        (endpointOuterRadius cStar certifiedEndpointPair.2)
        (endpointUnitAbscissa certifiedEndpointPair.2) =
      (endpointChordAbscissa cStar certifiedEndpointPair.2 *
          endpointUnitAbscissa certifiedEndpointPair.2 -
        endpointOuterAbscissa cStar certifiedEndpointPair.2) ^ 2 := by
  have hpair : IsEndpointPair cStar certifiedEndpointPair.2 := by
    rw [cStar_eq_certifiedEndpointPair_fst]
    exact certifiedEndpointPair_isEndpointPair
  have hgram :
      (endpointChordAbscissa cStar certifiedEndpointPair.2 -
          endpointUnitAbscissa certifiedEndpointPair.2 *
            endpointOuterAbscissa cStar certifiedEndpointPair.2) ^ 2 =
        (1 - endpointUnitAbscissa certifiedEndpointPair.2 ^ 2) *
          (endpointOuterRadius cStar certifiedEndpointPair.2 ^ 2 -
            endpointOuterAbscissa cStar certifiedEndpointPair.2 ^ 2) := by
    simpa only [IsEndpointPair, endpointOuterRadius, endpointSecondDistance,
      endpointUnitAbscissa, endpointOuterAbscissa, endpointChordAbscissa] using
      hpair.2.2.2.2.2.1
  rw [endpointChordAbscissa] at hgram
  rw [chordProjectionRadicand, chordInnerProduct, endpointChordAbscissa]
  norm_num
  ring_nf at hgram ⊢
  nlinarith

private theorem weightedSelfExceptional_gramOrdinate_pos :
    0 < endpointChordAbscissa cStar certifiedEndpointPair.2 *
        endpointUnitAbscissa certifiedEndpointPair.2 -
      endpointOuterAbscissa cStar certifiedEndpointPair.2 := by
  have hpair : IsEndpointPair cStar certifiedEndpointPair.2 := by
    rw [cStar_eq_certifiedEndpointPair_fst]
    exact certifiedEndpointPair_isEndpointPair
  have hx : endpointUnitAbscissa certifiedEndpointPair.2 < 0 := by
    simpa only [IsEndpointPair, endpointOuterRadius, endpointSecondDistance,
      endpointUnitAbscissa, endpointOuterAbscissa, endpointChordAbscissa] using
      hpair.2.2.2.2.2.2.1
  have hz : endpointOuterAbscissa cStar certifiedEndpointPair.2 < 0 := by
    simpa only [IsEndpointPair, endpointOuterRadius, endpointSecondDistance,
      endpointUnitAbscissa, endpointOuterAbscissa, endpointChordAbscissa] using
      hpair.2.2.2.2.2.2.2.1
  have hc : (13 : ℝ) / 10 < cStar := by
    have := cStar_mem_isolation_box.1
    norm_num at this ⊢
    linarith
  have hb : endpointOuterRadius cStar certifiedEndpointPair.2 < (4 : ℝ) / 5 := by
    have := endpointOuterRadius_tight_bounds.2
    norm_num at this ⊢
    linarith
  have hcSq : (13 / 10 : ℝ) ^ 2 < cStar ^ 2 := by nlinarith
  have hbSq : endpointOuterRadius cStar certifiedEndpointPair.2 ^ 2 < (4 / 5 : ℝ) ^ 2 := by
    have hbPos : 0 < endpointOuterRadius cStar certifiedEndpointPair.2 := by
      have := endpointOuterRadius_tight_bounds.1
      norm_num at this ⊢
      linarith
    nlinarith
  have hk : endpointChordAbscissa cStar certifiedEndpointPair.2 < 0 := by
    rw [endpointChordAbscissa]
    nlinarith
  nlinarith [mul_pos_of_neg_of_neg hk hx]

private theorem weightedSelfExceptional_sqrt_radicand :
    Real.sqrt (chordProjectionRadicand cStar 1
      (endpointOuterRadius cStar certifiedEndpointPair.2)
      (endpointUnitAbscissa certifiedEndpointPair.2)) =
        endpointChordAbscissa cStar certifiedEndpointPair.2 *
          endpointUnitAbscissa certifiedEndpointPair.2 -
        endpointOuterAbscissa cStar certifiedEndpointPair.2 := by
  rw [weightedSelfExceptional_radicand_eq_sq, Real.sqrt_sq_eq_abs,
    abs_of_pos weightedSelfExceptional_gramOrdinate_pos]

private theorem weightedSelfExceptional_unitOrdinate_pos :
    0 < endpointUnitOrdinate certifiedEndpointPair.2 := by
  have ht := weightedSelfExceptional_endpoint_mem.2.2
  rw [endpointUnitOrdinate]
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg
    (endpointUnitAbscissa certifiedEndpointPair.2 + 1),
    sq_nonneg (1 - endpointUnitAbscissa certifiedEndpointPair.2)]

private theorem weightedSelfExceptional_chordOrdinate_pos :
    0 < endpointChordOrdinate cStar certifiedEndpointPair.2 := by
  let b := endpointOuterRadius cStar certifiedEndpointPair.2
  let x := endpointUnitAbscissa certifiedEndpointPair.2
  let k := endpointChordAbscissa cStar certifiedEndpointPair.2
  have hx : 0 < 1 - x ^ 2 := by
    have ht := weightedSelfExceptional_endpoint_mem.2.2
    dsimp only [x]
    nlinarith [sq_nonneg
      (endpointUnitAbscissa certifiedEndpointPair.2 + 1),
      sq_nonneg (1 - endpointUnitAbscissa certifiedEndpointPair.2)]
  have hproduct : 0 < (1 - x ^ 2) * (b ^ 2 - k ^ 2) := by
    have hs := sq_pos_of_pos weightedSelfExceptional_gramOrdinate_pos
    rw [← weightedSelfExceptional_radicand_eq_sq] at hs
    simpa only [chordProjectionRadicand, chordInnerProduct,
      endpointChordAbscissa, one_pow, one_mul, b, x, k] using hs
  have hk : 0 < b ^ 2 - k ^ 2 := by
    rcases mul_pos_iff.mp hproduct with h | h
    · exact h.2
    · linarith
  dsimp only [endpointChordOrdinate, b, k]
  exact Real.sqrt_pos.2 hk

private theorem weightedSelfExceptional_gramOrdinate_eq_mul :
    endpointChordAbscissa cStar certifiedEndpointPair.2 *
        endpointUnitAbscissa certifiedEndpointPair.2 -
      endpointOuterAbscissa cStar certifiedEndpointPair.2 =
        endpointUnitOrdinate certifiedEndpointPair.2 *
          endpointChordOrdinate cStar certifiedEndpointPair.2 := by
  let b := endpointOuterRadius cStar certifiedEndpointPair.2
  let x := endpointUnitAbscissa certifiedEndpointPair.2
  let k := endpointChordAbscissa cStar certifiedEndpointPair.2
  let y := endpointUnitOrdinate certifiedEndpointPair.2
  let h := endpointChordOrdinate cStar certifiedEndpointPair.2
  have hySq : y ^ 2 = 1 - x ^ 2 := by
    dsimp only [y, x, endpointUnitOrdinate]
    exact Real.sq_sqrt (Real.sqrt_pos.1 weightedSelfExceptional_unitOrdinate_pos).le
  have hhSq : h ^ 2 = b ^ 2 - k ^ 2 := by
    dsimp only [h, b, k, endpointChordOrdinate]
    exact Real.sq_sqrt (Real.sqrt_pos.1 weightedSelfExceptional_chordOrdinate_pos).le
  have hsSq := weightedSelfExceptional_radicand_eq_sq
  rw [chordProjectionRadicand, chordInnerProduct, endpointChordAbscissa] at hsSq
  norm_num at hsSq
  change (1 - x ^ 2) * (b ^ 2 - k ^ 2) =
    (k * x - endpointOuterAbscissa cStar certifiedEndpointPair.2) ^ 2 at hsSq
  have hright : 0 < y * h := mul_pos
    weightedSelfExceptional_unitOrdinate_pos weightedSelfExceptional_chordOrdinate_pos
  have hleft := weightedSelfExceptional_gramOrdinate_pos
  change 0 < k * x - endpointOuterAbscissa cStar certifiedEndpointPair.2 at hleft
  change k * x - endpointOuterAbscissa cStar certifiedEndpointPair.2 = y * h
  nlinarith

private theorem weightedSelfExceptional_outerOrdinate_identity :
    endpointOuterOrdinate cStar certifiedEndpointPair.2 =
      endpointChordAbscissa cStar certifiedEndpointPair.2 *
          endpointUnitOrdinate certifiedEndpointPair.2 +
        endpointUnitAbscissa certifiedEndpointPair.2 *
          endpointChordOrdinate cStar certifiedEndpointPair.2 := by
  let b := endpointOuterRadius cStar certifiedEndpointPair.2
  let x := endpointUnitAbscissa certifiedEndpointPair.2
  let y := endpointUnitOrdinate certifiedEndpointPair.2
  let z := endpointOuterAbscissa cStar certifiedEndpointPair.2
  let k := endpointChordAbscissa cStar certifiedEndpointPair.2
  let h := endpointChordOrdinate cStar certifiedEndpointPair.2
  have hySq : y ^ 2 = 1 - x ^ 2 := by
    dsimp only [y, x, endpointUnitOrdinate]
    exact Real.sq_sqrt (Real.sqrt_pos.1 weightedSelfExceptional_unitOrdinate_pos).le
  have hhSq : h ^ 2 = b ^ 2 - k ^ 2 := by
    dsimp only [h, b, k, endpointChordOrdinate]
    exact Real.sq_sqrt (Real.sqrt_pos.1 weightedSelfExceptional_chordOrdinate_pos).le
  have hz : z = k * x - y * h := by
    have hs := weightedSelfExceptional_gramOrdinate_eq_mul
    dsimp only [x, y, z, k, h] at hs ⊢
    linarith
  have hsquare : (k * y + x * h) ^ 2 = b ^ 2 - z ^ 2 := by
    rw [hz]
    nlinarith
  have hpair : IsEndpointPair cStar certifiedEndpointPair.2 := by
    rw [cStar_eq_certifiedEndpointPair_fst]
    exact certifiedEndpointPair_isEndpointPair
  have hbranch : k - x * z < 0 := by
    simpa only [IsEndpointPair, endpointOuterRadius, endpointSecondDistance,
      endpointUnitAbscissa, endpointOuterAbscissa, endpointChordAbscissa,
      b, x, z, k] using hpair.2.2.2.2.2.2.2.2
  have hrhs : k * y + x * h < 0 := by
    have hy := weightedSelfExceptional_unitOrdinate_pos
    change 0 < y at hy
    rw [hz] at hbranch
    have heq : k - x * (k * x - y * h) = y * (k * y + x * h) := by
      calc
        k - x * (k * x - y * h) = k * (1 - x ^ 2) + x * y * h := by ring
        _ = k * y ^ 2 + x * y * h := by rw [← hySq]
        _ = y * (k * y + x * h) := by ring
    rw [heq] at hbranch
    rcases mul_neg_iff.mp hbranch with hneg | hneg
    · exact hneg.2
    · linarith
  have hsqrt : Real.sqrt (b ^ 2 - z ^ 2) = -(k * y + x * h) := by
    rw [← hsquare, Real.sqrt_sq_eq_abs, abs_of_neg hrhs]
  dsimp only [endpointOuterOrdinate, b, z, x, y, k, h]
  rw [hsqrt]
  ring

private theorem quarticNormTangent_at_target {weight target cap : ℝ}
    (htarget : target ≠ 0) :
    quarticNormTangent weight target cap (target ^ 2) = weight * target := by
  rw [quarticNormTangent]
  field_simp [htarget]
  ring

private theorem quarticNormTangent_hasDerivAt_at_target
    {q : ℝ → ℝ} {q' x weight target cap : ℝ}
    (hq : HasDerivAt q q' x) (hvalue : q x = target ^ 2) :
    HasDerivAt (fun u ↦ quarticNormTangent weight target cap (q u))
      (weight / (2 * target) * q') x := by
  have hlinear := (hq.const_mul (weight / (2 * target))).add_const
    (weight * target / 2)
  have hsub := hq.sub_const (target ^ 2)
  have hremainder := (hsub.mul hsub).const_mul
    (weight / (2 * target * (cap + target) ^ 2))
  have hraw : HasDerivAt
      ((fun u ↦ weight / (2 * target) * q u + weight * target / 2) -
        fun u ↦ weight / (2 * target * (cap + target) ^ 2) *
          ((q u - target ^ 2) * (q u - target ^ 2)))
      (weight / (2 * target) * q') x := by
    apply (hlinear.sub hremainder).congr_deriv
    rw [hvalue]
    ring
  have heq :
      (fun u ↦ quarticNormTangent weight target cap (q u)) =
        (fun u ↦ weight / (2 * target) * q u + weight * target / 2 -
          weight / (2 * target * (cap + target) ^ 2) *
            ((q u - target ^ 2) * (q u - target ^ 2))) := by
    funext u
    rw [quarticNormTangent, pow_two]
    ring
  rw [heq]
  apply hraw.congr_of_eventuallyEq
  filter_upwards [] with u
  rfl

private theorem weightedSelfExceptional_coordinateMajorant_eq_zero :
    weightedSelfCoordinateMajorant 1
      (endpointOuterRadius cStar certifiedEndpointPair.2)
      (endpointUnitAbscissa certifiedEndpointPair.2) (4 / 5) = 0 := by
  let B := certifiedEndpointPair.2
  let b := endpointOuterRadius cStar B
  let D := endpointSecondDistance cStar B
  let A := endpointFirstAuxiliaryDistance B
  let C := endpointMixedAuxiliaryDistance cStar B
  let x := endpointUnitAbscissa B
  let z := endpointOuterAbscissa cStar B
  let k := endpointChordAbscissa cStar B
  have hpair : IsEndpointPair cStar B := by
    dsimp only [B]
    rw [cStar_eq_certifiedEndpointPair_fst]
    exact certifiedEndpointPair_isEndpointPair
  have hB : 0 < B := by
    have := endpointB_tight_bounds.1
    dsimp only [B]
    norm_num at this ⊢
    linarith
  have hD : 0 < D := by
    have := endpointSecondDistance_tight_bounds.1
    dsimp only [D, B]
    norm_num at this ⊢
    linarith
  have hA : 0 < A := by
    dsimp only [A, B, endpointFirstAuxiliaryDistance]
    exact Real.sqrt_pos.2 certifiedEndpointPair_radicands_pos.1
  have hC : 0 < C := by
    dsimp only [C, B, endpointMixedAuxiliaryDistance, endpointSecondDistance]
    rw [cStar_eq_certifiedEndpointPair_fst]
    exact Real.sqrt_pos.2 certifiedEndpointPair_radicands_pos.2
  have hA_sq : A ^ 2 = (B ^ 2 - 1) / 2 := by
    dsimp only [A, B, endpointFirstAuxiliaryDistance]
    exact Real.sq_sqrt certifiedEndpointPair_radicands_pos.1.le
  have hC_sq : C ^ 2 = (B ^ 2 + D ^ 2) / 2 - cStar ^ 2 := by
    dsimp only [C, B, D, endpointMixedAuxiliaryDistance]
    exact Real.sq_sqrt (by
      simpa only [endpointSecondDistance, cStar_eq_certifiedEndpointPair_fst] using
        certifiedEndpointPair_radicands_pos.2.le)
  have hqB : 1 + 4 * (1 : ℝ) ^ 2 - 4 * 1 * x = B ^ 2 := by
    dsimp only [x, B, endpointUnitAbscissa]
    ring
  have hqD : 1 + 4 * b ^ 2 - 4 * z = D ^ 2 := by
    dsimp only [z, b, D, B, endpointOuterAbscissa]
    ring
  have hqA : 1 + (1 : ℝ) ^ 2 - 2 * 1 * x = A ^ 2 := by
    rw [hA_sq]
    dsimp only [x, B, endpointUnitAbscissa]
    ring
  have hk : chordInnerProduct cStar 1 b = k := by
    dsimp only [k, b, B, chordInnerProduct, endpointChordAbscissa]
    ring
  have hqC :
      1 + (1 : ℝ) ^ 2 + b ^ 2 - 2 * 1 * x - 2 * z + 2 * k = C ^ 2 := by
    rw [hC_sq]
    dsimp only [x, z, k, b, D, B, endpointUnitAbscissa,
      endpointOuterAbscissa, endpointChordAbscissa]
    ring
  have hbalance : A + C = 3 * cStar * b + cStar ^ 2 - 1 := by
    simpa only [IsEndpointPair, b, D, A, C, B, endpointOuterRadius,
      endpointSecondDistance, endpointFirstAuxiliaryDistance,
      endpointMixedAuxiliaryDistance] using hpair.2.2.2.2.1
  have hcNe : cStar + 1 ≠ 0 := by linarith [cStar_pos]
  have hbIdentity :
      (cStar + 1) * b = 2 * B - 3 * cStar ^ 2 + 2 * cStar - 1 := by
    dsimp only [b, B, endpointOuterRadius]
    field_simp [hcNe]
  rw [weightedSelfCoordinateMajorant]
  change weightedSelfCoordinateExpression 1 b x
    (Real.sqrt (chordProjectionRadicand cStar 1 b x)) (4 / 5) = 0
  have hsqrt : Real.sqrt (chordProjectionRadicand cStar 1 b x) = k * x - z := by
    simpa only [b, x, k, z, B] using weightedSelfExceptional_sqrt_radicand
  rw [hsqrt]
  simp only [weightedSelfCoordinateExpression]
  rw [hk]
  have hzBranch : (k * x - (k * x - z)) / 1 = z := by ring
  rw [hzBranch, hqB, hqD, hqA, hqC]
  rw [quarticNormTangent_at_target hB.ne', quarticNormTangent_at_target hD.ne',
    quarticNormTangent_at_target hA.ne', quarticNormTangent_at_target hC.ne']
  rw [weightedFirstPenalty, weightedSecondPenalty, weightedConstantTerm]
  dsimp only [D, endpointSecondDistance]
  linear_combination endpointMu * hbalance - endpointLambda / 2 * hbIdentity

/-- The reduced discriminant vanishes at the sharp weighted-self endpoint. -/
theorem weightedSelfDiscriminant_endpoint_eq_zero :
    weightedSelfDiscriminant 1
      (endpointOuterRadius cStar certifiedEndpointPair.2)
      (endpointUnitAbscissa certifiedEndpointPair.2) (4 / 5) = 0 := by
  let b := endpointOuterRadius cStar certifiedEndpointPair.2
  let t := endpointUnitAbscissa certifiedEndpointPair.2
  let R := chordProjectionRadicand cStar 1 b t
  let y := Real.sqrt R
  have hR : 0 ≤ R := by
    dsimp only [R, b, t]
    rw [weightedSelfExceptional_radicand_eq_sq]
    positivity
  have hySq : y ^ 2 = R := by
    exact Real.sq_sqrt hR
  have hreduction := weightedSelfCoordinateExpression_reduction 1 b t y (4 / 5) hySq
  have hmajorant : weightedSelfCoordinateExpression 1 b t y (4 / 5) = 0 := by
    simpa only [weightedSelfCoordinateMajorant, b, t, R, y] using
      weightedSelfExceptional_coordinateMajorant_eq_zero
  have hlinear :
      weightedSelfPolynomialP 1 b t (4 / 5) +
        weightedSelfPolynomialQ 1 b t (4 / 5) * y = 0 := by
    norm_num at hreduction
    linarith
  rw [weightedSelfDiscriminant]
  change weightedSelfPolynomialP 1 b t (4 / 5) ^ 2 -
    weightedSelfPolynomialQ 1 b t (4 / 5) ^ 2 * R = 0
  rw [← hySq]
  calc
    weightedSelfPolynomialP 1 b t (4 / 5) ^ 2 -
          weightedSelfPolynomialQ 1 b t (4 / 5) ^ 2 * y ^ 2 =
        (weightedSelfPolynomialP 1 b t (4 / 5) +
            weightedSelfPolynomialQ 1 b t (4 / 5) * y) *
          (weightedSelfPolynomialP 1 b t (4 / 5) -
            weightedSelfPolynomialQ 1 b t (4 / 5) * y) := by ring
    _ = 0 := by rw [hlinear, zero_mul]

private theorem weightedSelfExceptional_majorant_hasDerivAt_radius :
    HasDerivAt
      (fun u ↦ weightedSelfCoordinateMajorant 1 u
        (endpointUnitAbscissa certifiedEndpointPair.2) (4 / 5)) 0
      (endpointOuterRadius cStar certifiedEndpointPair.2) := by
  let B := certifiedEndpointPair.2
  let b := endpointOuterRadius cStar B
  let D := endpointSecondDistance cStar B
  let A := endpointFirstAuxiliaryDistance B
  let C := endpointMixedAuxiliaryDistance cStar B
  let x := endpointUnitAbscissa B
  let z := endpointOuterAbscissa cStar B
  let k := endpointChordAbscissa cStar B
  let y := endpointUnitOrdinate B
  let h := endpointChordOrdinate cStar B
  let rho := endpointAngularRate cStar B
  let zb := endpointOuterAbscissaDerivative cStar B
  let kfun := fun u : ℝ ↦ chordInnerProduct cStar 1 u
  let Rfun := fun u : ℝ ↦ (1 - x ^ 2) * (u ^ 2 - kfun u ^ 2)
  let sfun := fun u : ℝ ↦ Real.sqrt (Rfun u)
  let zfun := fun u : ℝ ↦ kfun u * x - sfun u
  let qBfun := fun _ : ℝ ↦ 1 + 4 * (1 : ℝ) ^ 2 - 4 * 1 * x
  let qDfun := fun u : ℝ ↦ 1 + 4 * u ^ 2 - 4 * zfun u
  let qAfun := fun _ : ℝ ↦ 1 + (1 : ℝ) ^ 2 - 2 * 1 * x
  let qCfun := fun u : ℝ ↦
    1 + (1 : ℝ) ^ 2 + u ^ 2 - 2 * 1 * x - 2 * zfun u + 2 * kfun u
  have hkValue : kfun b = k := by
    dsimp only [kfun, k, b, B, chordInnerProduct, endpointChordAbscissa]
    ring
  have hkDeriv : HasDerivAt kfun b b := by
    have hsq := (hasDerivAt_id b).mul (hasDerivAt_id b)
    have hraw := (((hasDerivAt_const b 1).add hsq).sub_const (cStar ^ 2)).div_const 2
    have hraw' : HasDerivAt (fun u ↦ ((1 + u * u) - cStar ^ 2) / 2) b b := by
      simpa only [id_eq, Pi.add_apply, Pi.mul_apply] using
        hraw.congr_deriv (show (0 + (1 * b + b * 1)) / 2 = b by ring)
    apply hraw'.congr_of_eventuallyEq
    filter_upwards [] with u
    dsimp only [kfun, chordInnerProduct]
    ring
  have hRDeriv : HasDerivAt Rfun (2 * (1 - x ^ 2) * b * (1 - k)) b := by
    have hbsq := (hasDerivAt_id b).mul (hasDerivAt_id b)
    have hksq := hkDeriv.mul hkDeriv
    have hraw := (hbsq.sub hksq).const_mul (1 - x ^ 2)
    simp only [id_eq] at hraw
    have hraw' := hraw.congr_deriv (show
      (1 - x ^ 2) * (1 * b + b * 1 - (b * kfun b + kfun b * b)) =
        2 * (1 - x ^ 2) * b * (1 - k) by rw [hkValue]; ring)
    apply hraw'.congr_of_eventuallyEq
    filter_upwards [] with u
    simp only [Rfun, Pi.sub_apply, Pi.mul_apply, pow_two, id_eq]
  have hRValue : Rfun b = (y * h) ^ 2 := by
    have hySq : y ^ 2 = 1 - x ^ 2 := by
      dsimp only [y, x, endpointUnitOrdinate]
      exact Real.sq_sqrt (Real.sqrt_pos.1 weightedSelfExceptional_unitOrdinate_pos).le
    have hhSq : h ^ 2 = b ^ 2 - k ^ 2 := by
      dsimp only [h, b, k, endpointChordOrdinate]
      exact Real.sq_sqrt (Real.sqrt_pos.1 weightedSelfExceptional_chordOrdinate_pos).le
    dsimp only [Rfun]
    rw [hkValue]
    nlinarith
  have hRNe : Rfun b ≠ 0 := by
    rw [hRValue]
    exact pow_ne_zero 2 (mul_ne_zero
      weightedSelfExceptional_unitOrdinate_pos.ne'
      weightedSelfExceptional_chordOrdinate_pos.ne')
  have hsValue : sfun b = y * h := by
    dsimp only [sfun]
    rw [hRValue, Real.sqrt_sq_eq_abs,
      abs_of_pos (mul_pos weightedSelfExceptional_unitOrdinate_pos
        weightedSelfExceptional_chordOrdinate_pos)]
  have hsDeriv : HasDerivAt sfun (y * rho) b := by
    have hsqrt := hRDeriv.sqrt hRNe
    apply hsqrt.congr_deriv
    change 2 * (1 - x ^ 2) * b * (1 - k) / (2 * sfun b) = y * rho
    rw [hsValue]
    dsimp only [rho, endpointAngularRate]
    change 2 * (1 - x ^ 2) * b * (1 - k) / (2 * (y * h)) =
      y * (b * (1 - k) / h)
    have hySq : y ^ 2 = 1 - x ^ 2 := by
      dsimp only [y, x, endpointUnitOrdinate]
      exact Real.sq_sqrt (Real.sqrt_pos.1 weightedSelfExceptional_unitOrdinate_pos).le
    rw [← hySq]
    field_simp [weightedSelfExceptional_unitOrdinate_pos.ne',
      weightedSelfExceptional_chordOrdinate_pos.ne']
  have hzValue : zfun b = z := by
    dsimp only [zfun]
    rw [hkValue, hsValue]
    have hs := weightedSelfExceptional_gramOrdinate_eq_mul
    dsimp only [k, x, z, y, h] at hs ⊢
    linarith
  have hzDeriv : HasDerivAt zfun zb b := by
    have hraw := (hkDeriv.mul_const x).sub hsDeriv
    apply hraw.congr_deriv
    dsimp only [zb, b, x, y, rho, B, endpointOuterAbscissaDerivative]
    ring
  have hqBValue : qBfun b = B ^ 2 := by
    dsimp only [qBfun, x, B, endpointUnitAbscissa]
    ring
  have hqDValue : qDfun b = D ^ 2 := by
    dsimp only [qDfun]
    rw [hzValue]
    dsimp only [z, b, D, B, endpointOuterAbscissa]
    ring
  have hqAValue : qAfun b = A ^ 2 := by
    have hA := Real.sq_sqrt certifiedEndpointPair_radicands_pos.1.le
    dsimp only [qAfun, x, A, B, endpointUnitAbscissa,
      endpointFirstAuxiliaryDistance]
    rw [hA]
    ring
  have hqCValue : qCfun b = C ^ 2 := by
    have hC : C ^ 2 = (B ^ 2 + D ^ 2) / 2 - cStar ^ 2 := by
      dsimp only [C, B, D, endpointMixedAuxiliaryDistance]
      exact Real.sq_sqrt (by
        simpa only [endpointSecondDistance, cStar_eq_certifiedEndpointPair_fst] using
          certifiedEndpointPair_radicands_pos.2.le)
    dsimp only [qCfun]
    rw [hzValue, hkValue, hC]
    dsimp only [x, z, k, b, D, B, endpointUnitAbscissa,
      endpointOuterAbscissa, endpointChordAbscissa]
    ring
  have hqB : HasDerivAt qBfun 0 b := hasDerivAt_const b _
  have hqA : HasDerivAt qAfun 0 b := hasDerivAt_const b _
  have hqD : HasDerivAt qDfun (8 * b - 4 * zb) b := by
    have hsq := (hasDerivAt_id b).mul (hasDerivAt_id b)
    have hraw := ((hasDerivAt_const b 1).add (hsq.const_mul 4)).sub
      (hzDeriv.const_mul 4)
    simp only [id_eq] at hraw
    have hraw' := hraw.congr_deriv (show 0 + 4 * (1 * b + b * 1) - 4 * zb =
      8 * b - 4 * zb by ring)
    apply hraw'.congr_of_eventuallyEq
    filter_upwards [] with u
    simp only [qDfun, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, pow_two, id_eq]
  have hqC : HasDerivAt qCfun (4 * b - 2 * zb) b := by
    have hsq := (hasDerivAt_id b).mul (hasDerivAt_id b)
    have hraw := (((((hasDerivAt_const b 1).add_const 1).add hsq).sub_const
      (2 * x)).sub (hzDeriv.const_mul 2)).add (hkDeriv.const_mul 2)
    simp only [id_eq] at hraw
    have hraw' := hraw.congr_deriv (show
      0 + (1 * b + b * 1) - 2 * zb + 2 * b = 4 * b - 2 * zb by ring)
    apply hraw'.congr_of_eventuallyEq
    filter_upwards [] with u
    simp only [qCfun, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, pow_two, id_eq]
    ring
  have hBterm := quarticNormTangent_hasDerivAt_at_target
    (weight := 1 + endpointLambda) (target := B) (cap := 3) hqB hqBValue
  have hDterm := quarticNormTangent_hasDerivAt_at_target
    (weight := 1) (target := D) (cap := 1 + 2 * (4 / 5)) hqD hqDValue
  have hAterm := quarticNormTangent_hasDerivAt_at_target
    (weight := endpointMu) (target := A) (cap := 2) hqA hqAValue
  have hCterm := quarticNormTangent_hasDerivAt_at_target
    (weight := endpointMu) (target := C) (cap := 2 + 4 / 5) hqC hqCValue
  have htotalFirst := (((hBterm.add hDterm).add hAterm).add hCterm).sub
    (hasDerivAt_const b (weightedFirstPenalty cStar endpointLambda endpointMu))
  have htotalSecond := htotalFirst.sub ((hasDerivAt_id b).const_mul
    (weightedSecondPenalty cStar endpointLambda endpointMu))
  have htotal := htotalSecond.sub
    (hasDerivAt_const b (weightedConstantTerm cStar endpointLambda endpointMu))
  have htotalZero : HasDerivAt
      (fun u ↦ quarticNormTangent (1 + endpointLambda) B 3 (qBfun u) +
          quarticNormTangent 1 D (1 + 2 * (4 / 5)) (qDfun u) +
          quarticNormTangent endpointMu A 2 (qAfun u) +
          quarticNormTangent endpointMu C (2 + 4 / 5) (qCfun u) -
          weightedFirstPenalty cStar endpointLambda endpointMu -
          weightedSecondPenalty cStar endpointLambda endpointMu * u -
          weightedConstantTerm cStar endpointLambda endpointMu) 0 b := by
    apply htotal.congr_deriv
    simp only [mul_zero, zero_add, add_zero, sub_zero, mul_one]
    calc
      1 / (2 * D) * (8 * b - 4 * zb) +
            endpointMu / (2 * C) * (4 * b - 2 * zb) -
          weightedSecondPenalty cStar endpointLambda endpointMu =
        endpointSecondDistanceDerivative cStar certifiedEndpointPair.2 +
            endpointLambda * endpointLambdaRadialCoefficient cStar +
          endpointMu * endpointMuRadialCoefficient cStar certifiedEndpointPair.2 := by
            have hDNe : D ≠ 0 := by
              have := endpointSecondDistance_tight_bounds.1
              dsimp only [D, B]
              norm_num at this ⊢
              linarith
            have hCNe : C ≠ 0 := by
              have := endpointMixedAuxiliaryDistance_tight_bounds.1
              dsimp only [C, B]
              norm_num at this ⊢
              linarith
            dsimp only [D, C, b, B, zb, endpointSecondDistanceDerivative,
              endpointMixedDistanceDerivative, endpointLambdaRadialCoefficient,
              endpointMuRadialCoefficient]
            rw [weightedSecondPenalty]
            field_simp [hDNe, hCNe]
            ring
      _ = 0 := endpoint_radial_stationarity
  apply htotalZero.congr_of_eventuallyEq
  filter_upwards [] with u
  have hkfun : kfun u = chordInnerProduct cStar 1 u := rfl
  have hRfun : Rfun u = chordProjectionRadicand cStar 1 u x := by
    dsimp only [Rfun, kfun, chordProjectionRadicand]
    norm_num
  dsimp only [x, B] at hRfun
  simp only [weightedSelfCoordinateMajorant, weightedSelfCoordinateExpression]
  dsimp only [B, D, A, C, x, sfun, zfun, qBfun, qDfun, qAfun, qCfun]
  rw [hkfun, hRfun]
  ring_nf

private theorem weightedSelfDiscriminant_hasDerivAt_zero_of_majorant
    {b t : ℝ → ℝ} {x : ℝ}
    (hb : DifferentiableAt ℝ b x) (ht : DifferentiableAt ℝ t x)
    (hRPos : 0 < chordProjectionRadicand cStar 1 (b x) (t x))
    (hmajorant : HasDerivAt
      (fun u ↦ weightedSelfCoordinateMajorant 1 (b u) (t u) (4 / 5)) 0 x)
    (hvalue : weightedSelfCoordinateMajorant 1 (b x) (t x) (4 / 5) = 0) :
    HasDerivAt
      (fun u ↦ weightedSelfDiscriminant 1 (b u) (t u) (4 / 5)) 0 x := by
  let R := fun u ↦ chordProjectionRadicand cStar 1 (b u) (t u)
  let other := fun u ↦
    weightedSelfPolynomialP 1 (b u) (t u) (4 / 5) -
      weightedSelfPolynomialQ 1 (b u) (t u) (4 / 5) * Real.sqrt (R u)
  have hP : DifferentiableAt ℝ
      (fun u ↦ weightedSelfPolynomialP 1 (b u) (t u) (4 / 5)) x := by
    simp only [weightedSelfPolynomialP, weightedSelfCoordinateExpression,
      quarticNormTangent, chordInnerProduct, chordProjectionRadicand]
    fun_prop
  have hQ : DifferentiableAt ℝ
      (fun u ↦ weightedSelfPolynomialQ 1 (b u) (t u) (4 / 5)) x := by
    simp only [weightedSelfPolynomialQ, weightedSelfCoordinateExpression,
      quarticNormTangent, chordInnerProduct]
    fun_prop
  have hR : DifferentiableAt ℝ R x := by
    dsimp only [R, chordProjectionRadicand, chordInnerProduct]
    fun_prop
  have hsqrt : DifferentiableAt ℝ (fun u ↦ Real.sqrt (R u)) x :=
    hR.sqrt hRPos.ne'
  have hother : DifferentiableAt ℝ other x := hP.sub (hQ.mul hsqrt)
  have hproduct := hmajorant.mul hother.hasDerivAt
  have hproductZero : HasDerivAt
      (fun u ↦ weightedSelfCoordinateMajorant 1 (b u) (t u) (4 / 5) * other u)
      0 x := by
    apply hproduct.congr_deriv
    rw [hvalue]
    ring
  have hRContinuous : ContinuousAt R x := hR.continuousAt
  have hRPositiveEventually : ∀ᶠ u in nhds x, 0 < R u :=
    hRContinuous (Ioi_mem_nhds hRPos)
  apply hproductZero.congr_of_eventuallyEq
  filter_upwards [hRPositiveEventually] with u hu
  have hsquare : Real.sqrt (R u) ^ 2 = R u := Real.sq_sqrt hu.le
  have hreduction := weightedSelfCoordinateExpression_reduction
    1 (b u) (t u) (Real.sqrt (R u)) (4 / 5) hsquare
  have hlinear :
      weightedSelfCoordinateMajorant 1 (b u) (t u) (4 / 5) =
        weightedSelfPolynomialP 1 (b u) (t u) (4 / 5) +
          weightedSelfPolynomialQ 1 (b u) (t u) (4 / 5) * Real.sqrt (R u) := by
    rw [weightedSelfCoordinateMajorant]
    norm_num at hreduction ⊢
    exact hreduction
  rw [weightedSelfDiscriminant, hlinear]
  dsimp only [other]
  calc
    weightedSelfPolynomialP 1 (b u) (t u) (4 / 5) ^ 2 -
          weightedSelfPolynomialQ 1 (b u) (t u) (4 / 5) ^ 2 * R u =
        weightedSelfPolynomialP 1 (b u) (t u) (4 / 5) ^ 2 -
          weightedSelfPolynomialQ 1 (b u) (t u) (4 / 5) ^ 2 *
            Real.sqrt (R u) ^ 2 := by rw [hsquare]
    _ = (weightedSelfPolynomialP 1 (b u) (t u) (4 / 5) +
            weightedSelfPolynomialQ 1 (b u) (t u) (4 / 5) * Real.sqrt (R u)) *
          (weightedSelfPolynomialP 1 (b u) (t u) (4 / 5) -
            weightedSelfPolynomialQ 1 (b u) (t u) (4 / 5) * Real.sqrt (R u)) := by ring

/-- The reduced discriminant is radially stationary at the sharp endpoint. -/
theorem weightedSelfDiscriminant_hasDerivAt_radius_endpoint :
    HasDerivAt
      (fun u ↦ weightedSelfDiscriminant 1 u
        (endpointUnitAbscissa certifiedEndpointPair.2) (4 / 5)) 0
      (endpointOuterRadius cStar certifiedEndpointPair.2) := by
  apply weightedSelfDiscriminant_hasDerivAt_zero_of_majorant
    (b := fun u ↦ u)
    (t := fun _ ↦ endpointUnitAbscissa certifiedEndpointPair.2)
  · fun_prop
  · fun_prop
  · rw [weightedSelfExceptional_radicand_eq_sq]
    exact sq_pos_of_pos weightedSelfExceptional_gramOrdinate_pos
  · exact weightedSelfExceptional_majorant_hasDerivAt_radius
  · exact weightedSelfExceptional_coordinateMajorant_eq_zero

private theorem weightedSelfExceptional_majorant_hasDerivAt_abscissa :
    HasDerivAt
      (fun u ↦ weightedSelfCoordinateMajorant 1
        (endpointOuterRadius cStar certifiedEndpointPair.2) u (4 / 5)) 0
      (endpointUnitAbscissa certifiedEndpointPair.2) := by
  let B := certifiedEndpointPair.2
  let b := endpointOuterRadius cStar B
  let D := endpointSecondDistance cStar B
  let A := endpointFirstAuxiliaryDistance B
  let C := endpointMixedAuxiliaryDistance cStar B
  let x := endpointUnitAbscissa B
  let z := endpointOuterAbscissa cStar B
  let k := endpointChordAbscissa cStar B
  let y := endpointUnitOrdinate B
  let h := endpointChordOrdinate cStar B
  let w := endpointOuterOrdinate cStar B
  let Rfun := fun u : ℝ ↦ (1 - u ^ 2) * (b ^ 2 - k ^ 2)
  let sfun := fun u : ℝ ↦ Real.sqrt (Rfun u)
  let zfun := fun u : ℝ ↦ k * u - sfun u
  let qBfun := fun u : ℝ ↦ 1 + 4 * (1 : ℝ) ^ 2 - 4 * 1 * u
  let qDfun := fun u : ℝ ↦ 1 + 4 * b ^ 2 - 4 * zfun u
  let qAfun := fun u : ℝ ↦ 1 + (1 : ℝ) ^ 2 - 2 * 1 * u
  let qCfun := fun u : ℝ ↦
    1 + (1 : ℝ) ^ 2 + b ^ 2 - 2 * 1 * u - 2 * zfun u + 2 * k
  have hySq : y ^ 2 = 1 - x ^ 2 := by
    dsimp only [y, x, endpointUnitOrdinate]
    exact Real.sq_sqrt (Real.sqrt_pos.1 weightedSelfExceptional_unitOrdinate_pos).le
  have hhSq : h ^ 2 = b ^ 2 - k ^ 2 := by
    dsimp only [h, b, k, endpointChordOrdinate]
    exact Real.sq_sqrt (Real.sqrt_pos.1 weightedSelfExceptional_chordOrdinate_pos).le
  have hRDeriv : HasDerivAt Rfun (-2 * x * (b ^ 2 - k ^ 2)) x := by
    have hsq := (hasDerivAt_id x).mul (hasDerivAt_id x)
    have hraw := ((hasDerivAt_const x 1).sub hsq).mul_const (b ^ 2 - k ^ 2)
    simp only [id_eq] at hraw
    have hraw' := hraw.congr_deriv (show
      (0 - (1 * x + x * 1)) * (b ^ 2 - k ^ 2) =
        -2 * x * (b ^ 2 - k ^ 2) by ring)
    apply hraw'.congr_of_eventuallyEq
    filter_upwards [] with u
    simp only [Rfun, Pi.sub_apply, Pi.mul_apply, pow_two, id_eq]
  have hRValue : Rfun x = (y * h) ^ 2 := by
    dsimp only [Rfun]
    nlinarith
  have hRNe : Rfun x ≠ 0 := by
    rw [hRValue]
    exact pow_ne_zero 2 (mul_ne_zero
      weightedSelfExceptional_unitOrdinate_pos.ne'
      weightedSelfExceptional_chordOrdinate_pos.ne')
  have hsValue : sfun x = y * h := by
    dsimp only [sfun]
    rw [hRValue, Real.sqrt_sq_eq_abs,
      abs_of_pos (mul_pos weightedSelfExceptional_unitOrdinate_pos
        weightedSelfExceptional_chordOrdinate_pos)]
  have hsDeriv : HasDerivAt sfun (-x * h / y) x := by
    have hsqrt := hRDeriv.sqrt hRNe
    apply hsqrt.congr_deriv
    change (-2 * x * (b ^ 2 - k ^ 2)) / (2 * sfun x) = -x * h / y
    rw [hsValue, ← hhSq]
    field_simp [weightedSelfExceptional_unitOrdinate_pos.ne',
      weightedSelfExceptional_chordOrdinate_pos.ne']
  have hzValue : zfun x = z := by
    dsimp only [zfun]
    rw [hsValue]
    have hs := weightedSelfExceptional_gramOrdinate_eq_mul
    dsimp only [k, x, z, y, h] at hs ⊢
    linarith
  have hzDeriv : HasDerivAt zfun (w / y) x := by
    have hraw := (hasDerivAt_id x).const_mul k |>.sub hsDeriv
    apply hraw.congr_deriv
    have hw := weightedSelfExceptional_outerOrdinate_identity
    change w = k * y + x * h at hw
    rw [hw]
    rw [add_div, mul_div_cancel_right₀ k
      weightedSelfExceptional_unitOrdinate_pos.ne']
    ring
  have hqBValue : qBfun x = B ^ 2 := by
    dsimp only [qBfun, x, B, endpointUnitAbscissa]
    ring
  have hqDValue : qDfun x = D ^ 2 := by
    dsimp only [qDfun]
    rw [hzValue]
    dsimp only [z, b, D, B, endpointOuterAbscissa]
    ring
  have hqAValue : qAfun x = A ^ 2 := by
    have hA := Real.sq_sqrt certifiedEndpointPair_radicands_pos.1.le
    dsimp only [qAfun, x, A, B, endpointUnitAbscissa,
      endpointFirstAuxiliaryDistance]
    rw [hA]
    ring
  have hqCValue : qCfun x = C ^ 2 := by
    have hC : C ^ 2 = (B ^ 2 + D ^ 2) / 2 - cStar ^ 2 := by
      dsimp only [C, B, D, endpointMixedAuxiliaryDistance]
      exact Real.sq_sqrt (by
        simpa only [endpointSecondDistance, cStar_eq_certifiedEndpointPair_fst] using
          certifiedEndpointPair_radicands_pos.2.le)
    dsimp only [qCfun]
    rw [hzValue, hC]
    dsimp only [x, z, k, b, D, B, endpointUnitAbscissa,
      endpointOuterAbscissa, endpointChordAbscissa]
    ring
  have hqB : HasDerivAt qBfun (-4) x := by
    have hraw := (hasDerivAt_const x 5).sub ((hasDerivAt_id x).const_mul 4)
    have hraw' := hraw.congr_deriv (show 0 - 4 * 1 = (-4 : ℝ) by ring)
    apply hraw'.congr_of_eventuallyEq
    filter_upwards [] with u
    dsimp only [qBfun]
    simp only [Pi.sub_apply, id_eq]
    ring
  have hqD : HasDerivAt qDfun (-4 * (w / y)) x := by
    have hraw := (hasDerivAt_const x (1 + 4 * b ^ 2)).sub (hzDeriv.const_mul 4)
    have hraw' := hraw.congr_deriv
      (show 0 - 4 * (w / y) = -4 * (w / y) by ring)
    apply hraw'.congr_of_eventuallyEq
    filter_upwards [] with u
    dsimp only [qDfun]
    simp only [Pi.sub_apply]
  have hqA : HasDerivAt qAfun (-2) x := by
    have hraw := (hasDerivAt_const x 2).sub ((hasDerivAt_id x).const_mul 2)
    have hraw' := hraw.congr_deriv (show 0 - 2 * 1 = (-2 : ℝ) by ring)
    apply hraw'.congr_of_eventuallyEq
    filter_upwards [] with u
    dsimp only [qAfun]
    simp only [Pi.sub_apply, id_eq]
    ring
  have hqC : HasDerivAt qCfun (-2 - 2 * (w / y)) x := by
    have hraw := ((hasDerivAt_const x (2 + b ^ 2 + 2 * k)).sub
      ((hasDerivAt_id x).const_mul 2)).sub (hzDeriv.const_mul 2)
    have hraw' := hraw.congr_deriv
      (show 0 - 2 * 1 - 2 * (w / y) = -2 - 2 * (w / y) by ring)
    apply hraw'.congr_of_eventuallyEq
    filter_upwards [] with u
    dsimp only [qCfun]
    simp only [Pi.sub_apply, id_eq]
    ring
  have hBterm := quarticNormTangent_hasDerivAt_at_target
    (weight := 1 + endpointLambda) (target := B) (cap := 3) hqB hqBValue
  have hDterm := quarticNormTangent_hasDerivAt_at_target
    (weight := 1) (target := D) (cap := 1 + 2 * (4 / 5)) hqD hqDValue
  have hAterm := quarticNormTangent_hasDerivAt_at_target
    (weight := endpointMu) (target := A) (cap := 2) hqA hqAValue
  have hCterm := quarticNormTangent_hasDerivAt_at_target
    (weight := endpointMu) (target := C) (cap := 2 + 4 / 5) hqC hqCValue
  have htotalFirst := (((hBterm.add hDterm).add hAterm).add hCterm).sub
    (hasDerivAt_const x (weightedFirstPenalty cStar endpointLambda endpointMu))
  have htotalSecond := htotalFirst.sub
    (hasDerivAt_const x
      (weightedSecondPenalty cStar endpointLambda endpointMu * b))
  have htotal := htotalSecond.sub
    (hasDerivAt_const x (weightedConstantTerm cStar endpointLambda endpointMu))
  have htotalZero : HasDerivAt
      (fun u ↦ quarticNormTangent (1 + endpointLambda) B 3 (qBfun u) +
          quarticNormTangent 1 D (1 + 2 * (4 / 5)) (qDfun u) +
          quarticNormTangent endpointMu A 2 (qAfun u) +
          quarticNormTangent endpointMu C (2 + 4 / 5) (qCfun u) -
          weightedFirstPenalty cStar endpointLambda endpointMu -
          weightedSecondPenalty cStar endpointLambda endpointMu * b -
          weightedConstantTerm cStar endpointLambda endpointMu) 0 x := by
    apply htotal.congr_deriv
    simp only [sub_zero]
    calc
      (1 + endpointLambda) / (2 * B) * (-4) +
              1 / (2 * D) * (-4 * (w / y)) +
            endpointMu / (2 * A) * (-2) +
          endpointMu / (2 * C) * (-2 - 2 * (w / y)) =
        -(endpointBaseAngularCoefficient cStar certifiedEndpointPair.2 +
            endpointLambda * endpointLambdaAngularCoefficient certifiedEndpointPair.2 +
          endpointMu * endpointMuAngularCoefficient cStar certifiedEndpointPair.2) / y := by
            have hBNe : B ≠ 0 := by
              have := endpointB_tight_bounds.1
              dsimp only [B]
              norm_num at this ⊢
              linarith
            have hDNe : D ≠ 0 := by
              have := endpointSecondDistance_tight_bounds.1
              dsimp only [D, B]
              norm_num at this ⊢
              linarith
            have hANe : A ≠ 0 := by
              dsimp only [A, B, endpointFirstAuxiliaryDistance]
              exact (Real.sqrt_pos.2 certifiedEndpointPair_radicands_pos.1).ne'
            have hCNe : C ≠ 0 := by
              have := endpointMixedAuxiliaryDistance_tight_bounds.1
              dsimp only [C, B]
              norm_num at this ⊢
              linarith
            dsimp only [B, D, A, C, y, w, endpointBaseAngularCoefficient,
              endpointLambdaAngularCoefficient, endpointMuAngularCoefficient]
            field_simp [hBNe, hDNe, hANe, hCNe,
              weightedSelfExceptional_unitOrdinate_pos.ne']
            ring
      _ = 0 := by rw [endpoint_angular_stationarity, neg_zero, zero_div]
  apply htotalZero.congr_of_eventuallyEq
  filter_upwards [] with u
  have hk : k = chordInnerProduct cStar 1 b := by
    dsimp only [k, b, B, endpointChordAbscissa, chordInnerProduct]
    ring
  have hRfun : Rfun u = chordProjectionRadicand cStar 1 b u := by
    dsimp only [Rfun, chordProjectionRadicand]
    rw [← hk]
    norm_num
  simp only [weightedSelfCoordinateMajorant, weightedSelfCoordinateExpression]
  dsimp only [B, D, A, C, b, sfun, zfun, qBfun, qDfun, qAfun, qCfun]
  dsimp only [b, B] at hk hRfun ⊢
  rw [hk, hRfun]
  ring_nf

/-- The reduced discriminant is angularly stationary at the sharp endpoint. -/
theorem weightedSelfDiscriminant_hasDerivAt_abscissa_endpoint :
    HasDerivAt
      (fun u ↦ weightedSelfDiscriminant 1
        (endpointOuterRadius cStar certifiedEndpointPair.2) u (4 / 5)) 0
      (endpointUnitAbscissa certifiedEndpointPair.2) := by
  apply weightedSelfDiscriminant_hasDerivAt_zero_of_majorant
    (b := fun _ ↦ endpointOuterRadius cStar certifiedEndpointPair.2)
    (t := fun u ↦ u)
  · fun_prop
  · fun_prop
  · rw [weightedSelfExceptional_radicand_eq_sq]
    exact sq_pos_of_pos weightedSelfExceptional_gramOrdinate_pos
  · exact weightedSelfExceptional_majorant_hasDerivAt_abscissa
  · exact weightedSelfExceptional_coordinateMajorant_eq_zero

private theorem weightedSelfDiscriminant_differentiableAt_radial
    {r b t upper : ℝ} (hr : r ≠ 0) :
    DifferentiableAt ℝ (fun s ↦ weightedSelfDiscriminant s b t upper) r := by
  simp only [weightedSelfDiscriminant, weightedSelfPolynomialP,
    weightedSelfPolynomialQ, weightedSelfCoordinateExpression,
    quarticNormTangent, chordInnerProduct, chordProjectionRadicand]
  fun_prop

/-- Radial monotonicity and a positive-semidefinite face Hessian control the exceptional box. -/
theorem weightedSelfDiscriminant_nonneg_on_exceptionalBox_of_certificates
    (faceB faceT faceBB faceBT faceTT : ℝ → ℝ → ℝ)
    (hradialNonpos : ∀ r b t,
      weightedSelfExceptionalRadialLower b ≤ r → r ≤ 1 →
      (29 : ℝ) / 40 ≤ b → b ≤ 3 / 4 →
      (-209 : ℝ) / 256 ≤ t → t ≤ -13 / 16 →
      deriv (fun s ↦ weightedSelfDiscriminant s b t (4 / 5)) r ≤ 0)
    (hfaceBBPos : ∀ b t,
      (29 : ℝ) / 40 ≤ b → b ≤ 3 / 4 →
      (-209 : ℝ) / 256 ≤ t → t ≤ -13 / 16 →
      0 < faceBB b t)
    (hfaceDeterminant : ∀ b t,
      (29 : ℝ) / 40 ≤ b → b ≤ 3 / 4 →
      (-209 : ℝ) / 256 ≤ t → t ≤ -13 / 16 →
      0 ≤ faceBB b t * faceTT b t - faceBT b t ^ 2)
    {r b t : ℝ}
    (hrLower : weightedSelfExceptionalRadialLower b ≤ r) (hrUpper : r ≤ 1)
    (hbLower : (29 : ℝ) / 40 ≤ b) (hbUpper : b ≤ 3 / 4)
    (htLower : (-209 : ℝ) / 256 ≤ t) (htUpper : t ≤ -13 / 16)
    (hgradientB : HasDerivAt
      (fun u ↦ weightedSelfExceptionalFace u
        (endpointUnitAbscissa certifiedEndpointPair.2))
      (faceB (endpointOuterRadius cStar certifiedEndpointPair.2)
        (endpointUnitAbscissa certifiedEndpointPair.2))
      (endpointOuterRadius cStar certifiedEndpointPair.2))
    (hgradientT : HasDerivAt
      (fun u ↦ weightedSelfExceptionalFace
        (endpointOuterRadius cStar certifiedEndpointPair.2) u)
      (faceT (endpointOuterRadius cStar certifiedEndpointPair.2)
        (endpointUnitAbscissa certifiedEndpointPair.2))
      (endpointUnitAbscissa certifiedEndpointPair.2))
    (hfirst : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt
        (fun u ↦ weightedSelfExceptionalFace
          (endpointOuterRadius cStar certifiedEndpointPair.2 +
            u * (b - endpointOuterRadius cStar certifiedEndpointPair.2))
          (endpointUnitAbscissa certifiedEndpointPair.2 +
            u * (t - endpointUnitAbscissa certifiedEndpointPair.2)))
        ((b - endpointOuterRadius cStar certifiedEndpointPair.2) *
            faceB
              (endpointOuterRadius cStar certifiedEndpointPair.2 +
                s * (b - endpointOuterRadius cStar certifiedEndpointPair.2))
              (endpointUnitAbscissa certifiedEndpointPair.2 +
                s * (t - endpointUnitAbscissa certifiedEndpointPair.2)) +
          (t - endpointUnitAbscissa certifiedEndpointPair.2) *
            faceT
              (endpointOuterRadius cStar certifiedEndpointPair.2 +
                s * (b - endpointOuterRadius cStar certifiedEndpointPair.2))
              (endpointUnitAbscissa certifiedEndpointPair.2 +
                s * (t - endpointUnitAbscissa certifiedEndpointPair.2))) s)
    (hsecond : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt
        (fun u ↦
          (b - endpointOuterRadius cStar certifiedEndpointPair.2) *
              faceB
                (endpointOuterRadius cStar certifiedEndpointPair.2 +
                  u * (b - endpointOuterRadius cStar certifiedEndpointPair.2))
                (endpointUnitAbscissa certifiedEndpointPair.2 +
                  u * (t - endpointUnitAbscissa certifiedEndpointPair.2)) +
            (t - endpointUnitAbscissa certifiedEndpointPair.2) *
              faceT
                (endpointOuterRadius cStar certifiedEndpointPair.2 +
                  u * (b - endpointOuterRadius cStar certifiedEndpointPair.2))
                (endpointUnitAbscissa certifiedEndpointPair.2 +
                  u * (t - endpointUnitAbscissa certifiedEndpointPair.2)))
        ((b - endpointOuterRadius cStar certifiedEndpointPair.2) ^ 2 *
            faceBB
              (endpointOuterRadius cStar certifiedEndpointPair.2 +
                s * (b - endpointOuterRadius cStar certifiedEndpointPair.2))
              (endpointUnitAbscissa certifiedEndpointPair.2 +
                s * (t - endpointUnitAbscissa certifiedEndpointPair.2)) +
          2 * (b - endpointOuterRadius cStar certifiedEndpointPair.2) *
              (t - endpointUnitAbscissa certifiedEndpointPair.2) *
            faceBT
              (endpointOuterRadius cStar certifiedEndpointPair.2 +
                s * (b - endpointOuterRadius cStar certifiedEndpointPair.2))
              (endpointUnitAbscissa certifiedEndpointPair.2 +
                s * (t - endpointUnitAbscissa certifiedEndpointPair.2)) +
          (t - endpointUnitAbscissa certifiedEndpointPair.2) ^ 2 *
            faceTT
              (endpointOuterRadius cStar certifiedEndpointPair.2 +
                s * (b - endpointOuterRadius cStar certifiedEndpointPair.2))
              (endpointUnitAbscissa certifiedEndpointPair.2 +
                s * (t - endpointUnitAbscissa certifiedEndpointPair.2))) s) :
    0 ≤ weightedSelfDiscriminant r b t (4 / 5) := by
  let b₀ := endpointOuterRadius cStar certifiedEndpointPair.2
  let t₀ := endpointUnitAbscissa certifiedEndpointPair.2
  have hendpoint := weightedSelfExceptional_endpoint_mem
  have hb₀ : b₀ ∈ Icc ((29 : ℝ) / 40) (3 / 4) := ⟨hendpoint.1, hendpoint.2.1⟩
  have ht₀ : t₀ ∈ Icc ((-209 : ℝ) / 256) (-13 / 16) :=
    ⟨hendpoint.2.2.1, hendpoint.2.2.2⟩
  have hb : b ∈ Icc ((29 : ℝ) / 40) (3 / 4) := ⟨hbLower, hbUpper⟩
  have ht : t ∈ Icc ((-209 : ℝ) / 256) (-13 / 16) := ⟨htLower, htUpper⟩
  have hgradientBZero : faceB b₀ t₀ = 0 := by
    apply hgradientB.unique
    simpa only [weightedSelfExceptionalFace, b₀, t₀] using
      weightedSelfDiscriminant_hasDerivAt_radius_endpoint
  have hgradientTZero : faceT b₀ t₀ = 0 := by
    apply hgradientT.unique
    simpa only [weightedSelfExceptionalFace, b₀, t₀] using
      weightedSelfDiscriminant_hasDerivAt_abscissa_endpoint
  have hfaceNonneg : 0 ≤ weightedSelfExceptionalFace b t := by
    apply value_nonneg_of_hessian_on_segment
      (f := weightedSelfExceptionalFace) (fb := faceB) (ft := faceT)
      (fbb := faceBB) (fbt := faceBT) (ftt := faceTT)
      (b₀ := b₀) (t₀ := t₀)
    · simpa only [weightedSelfExceptionalFace, b₀, t₀] using
        weightedSelfDiscriminant_endpoint_eq_zero
    · exact hgradientBZero
    · exact hgradientTZero
    · simpa only [b₀, t₀] using hfirst
    · simpa only [b₀, t₀] using hsecond
    · intro s hs
      have hbs := affine_mem_Icc hb₀ hb hs
      have hts := affine_mem_Icc ht₀ ht hs
      exact hfaceBBPos _ _ hbs.1 hbs.2 hts.1 hts.2
    · intro s hs
      have hbs := affine_mem_Icc hb₀ hb hs
      have hts := affine_mem_Icc ht₀ ht hs
      exact hfaceDeterminant _ _ hbs.1 hbs.2 hts.1 hts.2
  have hfaceLe : weightedSelfDiscriminant 1 b t (4 / 5) ≤
      weightedSelfDiscriminant r b t (4 / 5) := by
    apply value_le_of_hasDerivAt_nonpos_on_Icc
      (f := fun s ↦ weightedSelfDiscriminant s b t (4 / 5))
      (f' := fun s ↦ deriv (fun u ↦ weightedSelfDiscriminant u b t (4 / 5)) s)
      hrUpper
    · intro s hs
      have hc := one_lt_cStar_and_cStar_lt_two.1
      have hradialLowerPos : 0 < weightedSelfExceptionalRadialLower b := by
        rw [weightedSelfExceptionalRadialLower]
        norm_num at hbUpper ⊢
        nlinarith
      have hsPos : 0 < s := hradialLowerPos.trans_le (hrLower.trans hs.1)
      exact (weightedSelfDiscriminant_differentiableAt_radial hsPos.ne').hasDerivAt
    · intro s hs
      exact hradialNonpos s b t (hrLower.trans hs.1) hs.2
        hbLower hbUpper htLower htUpper
  exact (show 0 ≤ weightedSelfDiscriminant 1 b t (4 / 5) from hfaceNonneg).trans hfaceLe

end Bescovitch
