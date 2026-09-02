# Plan: `1/2 ≤ sigmaOne (EuclideanSpace ℝ (Fin 2))`

Written 2026-09-02, before any code, after the literature review below.

## What must be proved

`sigmaOne` is `sInf {β ≥ 0 | ForcesOneRectifiability β}`. By `le_csInf` (the set is nonempty —
`forcesOneRectifiability_plane_of_gt`), it suffices that **no threshold below 1/2 forces
rectifiability**: for every `β < 1/2` there is a measurable `s ⊂ ℝ²` with `μH[1] s < ∞`, lower
density `≥ β` at `μH[1]`-a.e. point of `s`, and `¬ IsCountablyOneRectifiable s`.

One set serves every `β < 1/2`: a set with lower density `≥ 1/2` at *every* point.

## Literature

- Besicovitch 1938 suggested the set; **Dickinson 1939** (Math. Ann. 116, "Study of extreme
  cases with respect to the densities of irregular linearly measurable plane sets of points",
  Thm 2 §17) proved lower density 1/2 a.e. De Lellis–Glaudo–Massaccesi–Vittone 2024 cite exactly
  this for the lower bound `σ̄ ≥ 1/2`.
- **Capdevila, arXiv:2607.05206 (July 2026)** gives a modern self-contained account and is the
  source used here. Its planar construction is followed verbatim; its proofs are simplified where
  we need less than it proves.
- The four-corner Cantor set (the standard purely unrectifiable set) does **not** work: its lower
  density is about 0.35. Exactly 1/2 needs Besicovitch's construction.

## The set

```
α n = 2^(-n²)      β n = α n / n
f n x = ±β n       square wave of period 2 α n      (−β on even cells, +β on odd cells)
g x   = Σ_n f n x  (uniformly convergent)
Π     = { (x, g x) : x ∈ [0,1] } ⊂ EuclideanSpace ℝ (Fin 2)
```
Level-`n` cells: `I n i = [i α n, (i+1) α n)`. The coarse grid refines: `α m` is a multiple of
`α n` for `m < n`, so every level-`m` boundary is a level-`n` boundary.

Two estimates carry everything (Capdevila eq. 1, 2):

- **(E1)** `x, y` in the same level-`n` cell ⟹ `|g x − g y| ≤ (4/n) α (n+1)`.
- **(E2)** `x, y` in *adjacent* level-`n` cells ⟹ `|g x − g y| ≥ α n / n`.

## The lemma graph

```
A. cells + g + (E1), (E2)                                              ~300 lines
B. μH[1] (Π '' A) = volume A  for A ⊆ [0,1]                              ~400
   ≥ : first-coordinate projection is 1-Lipschitz   (LipschitzWith.hausdorffMeasure_image_le,
       hausdorffMeasure_real)
   ≤ : cover Π '' U by cylinders over level-n cells for open U, sum of diameters
       ≤ (1+ε_n)·volume U; then outer regularity (Set.exists_isOpen_lt_of_lt).
       Holds for arbitrary A as outer measures.  Gives μH[1] Π = 1, in particular finite.
C. lower density ≥ 1/2 at every point of Π over (0,1)                    ~500
   Capdevila part (C): for small r pick n with α(n+1)λ_n ≤ r ≤ α n λ(n−1); the graph over
   the cell ∩ ball(x, r/λ_n) lies in ball(Π x, r) by (E1), and that cell piece contains an
   interval of length ≥ r/λ_n; apply B (≥).   λ_n = √(1+(4/n)²) → 1.
D. pure unrectifiability                                                 ~1100
   D1 (reduction, ~400): Lipschitz f : ℝ → ℝ² with μH[1] (range f ∩ Π) > 0 gives A ⊆ [0,1]
       with volume A > 0 on which g is Lipschitz.
       Rademacher (LipschitzWith.ae_differentiableAt); where f₁' = 0 the image of f₁ is null
       (addHaar_image_eq_zero_of_det_fderivWithin_eq_zero) hence its graph piece is μH[1]-null
       by B(≤); where f₁' ≠ 0, the partition lemma
       (exists_partition_approximatesLinearOn_of_hasFDerivWithinAt) gives pieces on which f₁ is
       injective with |f₁ t − f₁ t'| ≥ c|t − t'|, so g∘f₁ = f₂ Lipschitz transfers to g on the
       image.  No area formula, no projection theorem.
   D2 (~500, DONE up to the final recursion): if g is L-Lipschitz on A then volume A = 0.
       The plan above (one-sided holes chosen per boundary) does NOT compound: a single hole is a
       1/n fraction of any ball and sup-over-cells bounds refuse to multiply.  What works instead:
       (a) Avoid.lean — by (E2) A cannot meet both sides of a level-n grid point within
           margin L n = cellLength n/(2n(L+1))  [not_both_sides];
       (b) Density.lean — a Lebesgue density point of A therefore cannot lie within margin of a
           level-n grid point for infinitely many n (the ball of radius 2·margin about it contains
           a hole of relative size 1/4, so the density along those radii is ≤ 3/4); hence almost
           every point of A eventually lies in
             avoid L n = {x | ∀ i, margin L n ≤ |x - i·cellLength n|}   (BOTH sides)
           [ae_eventually_mem_avoid];
       (c) Zero.lean — volume (Icc 0 1 ∩ ⋂ₙ avoid L (N+n)) = 0 by Capdevila's nested recursion,
           which now applies verbatim because the avoided sets are two-sided and A-independent:
           inside each level-M cell the surviving set is order-connected
           [ordConnected_avoid_inter_cell], the level-(M+1) grid points inside it carve
           ≥ ℓ/cellLength − 3 disjoint gaps of width 2·margin, so
             volume ≤ (1 − 1/((M+1)(L+1)))·volume + summable error,
           and tendsto_zero_of_recursive finishes.
   D3 (~100): μH[1] (Π \ ⋃ range f i) ≥ μH[1] Π − Σ 0 = 1 > 0.
E. assembly                                                              ~100
   Π measurable (graph of a Borel function); finite measure; density; not rectifiable ⟹
   ¬ ForcesOneRectifiability β for β < 1/2 ⟹ 1/2 ≤ sInf via le_csInf.
```

Estimated total 2,500–3,500 lines. Risk is concentrated in D2 and C.

## Status (2026-09-02, later)

Built and pushed: Graph (A), Plane + Cover + Hull (B, with constant 2 — the sharp constant 1 is
never needed), Measurable, Avoid + Density (D2 steps a–b), Recursion.  ~1,400 lines.
Remaining: Zero (D2 step c), Reduction (D1), LowerDensity (C), assembly (E).

## Mathlib tools, verified present at this project's revision

`LipschitzWith.ae_differentiableAt`, `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`,
`ApproximatesLinearOn.injOn`, `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`,
`lintegral_abs_det_fderiv_eq_addHaar_image` (not needed on the chosen route),
`hausdorffMeasure_real`, `LipschitzWith.hausdorffMeasure_image_le`, `Set.exists_isOpen_lt_of_lt`,
`Real.tendsto_sum_range_one_div_nat_succ_atTop`.

Absent from Mathlib: any notion of rectifiability, any purely unrectifiable set, the area
formula for curves, the Besicovitch–Federer projection theorem. The plan uses none of them.

## What is deliberately not proved

The upper density bound `≤ 1/2` (Capdevila part D) and the sharp `μH[1] (Π '' A) = volume A`
for all Borel `A` beyond what B needs.  Neither is required for the lower bound on `sigmaOne`.
