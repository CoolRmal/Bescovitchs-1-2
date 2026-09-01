# Formalization roadmap

The target is the exact theorem

```lean
Bescovitch.sigma_one_plane_le_s_star :
  sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ sStar
```

The comparator also checks the certified numerical consequence

```lean
Bescovitch.sStar_le_6934_div_10000 : sStar ≤ 6934 / 10000
```

The project separates the public statement from its proof. `Challenge.lean` contains every
transparent definition in the theorems and the two challenge holes. The identical
definitions in `Statement.lean` support the modular proof imported by `Solution.lean`. The
comparator recursively checks them, so neither `sigmaOne` nor `sStar` can be changed in the
solution.

Only declarations on a dependency path to this theorem belong in the project. In particular, a
lemma from Preiss's paper is formalized only when it is used by the six-point argument, the BPC
transfer, or the rectifiability transfer below.

## Definition layer

- `Challenge.lean`: lower density, countable rectifiability, `sigmaOne`, the exact endpoint, and the
  target theorem, stated directly for `EuclideanSpace ℝ (Fin 2)`.
- `Statement.lean`: the identical solution-side definitions required by the modular proof.
- `Rectifiability/Basic.lean`: pure one-unrectifiability and the basic rectifiability API.
- `BPC/Defs.lean`: set distance, straight measures, and the Besicovitch pair condition.

`lowerOneDensity` and the threshold of `ForcesOneRectifiability` are extended nonnegative reals, so
their comparison is direct. `sigmaOne` and `sStar` remain real because the endpoint geometry is
real-valued; the single `ENNReal.ofReal` in the definition of `sigmaOne` is the genuine boundary
between the two theories. The endpoint is constructed from an exactly isolated real-algebraic
pair; its decimal expansion is documentation only and never occurs in the theorem or its proof.

## Completed logical transfers

- `BPC/Defs.lean` gives the Besicovitch pair condition directly for straight measures.
- `BPC/Rectifiability.lean` proves that BPC below a density threshold forces one-dimensional
  rectifiability above that threshold.
- `BPC/SixPointTransfer.lean` proves BPC at every `beta > s` from the finite six-point property at
  `s`. The strict inequality is intentional and is enough to pass to the infimum.
- `Main/Bound.lean` combines these results to prove
  `SixPointFiniteProperty s -> sigmaOne (EuclideanSpace ℝ (Fin 2)) <= s` for positive `s < 1`.

These modules compile without `sorry` or nonstandard axioms. Thus the remaining work is confined to
the exact endpoint statement `SixPointFiniteProperty sStar`.

## Endpoint six-point theorem

- `SixPoint/Configuration.lean` defines normalized two-colour configurations and admissibility.
- `SixPoint/Packing.lean` defines supported radius assignments, union diameter, and score.
- The failure-tree modules route failure of the selected supports to three explicit slacks.
- `SixPoint/EndpointPacking.lean` reduces endpoint packing to one coordinate-free statement,
  `WeightedGeometricBound`.
- `SixPoint/WeightedReduction.lean` shortens the two sibling chords to exact length `cStar` without
  decreasing the weighted failure score.
- `SixPoint/WeightedChart.lean` puts the two chords into exact rational lens coordinates.
- `SixPoint/WeightedSelf.lean` reduces the crossed one-pair estimate to seven scalar radius bins.
- The mixed-certificate modules reduce the remaining chart inequality to exact rational polynomial
  inequalities.

Only endpoint nonnegativity is needed downstream. The 49-support lower obstruction, irreducibility
of the degree-54 eliminant, and uniqueness of the equality configuration are not dependencies of the
requested bound and will not be formalized unless a proof step genuinely needs them.

The endpoint certificate has three parts:

1. Seven self-interaction radius bins are checked by exact interval arithmetic and tensor Bernstein
   bounds.
2. Fifteen of the sixteen mixed lens charts are covered by adaptive rational boxes. Each retained
   leaf supplies a quadratic norm majorant whose dense polynomial has nonpositive Bernstein
   coefficients. Discarded leaves are proved disjoint from the feasible unit-disk lens.
3. The exceptional chart contains the equality configuration, so a strict polynomial bound cannot
   cover it. Exact transverse monotonicity moves a small neighbourhood to the unit-circle faces;
   negative definiteness in the antisymmetric directions then reduces the midpoint to the proved
   self inequality. The rest of that chart is covered by the strict certificate.

Six of the seven radius bins close by plain certificates. `[1933/5000, 2/5]` uses the exact integer
route and `[3/5, 7/10]` the Taylor route; `[2/5, 1/2]`, `[1/2, 3/5]`, `[4/5, 9/10]`, and `[9/10, 1]`
use the interval-Horner and Bernstein trees of `SixPoint/WeightedSelfIntervalCertificate.lean`. The
seventh bin `[7/10, 4/5]` is the exceptional one: it contains the sharp endpoint configuration, so
no strict polynomial bound covers it, and it is closed instead through the hybrid and
exceptional-face modules.

## Certificate cost

Kernel checking is the binding constraint on parts 2 and 3, and the two parts differ by orders of
magnitude.

A self radius bin is cheap. Its certificate is trivariate, its subdivision trees have a handful of
leaves, and `with_unfolding_all rfl` discharges a whole interval-Horner or Bernstein check in about
a minute.

A mixed lens chart is not. `weightedMixedTreeCheck` rebuilds `polynomialOfLeaf` at every leaf: a
six-variable dense polynomial of multidegree `(2, 2, 4, 2, 2, 4)`, hence 2025 coefficients, and only
then converts to the Bernstein basis. One leaf costs more than five kernel CPU-minutes, and the
fifteen generated trees hold about 5900 certified leaves between them, so checking them as written
is on the order of twenty CPU-days. The equality complement needs eighty further cell trees that
have not been generated.

Two candidate remedies were measured and rejected as insufficient on their own. `Nat.gcd` is
already accelerated in the kernel, so exact rational normalisation is not the bottleneck and an
unreduced `RawRat` representation buys little; a direct loop puts kernel `Rat` arithmetic at only
about six times kernel `Int` arithmetic, so an integer-scaled representation is worth a single-digit
factor.

The cost is structural rather than arithmetic, so the remedy has to be structural too. The leaf
polynomial is a fixed linear combination of about thirty-seven base polynomials whose coefficients
are elementary rational functions of the leaf data alone; the base polynomials themselves do not
depend on it. Converting those once on the root box and then descending the tree by exact
bisection of Bernstein coefficients replaces the per-leaf rebuild by one linear combination per
leaf, which is the reduction the remaining charts need.

All interval endpoints and certificate coefficients are rational. Bernstein conversion is itself
implemented and proved sound in Lean. Hashes, program exit codes, floating-point samples,
`native_decide`, and unchecked external computations are not proof objects.

## Why the endpoint suffices

`BPC/SixPointTransfer.lean` extracts two children near each of two approximate closest points,
normalizes the roots, applies the endpoint theorem, and absorbs the normalization error using
`beta > sStar`.

This direct argument uses six centres, not the older depth-two fourteen-centre detour. Straightness
turns the mass in each root ball into a sibling pair of large separation. The physical packing then
contradicts straightness by inclusion–exclusion unless the required leaking open set exists.

It therefore proves `BesicovitchPairCondition beta` for every `beta > sStar`; it does not need the
stronger endpoint assertion `BesicovitchPairCondition sStar`. The subsequent infimum argument gives
the exact non-strict conclusion
`sigmaOne (EuclideanSpace ℝ (Fin 2)) <= sStar`.

## Transfer to rectifiability

- `Rectifiability/Decomposition.lean`: rectifiable/pure decomposition and straight localization.
- `Rectifiability/Continuum.lean`: maximal disjoint selection, continuum surgery, and finite-length
  continuum rectifiability.
- `BPC/Rectifiability.lean`: BPC below a density threshold forces a positive rectifiable subset,
  hence countable rectifiability.
- `Main/Bound.lean`: for every `c > sStar`, choose `beta` strictly between them, apply both
  transfers, and pass to the infimum defining `sigmaOne`.

The geometric-measure-theory results absent from Mathlib are proved in the local `Measure` and
`Rectifiability` modules, rather than assumed. No custom axioms are introduced.

## Verification gates

Each milestone is built and pushed separately. The final gate requires:

1. a clean `lake build` and a separate build of `Challenge.lean`;
2. exactly the two requested holes in `Challenge.lean`, and none in the solution dependency graph;
3. no `native_decide`, `Lean.ofReduceBool`, or custom axioms;
4. only `propext`, `Quot.sound`, and `Classical.choice` in the proved theorem;
5. every Lean file below 1,500 lines and ordinary style/lint checks passing;
6. the upstream Lean comparator passing on Linux.
