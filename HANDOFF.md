# Retargeting to `sigmaOne <= 6934 / 10000`

This file is a working checklist for the change of target recorded in `DEVELOPMENT_PLAN.md`.
It is written so that the remaining work can be carried out mechanically, with `lake build` as
the arbiter at every step.

## Why the target changed

Certifying `sigmaOne <= sStar` needs the six-point endpoint to be attained exactly. The weighted
score is then zero at the extremal configuration, so every finite certificate has to separate a
tight inequality and the existing ones carry a margin of `10 ^ -8`. At `6934 / 10000` the same score
has a margin of about `3 * 10 ^ -3`, and the extremal configuration is no longer tight, so the
exceptional chart, the equality complement and the exceptional self bin disappear outright.

Measured, so that none of it is re-litigated:

- The bound still holds at `6934 / 10000` with the existing `endpointLambda` and `endpointMu`; the
  sampled maximum of the weighted score is about `-0.23`. The weights need not be re-derived.
- Interval arithmetic on the cleared leaf polynomial certifies **none** of the hundred and thirty
  leaves of the smallest chart, overshooting by between `+13` and `+275`.
- Interval arithmetic on the score itself is first-order accurate in the box width, so it cannot
  use the larger margin either: it needs widths near `0.009` across six unit-sized coordinates.
  A search at `6934 / 10000` passed three hundred thousand boxes without closing one sign pair.
- The quadratic majorants and the Bernstein basis are therefore not negotiable. They are what
  makes the certificate second-order accurate, which is why the current trees need only about
  five thousand nine hundred leaves at a margin of `10 ^ -8`.

## Step 1 --- parameterise the chord

The routing and exclusion modules use only two facts about `cStar`:
`one_lt_cStar_and_cStar_lt_two` and `cStar_mem_isolation_box`. Everything else is `nlinarith`
over those bounds.

Retargeting `SixPoint/SiblingTangent.lean` (817 lines, 216 occurrences, 14 uses of the isolation
box) **compiles with zero errors at the new chord**, once the shim also supplies `cStar_pos`.
Every `nlinarith` in it goes through unchanged. It is the one routing module low enough in the
import graph to be tested in isolation, which is why it is the honest data point.

The remaining modules were each rewritten the same way and compiled alone. That test is
confounded --- a module high in the graph still refers to neighbours stated with the old chord, and
those broken references cascade into spurious `linarith` failures --- but the modules with no
cross-module mismatch give a clean reading:

| module | lines | genuine failures |
|---|---|---|
| `SiblingTangent` | 817 | 0 |
| `RootEdge` | 1267 | 1 |
| `RowColumnRescue` | 1230 | 4 |
| `LensEndpointBalancedE0S0` | 1026 | 1 |
| `RootEdgeType12` | 684 | 7 |
| `BlueChildSwap` | 231 | 1 |

Fourteen failures across five thousand lines, and most of them are explained by a detail the
rewrite missed: several of these files also contain the chord as a **decimal literal**
(`13866128436518096 / 10 ^ 16`, forty-three occurrences across seventeen files), so after renaming
the constant they mix two different chords. Replace those literals as well.

The conclusion to work from: the routing layer retargets close to free, with of order tens of
numeric repairs, and it must be done **bottom-up in import order** so that each module's
dependencies already speak of the new chord. Do not judge a module by compiling it in isolation.

It has to be done as a **substitution, not a parameterisation**. Making the chord a variable with
an abstract box hypothesis does not work: the separators are proved by `nlinarith` over the box
*numerals*, and an abstract box gives it nothing to compute with. Nor can one box serve both
chords --- widening `SiblingTangent`'s box to `(1.386, 1.399)`, which covers `cStar` and `barC`
together, turns its zero failures into forty-eight. Each chord needs its own tight box, and with
its own tight box each works.

So: replace `cStar` by `barC` and `sStar` by `barS` outright in the routing, weighted and
certificate layers, and let the mismatches propagate outward module by module. Order the work by
the import graph. `SixPoint/RationalChord.lean` already supplies the constants and the shim
lemmas, under the names the routing layer expects.

Leave the exact-endpoint machinery alone --- `Statement.lean`, `SixPoint/AlgebraicBasic.lean`,
`SixPoint/EndpointExtremizer.lean`, `SixPoint/EndpointWeights.lean`,
`Certificates/EndpointIsolation.lean`, `Certificates/EndpointBridge.lean` and
`Certificates/EndpointTightBounds.lean`. It is self-contained, it keeps proving
`sStar <= 6934 / 10000`, and `endpointLambda` and `endpointMu` keep their values: the weights are
still valid multipliers at the larger chord, so they are not re-derived.

The certificate data modules under `SixPoint/WeightedMixedCertificateData` and
`SixPoint/WeightedSelfCertificateData` are specific to the old chord and cannot be converted by
substitution; they have to be regenerated, as in step 2.
Forty-one files mention the constants outside the exact-endpoint machinery, about twenty thousand
lines. The routing modules to convert, largest first, are `RootEdge`, `RowColumnRescue`,
`SiblingIncidenceLedger`, `LensEndpointBalancedE0S0`, `SiblingIncidence`, `SiblingTangent`,
`RootEdgeType12`, `RootEdgeFailureTree`, `SiblingLensS0S3`, `SiblingLensE1S0`, `SiblingLens`,
`BlueChildSwap`, `EndpointFailureClosed`, `EndpointPacking`, `WeightedChart`.

`SixPoint/FiniteProperty.lean`, `SixPoint/WeightedReduction.lean` and `Main/Bound.lean` mention
the endpoint nowhere and need no change: `SixPointFiniteProperty.sigmaOne_plane_le` is already
generic in `s`.

## What the retarget already gave

The retarget is complete and the project builds green at `barC = 3467 / 2500`. The self side then
turned out to need far less than expected:

- The fourteen curvature enclosures recompute by interval arithmetic over the new endpoint data,
  and `weightedSelfKappaBoxes_certify` and `weightedSelfDirectQCertificates` both go through, so
  `Q >= 0` is certified on all seven radius bins.
- **The subdivision trees carry over unchanged.** The chord moved by only `1.4 * 10 ^ -4`, and the
  `-P` and discriminant certificates of the second bin still hold on the old trees at the same
  cost. So the self bins need no regeneration, and the bin `[7/10, 4/5]` is no longer exceptional:
  above the sharp constant it carries no equality configuration, so a plain certificate covers it.

That leaves the mixed root boxes as the only certificates to generate.

## Step 2 --- regenerate the certificates

The trees under `SixPoint/WeightedMixedCertificateData` and the self-bin trees are specific to the
old chord and must be regenerated. There is no generator in the repository; the one that produced
them is outside it.

Write the generator in Lean and run it with `#eval`. The pattern is proved out: for the
interval-Horner certificates it is enough to mirror the checker's own leaf test --- for
`intervalPolynomialSubdivisionCertifiesNonnegative` that is `0 <= (P.evalOn X Y Z).lower` --- and
recurse on `leftHalf` and `rightHalf`. Choosing the coordinate whose worse half has the largest
lower bound beats splitting the widest coordinate: on the exceptional face-Hessian determinant it
cut the tree from 3592 leaves to 2371.

For a mixed leaf the generator must also choose the stored data, and there is a natural choice at
the box centre `x*` that makes the majorant tight there:

- the six tangent parameters `rho i` as the norm of the corresponding cleared difference at
  `x*`, since the quadratic tangent is exact where it is taken;
- the four support slopes from the unit vector `p j x* / ‖p j x*‖`: a unit vector `(nx, ny)` has
  stereographic parameter `ny / (1 + nx)`;
- the four disk slacks at zero, which is always admissible.

Round each to a rational with denominator `4096`, the leaf data format. Search in floating point
with a safety margin --- only the final tree is verified exactly, in Lean --- and bisect
round-robin by depth, matching `weightedMixedSplitCoordinate`.

## Step 3 --- verify

Build the certificate modules **one target per `lake build` invocation**. Eight in parallel held
about seven gigabytes between them, drove the machine under three hundred megabytes free, and each
process then got a tenth of a core; the same module built alone finished in sixty-eight seconds.
`lake` has no `-j` short option here.

`lake env lean` blocks on the lake lock while a build runs. To run a generator alongside a build,
invoke the toolchain's `lean` directly with `LEAN_PATH` set over the package build
directories `.lake/packages/*/.lake/build/lib/lean` and `.lake/build/lib/lean`.

## The retargeted constants

`barC = 3467 / 2500` and `barB = 2873744161801660 / 10 ^ 15`.  The seven quantities of
`weightedSelfEndpointBox` follow, and only three of them change: `A` depends on `B` alone, and
the two weights are untouched.

| slot | quantity | value at the rational chord |
|---|---|---|
| 0 | `c` | `3467 / 2500` exactly |
| 1 | `B` | `2873744161801660 / 10 ^ 15` exactly |
| 2 | `D = 4c^2 - 2c - B` | `102275639909917 / 50000000000000` exactly |
| 3 | `A = sqrt((B^2-1)/2)` | `1.90504665395484808450...` (unchanged) |
| 4 | `C = sqrt((B^2+D^2)/2 - c^2)` | `2.07317385125829814362...` |
| 5 | `lambda` | unchanged |
| 6 | `mu` | unchanged |

with `A ^ 2 = 18146013768722813524642946889 / 5000000000000000000000000000` and
`C ^ 2 = 10745124543852910288258946889 / 2500000000000000000000000000`.

Slots 0, 1 and 2 are rational, so their box memberships are `norm_num`.  Slots 3 and 4 need
rational bounds on a square root, which follow from `Real.sqrt_le_sqrt` and `Real.sq_sqrt` against
the exact squares above.  The five tight-bound lemmas that `endpointCertificateInput_mem` cites
are stated for the old endpoint and have to be replaced by these.

## Why 6934 and not more

The routing separators cap how far above the sharp constant the argument can be pushed. One of
them, in `RootEdgeType12`, reduces to

```
c * 219977687 < (2 * c - 1) * 172000000  →  False
```

which holds only for `c < 1.386850`, that is `s < 0.693425`. At `6934 / 10000` it passes with a
relative margin of `1.9 * 10 ^ -5`; at `69345 / 100000` and above it fails. Do not raise the
threshold.

## Where the proof now stands

`Main/RationalBound.lean` reduces the target to **ten** `WeightedMixedRootBoxBound`s and nothing
else:

```lean
sigmaOne_plane_le_barS_of_mixed_root_box_bounds :
  (ten mixed root box bounds) → sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 6934 / 10000
```

Above the sharp constant the equality chart is not exceptional, so it needs no separate treatment,
and the self inequality --- which existed only to close that chart's central cell --- is no longer
on the dependency path at all. The seven radius bins are kept but are not needed for the theorem.

Nine of the ten charts have generated trees, restored in
`SixPoint/WeightedMixedCertificateData`, and trees of this kind still certify at the new chord.
`SixPoint/WeightedMixedCharts` holds a module per chart running its check. The tenth,
`Cap1Cap1NegNeg`, never had an ordinary tree because the equality machinery used to cover it, and
is the one thing left to generate.

A first generator is written: it chooses the stored data at each box centre by the geometric rule
above and bisects round-robin, mirroring `weightedMixedSplitCoordinate`. It compiles and runs, but
at a fuel of fourteen it does not close the equality chart --- unsurprising, since that chart is
where the score comes closest to zero and the existing trees elsewhere run to depths of twenty and
beyond. Raise the fuel, and expect that chart to need the deepest subdivision of the sixteen.

## Gates that still apply

Unchanged from `DEVELOPMENT_PLAN.md`: no `native_decide`, no `Lean.ofReduceBool`, no custom
axioms; only `propext`, `Quot.sound` and `Classical.choice` in the finished theorem; every file
under 1500 lines and 100 columns; and exactly one hole, in `Solution.lean`.
