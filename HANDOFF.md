# Retargeting to `sigmaOne <= 699 / 1000`

This file is a working checklist for the change of target recorded in `DEVELOPMENT_PLAN.md`.
It is written so that the remaining work can be carried out mechanically, with `lake build` as
the arbiter at every step.

## Why the target changed

Certifying `sigmaOne <= sStar` needs the six-point endpoint to be attained exactly. The weighted
score is then zero at the extremal configuration, so every finite certificate has to separate a
tight inequality and the existing ones carry a margin of `10 ^ -8`. At `699 / 1000` the same score
has a margin of about `0.2`, and the extremal configuration is no longer tight at all, so the
exceptional chart, the equality complement and the exceptional self bin disappear outright.

Measured, so that none of it is re-litigated:

- The bound still holds at `699 / 1000` with the existing `endpointLambda` and `endpointMu`; the
  sampled maximum of the weighted score is about `-0.23`. The weights need not be re-derived.
- Interval arithmetic on the cleared leaf polynomial certifies **none** of the hundred and thirty
  leaves of the smallest chart, overshooting by between `+13` and `+275`.
- Interval arithmetic on the score itself is first-order accurate in the box width, so it cannot
  use the larger margin either: it needs widths near `0.009` across six unit-sized coordinates.
  A search at `699 / 1000` passed three hundred thousand boxes without closing one sign pair.
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

For a mixed leaf the generator must also choose the stored data: `rho` from the norm of the
corresponding cleared difference at the box centre, the support slopes from the centre direction,
and the disk slacks from the constraint residuals.

## Step 3 --- verify

Build the certificate modules **one target per `lake build` invocation**. Eight in parallel held
about seven gigabytes between them, drove the machine under three hundred megabytes free, and each
process then got a tenth of a core; the same module built alone finished in sixty-eight seconds.
`lake` has no `-j` short option here.

`lake env lean` blocks on the lake lock while a build runs. To run a generator alongside a build,
invoke the toolchain's `lean` directly with `LEAN_PATH` set over the package build
directories `.lake/packages/*/.lake/build/lib/lean` and `.lake/build/lib/lean`.

## Gates that still apply

Unchanged from `DEVELOPMENT_PLAN.md`: no `native_decide`, no `Lean.ofReduceBool`, no custom
axioms; only `propext`, `Quot.sound` and `Classical.choice` in the finished theorem; every file
under 1500 lines and 100 columns; and exactly one hole, in `Solution.lean`.
