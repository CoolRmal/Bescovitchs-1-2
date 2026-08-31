# Formalization plan

The target is the exact theorem

```lean
Bescovitch.sigma_one_plane_le_s_star : sigmaOne Plane ≤ sStar
```

The project separates the public statement from its proof. `Challenge.lean` imports the transparent
definitions and contains the one permitted challenge hole. `Solution.lean` repeats the same theorem
header and imports the proof. The comparator recursively checks every definition appearing in the
theorem type, so neither `sigmaOne` nor `sStar` can be changed in the solution.

## Definition layer

- `Geometry/Basic.lean`: the Euclidean plane and elementary metric API.
- `Measure/Density.lean`: normalized lower one-dimensional Hausdorff density.
- `Rectifiability/Defs.lean`: countable and pure one-unrectifiability.
- `BPC/Defs.lean`: set distance, straight measures, and the Besicovitch pair condition.
- `Sigma/Defs.lean`: the rectifiability property and `sigmaOne`.
- `SixPoint/AlgebraicConstant.lean`: the isolated radical system defining `sStar`.
- `Statement.lean`: the trusted re-export used by both comparator files.

Every infimum in this layer will be accompanied by the nonemptiness and boundedness facts needed to
rule out default values. In particular, the proof must construct the isolated endpoint pair defining
`sStar`; a decimal approximation or an empty candidate set is not accepted.

## Finite six-point theorem

- `SixPoint/Configuration.lean`: normalized two-colour configurations and admissibility.
- `SixPoint/Packing.lean`: supported radius assignments, union diameter, and score.
- `SixPoint/FailureTree.lean`: exact routing of failure of the nine selected supports to three
  nonnegative slacks.
- `SixPoint/Self.lean`: the one-pair weighted inequality.
- `SixPoint/Contraction.lean`: the mixed contraction inequality.
- `SixPoint/Endpoint.lean`: every admissible configuration has a nonnegative nine-support packing at
  `sStar`.

Only endpoint nonnegativity is needed downstream. The 49-support lower obstruction, irreducibility
of the degree-54 eliminant, and uniqueness of the equality configuration are not dependencies of the
requested bound and will not be formalized unless a proof step genuinely needs them.

The source proof uses outward-rounded interval certificates in several leaves. Their formalization
must consist of a checked rational interval evaluator plus complete certificate data, or a shorter
analytic replacement. Hashes, program exit codes, and floating-point samples are not proof objects.

## Direct transfer to BPC

- `BPC/SixPointTransfer.lean`: extract two children near each of two approximate closest points,
  normalize the roots, apply the endpoint theorem, and absorb the normalization error using
  `β > sStar`.

This direct argument uses six centres, not the older depth-two fourteen-centre detour. Straightness
turns the mass in each root ball into a sibling pair of large separation. The physical packing then
contradicts straightness by inclusion–exclusion unless the required leaking open set exists.

## Transfer to rectifiability

- `Rectifiability/Decomposition.lean`: rectifiable/pure decomposition and straight localization.
- `Rectifiability/Continuum.lean`: maximal disjoint selection, continuum surgery, and finite-length
  continuum rectifiability.
- `BPC/Rectifiability.lean`: BPC below a density threshold forces a positive rectifiable subset, hence
  countable rectifiability.
- `Main/Bound.lean`: for every `c > sStar`, choose `β` strictly between them, apply both transfers,
  and pass to the infimum defining `sigmaOne`.

The cited geometric-measure-theory results absent from Mathlib are proof obligations here, not
assumptions. No custom axioms will be introduced.

## Verification gates

Each milestone is built and pushed separately. The final gate requires:

1. a clean `lake build` and a separate build of `Challenge.lean`;
2. exactly one `sorry`, in `Challenge.lean`, and none in the solution dependency graph;
3. no `native_decide`, `Lean.ofReduceBool`, or custom axioms;
4. only `propext`, `Quot.sound`, and `Classical.choice` in the proved theorem;
5. every Lean file below 1,500 lines and ordinary style/lint checks passing;
6. the upstream Lean comparator passing on Linux.
