# Bescovitch's 1/2

A Lean 4 and Mathlib project for the proposed bound

\[
\sigma_1(\mathbb R^2) \le s_*,
\qquad
s_* = 0.6933064218259048726\ldots,
\]

where `sStar` is defined by an exact isolated radical system rather than by a decimal.

The formalization is being developed in pushed, buildable milestones. The current solution theorem
still has a development hole and must not yet be treated as a completed proof. See
[`DEVELOPMENT_PLAN.md`](DEVELOPMENT_PLAN.md) for the proof graph and verification criteria.

## Comparator layout

- `Challenge.lean` contains the public theorem with the single challenge hole.
- `Solution.lean` repeats the same theorem independently.
- `Bescovitch/Statement.lean` re-exports the transparent definitions shared by both sides.
- `comparator.json` permits only `propext`, `Quot.sound`, and `Classical.choice`.

The comparator configuration intentionally has no `definition_names` escape hatch: the definitions
reachable from the theorem statement are compared recursively.

## Build

```sh
lake exe cache get
lake build
lake env lean Challenge.lean
```

The project is pinned to Lean and Mathlib `v4.32.0`, matching the comparator toolchain.
