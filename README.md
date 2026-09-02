# Besicovitch's 1/2-problem: a verified bound

A Lean 4 + Mathlib formalization of

$$
\frac{1}{2} \le \sigma_1(\mathbb{R}^2) \le \frac{6934}{10000} = 0.6934 .
$$

The upper bound improves the published $0.7$; the lower bound is Besicovitch's classical one,
formalized here so that the threshold is pinned to an explicit interval rather than merely
bounded above. Both proofs are complete: `Solution.lean` contains no `sorry`, and every compared
theorem depends on exactly the three axioms `propext`, `Classical.choice` and `Quot.sound`.

```
theorem Besicovitch.sigma_one_plane_le_6934_div_10000 :
    sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 6934 / 10000
theorem Besicovitch.one_half_le_sigma_one_plane :
    (1 / 2 : ℝ) ≤ sigmaOne (EuclideanSpace ℝ (Fin 2))
```

📄 **[`paper/gram-certificate-bound.pdf`](paper/gram-certificate-bound.pdf)** — the proof of this
bound, and the argument for the choice of constant.
[`paper/six-point-constant.pdf`](paper/six-point-constant.pdf) is background: the six-point
analysis that produces the sharp constant $s_*$ discussed below.

## The problem

For a Borel set $E \subset \mathbb{R}^2$ with $\mathcal{H}^1(E) < \infty$, the **lower density**
at a point $x$ is

$$
\Theta^1_*(E,x) = \liminf_{r \downarrow 0} \frac{\mathcal{H}^1(E \cap B(x,r))}{2r},
$$

normalized by the diameter $2r$, so a straight segment has density $1$ at its interior points.
**Besicovitch's 1/2 conjecture** asserts:

> if $\mathcal{H}^1(E) < \infty$ and $\Theta^1_*(E,x) > 1/2$ for $\mathcal{H}^1$-almost every
> $x \in E$, then $E$ is countably 1-rectifiable.

Writing $\sigma_1(\mathbb{R}^2)$ for the *infimum* of the thresholds $\beta \ge 0$ such that
$\Theta^1_* \ge \beta$ almost everywhere forces countable 1-rectifiability, the conjecture is
$\sigma_1(\mathbb{R}^2) = 1/2$. It is an infimum, not a minimum: nothing here claims it is attained.

| year | bound | source |
|---|---|---|
| 1928 | $1 - 10^{-2576}$ | Besicovitch |
| 1938 | $3/4$ | Besicovitch |
| 1992 | $(2+\sqrt{46})/12 = 0.73186\ldots$ | Preiss and Tišer |
| 2024 | $0.7$ | De Lellis, Glaudo, Massaccesi and Vittone |
| **here** | $\mathbf{0.6934}$ | **this repository, machine-checked** |

De Lellis, Glaudo, Massaccesi and Vittone recast the question as a family of finite-dimensional
optimization problems: the passage from a density hypothesis to rectifiability routes through a
purely finite statement about disjoint balls centred at finitely many points. **The optimization
approach here is inspired by theirs.**

## What is compared

Three statements, all proved in `Solution.lean`:

- `sigma_one_plane_le_6934_div_10000` — the upper bound.
- `forcesOneRectifiability_plane_of_gt` — every threshold strictly above $0.6934$ forces
  rectifiability: genuine admissible thresholds, so the bound on the infimum is not vacuous.
- `one_half_le_sigma_one_plane` — the lower bound. Together with the first it pins
  $\sigma_1(\mathbb{R}^2)$ to $[1/2, 0.6934]$; in particular the infimum is not the value Lean
  assigns to an empty set.

`sigmaOne` is an infimum, not a minimum: nothing here claims it is attained.

## The lower bound

$\sigma_1(\mathbb{R}^2) \ge 1/2$ needs a set of finite positive length that is *not* countably
rectifiable yet has lower density at least $1/2$ almost everywhere. Besicovitch proposed one in
1938 and Dickinson proved its properties in 1939; the formalization follows Capdevila's 2026
account. The set is the graph over $[0,1]$ of

$$
g = \sum_{n \ge 1} f_n, \qquad f_n = \text{a square wave of period } 2 \cdot 2^{-n^2}
\text{ and amplitude } 2^{-n^2}/n .
$$

Two estimates carry everything: inside a level-$n$ cell $g$ varies by at most
$4 \cdot 2^{-(n+1)^2}/(n+1)$, and across a level-$n$ cell boundary it jumps by at least
$2^{-n^2}/n$. The Hausdorff measure of the graph over any set lies between the Lebesgue measure of
the base and twice it; the lower density is at least $1/2$ at every interior point because at
every scale the graph is a near-flat segment through the point extending at least the radius to
one side; and no Lipschitz curve meets the graph in positive measure, because a set on which $g$
is Lipschitz cannot straddle a jump — the Lebesgue density theorem then forces almost every such
point to stay clear of the grid on both sides at all fine levels, and the nested cell recursion,
driven by $\sum 1/n = \infty$, makes that set null.

The proof uses no projection theorem, no tangent theory and no area formula: it is elementary
throughout, which is what made it feasible to formalize. The modules live in
[`Besicovitch/Example/`](Besicovitch/Example/).

## Why 0.6934 and not the sharp constant

This is the first question a reader should ask, so it is answered up front.

The finite problem this development solves — the **two-colour, six-centre** instance — has an
exact optimal constant,

$$
\theta_6 = s_* = 0.693306421825904872690678414403710951\ldots,
$$

an algebraic number pinned by an isolated pair of radical equations. The formalized bound is
$9.36 \times 10^{-5}$ above it. That gap is not a gap in the mathematics; it is the price of
making the certificates finite.

**Tightness destroys the certificates.** At $s_*$ the extremal configuration is *attained*: a
half-turn pair of chords at which three structurally different packing mechanisms tie
simultaneously. The weighted score that must be bounded above by zero therefore equals exactly
zero at an interior point, with vanishing gradient. A certificate for a non-strict bound at a
degenerate maximum has to resolve the geometry to the precision of the degeneracy. In practice
the margin away from the extremiser was about $10^{-8}$, and the adaptive subdivision needed near
the tie grew without bound — on one of the ten coordinate charts the score is identically zero at
the extremiser, so no strict certificate of the assumed shape exists there at all.

**Moving the chord breaks every tie at once.** With

$$
c = \frac{3467}{2500} = 1.3868, \qquad s = \frac{c}{2} = 0.6934,
$$

the three mechanisms no longer agree, the extremal configuration is infeasible, and the score
acquires a uniform negative margin of about $5.8 \times 10^{-4}$ — four orders of magnitude more
room. That is what lets a *small, fixed* family of thirty certificates replace an unbounded
adaptive search.

**The constant is also bounded from above.** The routing separators that prune the case tree are
themselves inequalities in the chord and fail once $c$ exceeds about $1.386850$. So the admissible
window is narrow: above $2s_*$ to break the tie, below that ceiling to keep the routing. The value
$6934/10000$ sits inside it.

A companion theorem, `sStar_le_6934_div_10000`, records that the exact endpoint does lie below the
rational target, so the two statements are consistent.

## How the proof works

The failure tree reduces the failure of all nine packings at a matched sibling endpoint to three
scalar slacks $q_1 \ge 0$, $q_2 > 0$, $q_3 > 0$. An algebraic identity says that for **any**
positive weights $\lambda, \mu$,

$$
q_1 + \lambda q_2 + \mu q_3 = \mathcal{W}_{c,\lambda,\mu}(e, p_1, p_2, w_1, w_2),
$$

so the weighted score is positive. The contradiction comes from bounding the same score *above*.
Because the identity holds for arbitrary weights, we take the small rationals

$$
\lambda = \frac{1}{12}, \qquad \mu = \frac{13}{14},
$$

which makes every downstream coefficient a small rational and removes the entire exact-endpoint
apparatus from the dependency path.

On a rectangle of second-child radii, six quadratic norm tangents, four radial secants and two
separation multipliers turn the score into a quadratic form in the five configuration vectors.
A rational $3 \times 5$ factor $F$, completed by elementary two-vector squares, dominates that
form:

$$
M = F^{\top} F + \sum_{i \lt j} \lvert \rho_{ij} \rvert
(e_i + \varepsilon_{ij} e_j)(e_i + \varepsilon_{ij} e_j)^{\top}
$$

is a sum of rank-one positive semidefinite matrices, so the Schur product theorem against the Gram
matrix of the five vectors cancels every inner product. What remains is a single exact rational
number $U$ per rectangle, and thirty rectangles cover every feasible pair of radii.

The binding certificate is on $[7/10, 3/4] \times [4/5, 9/10]$, with

$$
U = -\frac{141718938311359411043}{245112420775950000000000} = -0.000578179\ldots < -\frac{1}{2000}.
$$

## Where a computer is used

The certificate parameters were found by an unverified numerical search and stored as exact
rationals with denominator $10^4$. **Nothing about how they were found enters the proof.** Lean
recomputes every coefficient from the stored data by exact rational arithmetic and checks the sign
conditions and $U \le -1/2000$ for all thirty records. Positive semidefiniteness is a *theorem*
proved from the rank-one decomposition, not a numerical test — there is no eigenvalue computation
anywhere.

Hashes, program exit codes, floating-point samples, `native_decide`, `Lean.ofReduceBool`, and
unchecked external computations are not used as proof objects.

## Build

```sh
lake exe cache get
lake build Solution Challenge
```

From a warm Mathlib cache this takes about **2.5 minutes wall / 12 CPU-minutes** in total. The
certificate-specific part is a small fraction of that:

| stage | cost |
|---|---|
| thirty certificate validity checks | 43 s |
| Gram certificate core | 7 s |
| band cover | 3 s |
| everything else (measure theory, routing, transfers) | remainder |

To check the result yourself:

```sh
echo 'import Solution
#print axioms Besicovitch.sigma_one_plane_le_6934_div_10000' > /tmp/check.lean
lake env lean /tmp/check.lean
```

which prints

```
'Besicovitch.sigma_one_plane_le_6934_div_10000' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The project is pinned to Lean and Mathlib `v4.32.0`.

## Layout

| path | contents |
|---|---|
| `Challenge.lean` | the problem statement, self-contained, with the theorem hole |
| `Solution.lean` | the proved theorem |
| `Besicovitch/Statement.lean` | the same definitions, for the modular development |
| `Besicovitch/SixPoint/GramCertificateCore.lean` | the local certificate theorem |
| `Besicovitch/SixPoint/GramCertificateData.lean` | the thirty certificates and their checks |
| `Besicovitch/SixPoint/GramCertificateCover.lean` | the eight-band radius cover |
| `Besicovitch/SixPoint/GramWeightedBound.lean` | the coordinate-free weighted bound |
| `Besicovitch/Main/RationalBound.lean` | the reduction to the density bound |
| `Besicovitch/Example/` | Besicovitch's set and the lower bound $1/2 \le \sigma_1$ |
| `comparator.json` | permits only `propext`, `Quot.sound`, `Classical.choice` |

`comparator.json` intentionally has no `definition_names` escape hatch: the definitions reachable
from the theorem statement are compared recursively.

An earlier form of this development pursued the sharp constant $s_*$ through six-variable
Bernstein certificates. That branch needed an estimated 29 CPU-hours of kernel reduction over 3072
adaptive leaves and was still incomplete — one of ten charts admitted no certificate tree. It was
removed once the Gram argument superseded it, and remains in the history at commit `7a8c833`.

## References

- A. S. Besicovitch, *On the fundamental geometrical properties of linearly measurable plane sets
  of points*, Math. Ann. **98** (1928), 422–464; part II, Math. Ann. **115** (1938), 296–329.
- D. Preiss and J. Tišer, *On Besicovitch's ½-problem*, J. London Math. Soc. (2) **45** (1992),
  279–287.
- C. De Lellis, F. Glaudo, A. Massaccesi and D. Vittone, *Besicovitch's 1/2 problem and linear
  programming*, [arXiv:2404.17536](https://arxiv.org/abs/2404.17536) (2024).
