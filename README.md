# Bescovitch's 1/2

A Lean 4 and Mathlib project for the proposed bound

$$
\sigma_1(\mathbb{R}^2) \le s_{\ast},
\qquad
s_{\ast} = 0.6933064218259048726\ldots,
$$

where `sStar` is defined by an exact isolated radical system rather than by a decimal.

The formalization is being developed in pushed, buildable milestones. The current solution theorem
still has a development hole and must not yet be treated as a completed proof. See
[`DEVELOPMENT_PLAN.md`](DEVELOPMENT_PLAN.md) for the proof graph and verification criteria.

**The formalization currently targets the weaker rational bound**

$$
\sigma_1(\mathbb{R}^2) \le \frac{6934}{10000},
$$

which still improves on the published $0.7$. The sharp constant $s_{\ast}$ is what the six-point
analysis below actually computes, but certifying it in Lean requires the endpoint to be attained
exactly, and that tightness is what makes the finite certificates expensive. Away from the
endpoint the same argument carries a margin of about $3\times10^{-3}$ instead of $10^{-8}$, which is what
makes the rational target reachable. `DEVELOPMENT_PLAN.md` records the measurements behind that
choice.

## The problem

For a Borel set $E \subset \mathbb{R}^2$ with finite one-dimensional Hausdorff measure, the
**lower density** at a point $x$ is

$$
\Theta^1_{\ast}(E,x) \;=\; \liminf_{r \downarrow 0} \frac{\mathcal{H}^1(E \cap B(x,r))}{2r},
$$

normalized by the diameter $2r$ of the ball, so that a straight segment has density $1$ at its
interior points. **Besicovitch's 1/2 conjecture** asserts that

> if $\mathcal{H}^1(E) < \infty$ and $\Theta^1_{\ast}(E,x) > 1/2$ for $\mathcal{H}^1$-almost every
> $x \in E$, then $E$ is countably 1-rectifiable — covered up to null measure by countably many
> Lipschitz curves.

The threshold $1/2$ is the natural candidate: it is the value attained at the endpoint of a
segment, and no known purely 1-unrectifiable set of finite length achieves a lower density above
it. Writing

$$
\sigma_1(\mathbb{R}^2) = \inf\lbrace\beta \ge 0 : \text{every finite-measure Borel set with }
\Theta^1_{\ast} \ge \beta \text{ a.e. is countably 1-rectifiable}\rbrace,
$$

the conjecture is the assertion $\sigma_1(\mathbb{R}^2) = 1/2$.

## A short history

| year | bound | source |
|---|---|---|
| 1928 | $1 - 10^{-2576}$ | Besicovitch |
| 1938 | $3/4$ | Besicovitch |
| 1992 | $(2+\sqrt{46})/12 = 0.73186\ldots$ | Preiss and Tišer |
| 2024 | $0.7$ | De Lellis, Glaudo, Massaccesi and Vittone |

Besicovitch introduced the problem in his 1928 study of linearly measurable plane sets and, ten
years later, brought the threshold down to $3/4$. Preiss and Tišer reached
$(2+\sqrt{46})/12$ in 1992 by a two-point inequality for *straight* measures — those satisfying
$\mu(A) \le \operatorname{diam} A$ for every measurable $A$. That bound stood for more than three
decades; the sharp threshold obtainable from the method is the unique positive root of
$8s^3+4s^2-3s-3$, namely $0.72655\ldots$.

The decisive structural advance is due to De Lellis, Glaudo, Massaccesi and Vittone, who recast
the question as a family of finite-dimensional optimization problems: the passage from a density
hypothesis to rectifiability can be routed through a purely finite statement about disjoint balls
centred at finitely many points, and that statement is a linear program once the centres are
fixed. **The optimization approach in this repository is inspired by theirs.**

## What this project proves

The finite problems are indexed by how many centres are used and how they are grouped. This
project solves the **two-colour, six-centre** instance exactly. Two colours correspond to the two
sets a separation argument produces; each colour contributes a root and two children. Its optimal
constant is the algebraic number

$$
\theta_6 = s_{\ast} = 0.693306421825904872690678414403710951\ldots,
$$

pinned by an isolated pair of radical equations inside an explicit rational box — the decimal
appears nowhere in the proof — with a unique extremal configuration up to the evident symmetries.
That configuration is a half-turn pair of chords of length $c_{\ast} = 2s_{\ast}$ at which three
structurally different packing mechanisms tie simultaneously, which is why the answer is an
algebraic number of high degree rather than a round one.

Combined with a direct six-centre transfer to the Besicovitch pair condition and the standard
rectifiability machinery, this gives $\sigma_1(\mathbb{R}^2) \le s_{\ast}$.

## The paper

[`paper/six-point-constant.pdf`](paper/six-point-constant.pdf) — the full write-up, with the
proof outline and geometric intuition first and the details afterwards. Source:
[`paper/six-point-constant.tex`](paper/six-point-constant.tex).

Build it with:

```sh
cd paper
pdflatex six-point-constant.tex && pdflatex six-point-constant.tex
```

## Where a computer is used

Three ingredients are finite interval computations: isolation of the algebraic endpoint and its
weights; a list of strict routing separators that prune the case tree; and the two analytic
inequalities at the heart of the argument (a self inequality on one sibling pair, and a
contraction relating a mixed pair to the two self terms).

In each case the certified statement is a universal inequality on an explicitly covered compact
domain, not the output of an optimizer. All interval endpoints are rational or dyadic, every
arithmetic operation is rounded outward using integers, and every sign decision is an integer
comparison. Bernstein conversion and the interval arithmetic are implemented and proved sound
inside Lean. Hashes, program exit codes, floating-point samples, `native_decide`, and unchecked
external computations are not proof objects.

## Comparator layout

- `Challenge.lean` contains every transparent statement definition and the requested theorem hole.
- `Solution.lean` repeats the same theorem independently.
- `Bescovitch/Statement.lean` contains the identical definitions used by the modular solution.
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

## References

- A. S. Besicovitch, *On the fundamental geometrical properties of linearly measurable plane sets
  of points*, Math. Ann. **98** (1928), 422–464; part II, Math. Ann. **115** (1938), 296–329.
- D. Preiss and J. Tišer, *On Besicovitch's ½-problem*, J. London Math. Soc. (2) **45** (1992),
  279–287.
- C. De Lellis, F. Glaudo, A. Massaccesi and D. Vittone, *Besicovitch's 1/2 problem and linear
  programming*, [arXiv:2404.17536](https://arxiv.org/abs/2404.17536) (2024).
