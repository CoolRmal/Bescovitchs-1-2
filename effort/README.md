# Effort accounting

How this proof was produced, in time and tokens, separated into the two stages that made it:
the natural-language mathematics, and the Lean formalization.

Every figure below that is marked *measured* comes from a machine record and can be regenerated
with [`measure.sh`](measure.sh). Figures that could not be recovered are marked *not recoverable*
rather than estimated.

---

## 1. Natural-language mathematics

Done in a ChatGPT project, **"Besicovitch 1/2-Problem"**, before any Lean was written. This stage
produced the six-point analysis, the sharp constant, the failure tree, and finally the
Gram-certificate argument that the formalization actually uses.

### Time and tokens

| quantity | value | status |
|---|---|---|
| wall-clock span of the research output | **2026-08-26 → 2026-08-31** (6 days) | measured, from file timestamps |
| tokens consumed | — | **not recoverable** |
| session wall-clock | — | **not recoverable** |

**Why the token count is missing, stated plainly.** The ChatGPT project's conversations live
server-side. What exists locally is a mirror of the project's *output files* at
`~/.codex/.chatgpt-projects/g-p-6a8e11f7162c8191aab19dd2a7fe41d8`, not the transcripts. The local
Codex database (`~/.codex/state_5.sqlite`) does carry a `tokens_used` column, but it holds exactly
one thread rooted in this repository — a CLI session of 265,894 tokens — and none of the ChatGPT
project threads. The research notes themselves record no session accounting. Any token figure for
this stage would be a guess, so none is given.

### What the stage produced (measured)

| artifact | count | size |
|---|---|---|
| Markdown research notes | 246 files | 4,895,477 bytes — **617,968 words** |
| C++ search programs | 86 files | 467,774 bytes |
| LaTeX write-ups | 16 files | 450,197 bytes |
| Python verifiers | 53 files | 224,759 bytes |
| **total mirror** | **401 files** | **104 MB** |

The decisive output is the Gram-certificate document: the argument, the thirty exact rational
certificates, and two independent verifiers. Its own provenance note records that the certificate
family was checked three ways before formalization — an exact rational verifier, a symbolic
reconstruction in SymPy, and a diagnostic sweep of 3000 random feasible configurations.

---

## 2. Lean formalization

Done in Claude Code against this repository. Measured from the session transcripts at
`~/.claude/projects/-Users-aaron-Downloads-Besicovitchs-1-2/`.

The work splits cleanly at **2026-09-02 05:41:44**, when the Gram-certificate document arrived.
Before that point the target was pursued through six-variable Bernstein certificates; that route
was abandoned. The split is worth showing, because the two phases cost very differently.

| | Phase 1 — Bernstein (abandoned) | Phase 2 — Gram (delivered) | total |
|---|---:|---:|---:|
| wall clock | **14 h 54 m** | **10:11:05** | see note |
| API calls | 3,037 | 763 | 3,800 |
| output tokens | 1,963,539 | 2,361,573 | **4,325,112** |
| input tokens | 162,015 | 578 | 162,593 |
| cache writes | 43,101,010 | 2,225,567 | 45,326,577 |
| cache reads | 1,088,642,799 | 100,472,049 | 1,189,114,848 |
| **input + output + cache write** | **45,226,564** | **13,895,701** | **59,122,265** |

Cache reads are listed separately because they are billed differently from fresh input; the
"input + output + cache write" row is the figure to compare against a non-caching baseline.

Phase 2 is a snapshot taken while the session was still open — writing this document is itself
inside it — so re-running `measure.sh` will show that column a little larger. The figures above
were taken at the commit that completed the lower bound; Phase 2 now includes the whole
Besicovitch-example formalization (the `Besicovitch/Example/` modules), three of which were written
by parallel subagents whose tokens are included.

**The comparison that matters.** Phase 1 spent **94%** of the non-cached tokens and **75%** of the
wall clock, and contributed **no surviving line** to the final proof — its 24,274 lines were
deleted once the Gram argument superseded them. Phase 2 produced the entire delivered proof for
**2.7 M tokens in 5 hours**. Having the right mathematical argument was worth roughly a factor of
17 in tokens.

Phase 1 was not wasted in every sense: it built the failure tree, the geometric-measure-theory
layer, and the six-point transfer, all of which the final proof still uses. What it failed to
produce was the analytic endpoint.

### Repository history

| quantity | value |
|---|---|
| commits, total | 166 |
| commits co-authored by Claude | 27 |
| first commit | 2026-08-31 03:42 |
| latest commit | 2026-09-02 06:41 |

### Machine verification cost

Independent of authoring effort, checking the finished proof costs:

| stage | cost |
|---|---|
| full build, `lake build Solution Challenge`, warm Mathlib cache | **2 m 32 s wall / 12 m 13 s CPU** |
| the thirty certificate validity checks alone | 43 s |
| Gram certificate core | 7 s |
| band cover | 3 s |

For contrast, the abandoned Bernstein route was projected at **~29 CPU-hours** and was never
completed; one of its ten charts admitted no certificate tree at all.

---

## 3. Lines of Lean

99 files, **27,232 lines** total; **24,675** excluding blanks and comment-only lines.

| area | files | lines |
|---|---:|---:|
| `SixPoint` | 40 | 15,625 |
| `Rectifiability` | 18 | 5,024 |
| `Certificates` | 6 | 1,656 |
| `BPC` | 8 | 1,317 |
| `Measure` | 5 | 735 |
| `Geometry` | 2 | 218 |
| `Topology` | 1 | 128 |
| root (`Solution`, `Challenge`, `Besicovitch`, `Statement`) | 4 | 181 |
| `Main` | 2 | 97 |
| `Sigma` | 1 | 43 |
| **total** | **87** | **25,024** |

The Gram-certificate proof proper — everything the analytic endpoint needs — is four files:

| file | lines | contents |
|---|---:|---|
| `Besicovitch/SixPoint/GramCertificateData.lean` | 681 | the thirty certificates and their checks |
| `Besicovitch/SixPoint/GramCertificateCore.lean` | 578 | the local certificate theorem |
| `Besicovitch/SixPoint/GramCertificateCover.lean` | 217 | the eight-band radius cover |
| `Besicovitch/SixPoint/GramWeightedBound.lean` | 72 | the coordinate-free weighted bound |
| **total** | **1,548** | |

A further **24,274 lines across 84 modules** were deleted when the Gram argument made them
unreachable — the Bernstein charts, the self-inequality layer, and the exact-endpoint weight
derivation. They remain in the history at commit `7a8c833`.

---

## Reproducing these numbers

```sh
./effort/measure.sh
```

The script reads the Claude Code session transcripts and the repository itself. It cannot
reproduce the ChatGPT-side figures, for the reason given in section 1.
