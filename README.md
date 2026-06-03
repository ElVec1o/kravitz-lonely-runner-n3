# The n = 3 view-obstruction coordinate bound, formalized in Lean 4

A **sorry-free** Lean 4 / Mathlib formalization of the hard direction of Kravitz's
Theorem 7.2 for three runners: *a sorted primitive integer triple `(p, q, r)` whose
maximal-loneliness deficit satisfies `D(p, q, r) ≥ 3/14` has bounded top coordinate
`r ≤ 30`.* Combined with a finite enumeration, this closes the classification

```
D(p, q, r) ≥ 3/14   ⟺   (p, q, r) ∈ { (1,2,3), (1,2,6), (1,3,4), (1,5,6), (2,3,5) }
```

with `(1,2,3)` (where `D = 1/4`) the **unique** primitive triple strictly above the
`3/14` threshold. This is the `n = 3` input to the 2-dimensional view-obstruction
bound `δ₂(4) ≤ 3/14`.

Here `‖x‖` is the distance from `x` to the nearest integer,
`ML(p,q,r) = maxₜ minᵢ ‖vᵢ·t‖` is the maximal loneliness of the triple, and
`D(p,q,r) = 1/2 − ML(p,q,r)`.

## The theorems

In [`LonelyRunnerN3/KravitzPieceA.lean`](LonelyRunnerN3/KravitzPieceA.lean):

```lean
/-- The coordinate bound: D ≥ 3/14 forces r ≤ 30 (no boundary exception). -/
theorem coord_bound (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hcop_p : IsCoprime p (Int.gcd q r : ℤ)) (hcop_q : IsCoprime q (Int.gcd p r : ℤ))
    (hD : 3 / 14 ≤ D ![p, q, r]) : r ≤ 30

/-- (1,2,3) is the unique primitive triple strictly above 3/14. -/
theorem unique_above_threshold (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hcop_p : IsCoprime p (Int.gcd q r : ℤ)) (hcop_q : IsCoprime q (Int.gcd p r : ℤ))
    (hD : 3 / 14 < D ![p, q, r]) : p = 1 ∧ q = 2 ∧ r = 3
```

## How it is actually proved (no overclaiming)

The unbounded tail (`r > 30`) is closed by an **arithmetic-progression covering**,
not by the three-distance (three-gap) theorem. Once `r > 30` the relevant pair-sums
are `≥ 33`, so the modular covering step fits strictly inside the `2/7`-band and the
arithmetic progression spans a full period — forcing both runners into the band and
giving `ML ≥ 2/7`, i.e. `D ≤ 3/14`. The engine is
[`LonelyRunnerN3/Pigeonhole.lean`](LonelyRunnerN3/Pigeonhole.lean) (`ap_hits_interval`)
threaded through [`LonelyRunnerN3/KravitzCovering.lean`](LonelyRunnerN3/KravitzCovering.lean)
(`double_band_*`). The finite remainder (`r ≤ 30`) is closed by a verified enumeration.

> **Why not the three-gap theorem?** The bounded regime makes the simpler
> AP-pigeonhole covering sufficient, so the full three-distance machinery is not
> needed for this result.

## Trust surface

The project builds with **zero `sorry`**. An axiom audit (`#print axioms`, at the
bottom of `KravitzPieceA.lean`) makes the foundations explicit:

| Theorem | Axioms |
|---|---|
| `coord_bound`, `D_lt_of_large` | `propext`, `Classical.choice`, `Quot.sound` (the three Lean/Mathlib standard axioms — **nothing else**) |
| `D_le_of_not_123`, `unique_above_threshold` | the three standard axioms **plus** `native_decide` (a compiled finite enumeration) |

So the **coordinate bound itself rests on only the standard axioms**. `native_decide`
enters only the finer classification of the small (`r ≤ 30`) triples; it is a
kernel-external, compiler-trusting tactic, and its use is disclosed here and in the
source rather than hidden.

We *tested* replacing it with kernel-checked `decide`, and it is empirically
infeasible on commodity hardware: the `r ≤ 30` exhaustiveness check does not reduce
within practical limits (killed after >4 min, with the elaborator ballooning past
12 GB into swap), and the rational `mgapQ` certificates do not kernel-reduce at all
(only the compiled path evaluates them). `native_decide` is the appropriate tool for
these large finite verifications; a kernel-checked reformulation (integer-arithmetic
reflection with precomputed witness tables) is feasible in principle and tracked as
future work.

## Build

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager).
The toolchain (`leanprover/lean4:v4.30.0`) and Mathlib revision are pinned.

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build           # build the project (~minutes after cache)
```

A green `lake build` reproduces every theorem above and prints the axiom audit.

## Repository layout

The library is the transitive dependency closure of the capstone (19 modules).
Highlights:

| Module | Role |
|---|---|
| `NearestInteger`, `MaxLoneliness`, `DValue` | core definitions (`‖·‖`, `ML`, `D`) |
| `Pigeonhole` | the arithmetic-progression covering lemma `ap_hits_interval` |
| `KravitzCovering` | the double-band covering (Kravitz Lemma 7.1) |
| `KravitzStrict` | the strict large-coordinate bound `D < 3/14` for `r > 30` |
| `D3Classify` | the finite `r ≤ 30` enumeration |
| `KravitzPieceA` | the capstone `coord_bound` + axiom audit |

## Relationship to Mathlib

The genuinely reusable, Mathlib-shaped pieces are the arithmetic-progression
covering lemma (`ap_hits_interval`) and the nearest-integer / maximal-loneliness
API. The author makes no claim that the three-distance theorem is formalized here;
it is not used by this result.

## Provenance

This repository is a focused, self-contained extraction of the `n = 3` coordinate
bound from a larger research project on the view-obstruction spectrum. The companion
write-up of this formalization is in [`docs/paper_LEAN.md`](docs/paper_LEAN.md); the
accompanying analytical results (`δ₂(4) ≤ 3/14` and the exclusion of `2/7` from
`S₁(4)`) are released separately.

## Reference

N. Kravitz, *Barely lonely runners and very lonely runners*, Combinatorial Theory
**1** (2021), [arXiv:1912.06034](https://arxiv.org/abs/1912.06034).

## License & citation

Apache-2.0 (see [`LICENSE`](LICENSE)). Citation metadata in
[`CITATION.cff`](CITATION.cff). Author: **Vico Bonfioli**.

**AI assistance.** The Lean development, exploration, and exposition in this
repository were assisted by an AI language model (Anthropic's Claude). All
mathematical claims are the author's responsibility; the formal proofs are
machine-checked by Lean/Mathlib (axioms disclosed above and in the source).
