# Proof blueprint — the n = 3 view-obstruction coordinate bound

A structured overview of the formalization in this repository: what is proved, how
the proof is organized, and an honest account of the trust surface and its relation
to existing Mathlib. Intended as both documentation and the seed of a short
formalization write-up.

## 1. Statement

For a sorted primitive integer triple `0 < p < q < r` (primitivity in the usable form
`IsCoprime p (gcd q r)`, `IsCoprime q (gcd p r)`), with
`ML(p,q,r) = maxₜ minᵢ ‖vᵢ·t‖` the maximal loneliness and `D = 1/2 − ML`:

- **`coord_bound`** : `D(p,q,r) ≥ 3/14  →  r ≤ 30`.
- **`unique_above_threshold`** : `D(p,q,r) > 3/14  →  (p,q,r) = (1,2,3)`.

Together with the finite enumeration these give the classification
`D ≥ 3/14 ⟺ (p,q,r) ∈ L₃ = {(1,2,3),(1,2,6),(1,3,4),(1,5,6),(2,3,5)}`,
with `(1,2,3)` (`D = 1/4`) the unique triple strictly above `3/14`. This is the `n = 3`
input to the 2-dimensional view-obstruction bound `δ₂(4) ≤ 3/14` (Kravitz, Thm 7.2).

## 2. Definitions (and their Mathlib equivalents)

- `nearestIntDist x = min (Int.fract x) (1 − Int.fract x)`. **This equals Mathlib's
  `|x − round x|`** (`abs_sub_round_eq_min`) and the norm `‖·‖` of `AddCircle 1`
  (`Mathlib.Analysis.Normed.Group.AddCircle`). The local definition is self-contained
  for this development; a refactor to reuse Mathlib's `AddCircle` norm / `abs_sub_round`
  API is a natural cleanup (tracked as future work).
- `ML v = ⨆ₜ ⨅ᵢ nearestIntDist (vᵢ · t)`, `D v = 1/2 − ML v`.

## 3. Architecture: two regimes

The proof splits a sorted primitive triple by its top coordinate.

```
                          coord_bound  (D ≥ 3/14 → r ≤ 30)
                                  │  contrapositive
                                  ▼
                 r > 30 ───────────────────────────  r ≤ 30
                 (unbounded tail)                     (finite remainder)
                       │                                    │
            D_lt_of_large (strict)                 r30 enumeration + per-triple
            via AP-covering                        rational certificates
                       │                                    │
              ML ≥ 2/7  ⟹  D ≤ 3/14            each listed triple has D ≤ 3/14
```

### 3a. The unbounded tail `r > 30` — arithmetic-progression covering

This is the mathematical core, and it is **not** the three-distance theorem. Once
`r > 30`, the relevant pair-sums are `≥ 33`; the modular covering step then fits
strictly inside the `2/7`-band `[⌈2M/7⌉, ⌊5M/7⌋]`, and the arithmetic progression
`{ℓ·j mod M}` spans a full period, so it cannot skip the band.

- `Pigeonhole.ap_hits_interval` — generic AP-covering: an AP with step `q`, length
  `J·q ≥ m`, hits any band of width `≥ q−1` (mod `m`). *(Specialized; the only piece
  with plausible standalone Mathlib interest.)*
- `KravitzCovering.double_band_*` — both the pair-runner and third runner land in the
  band simultaneously (Kravitz Lemma 7.1), with explicit dispatch on the step size.
- `KravitzStrict.D_lt_of_large` — assembles the strict bound `D < 3/14` for `r > 30`.

### 3b. The finite remainder `r ≤ 30` — certified enumeration

- `D3Classify.tripleData` — the 3471 sorted primitive triples with `r ≤ 30` (≠ (1,2,3)),
  each with a rational witness `w = a/b`.
- `triple_certs` — every listed triple satisfies `2/7 ≤ mgapQ`, i.e. the witness clears
  the `2/7`-band; hence `D ≤ 3/14` (`mD_le_of_mgapQ`).
- `r30_exhaustive_nat` — every sorted primitive triple with `r ≤ 30` (≠ (1,2,3)) is listed.

## 4. Trust surface

- **Zero `sorry`.** Verified by a green `lake build`.
- **`#print axioms` audit** (bottom of `KravitzPieceA.lean`):
  - `coord_bound`, `D_lt_of_large`, `double_band_cover*` → `propext, Classical.choice,
    Quot.sound` only. **The coordinate bound itself is axiom-pure.**
  - `D_le_of_not_123`, `unique_above_threshold` → additionally `native_decide`, used for
    the two finite checks `triple_certs` and `r30_exhaustive_nat`.
- **On `native_decide`:** kernel-checked `decide` was tested as a replacement and is
  empirically infeasible on commodity hardware — the `r ≤ 30` exhaustiveness check does
  not reduce within practical time/memory (>4 min, >12 GB into swap), and the rational
  `mgapQ` certificates do not kernel-reduce at all. A kernel-checked reformulation
  (integer-arithmetic reflection with a precomputed witness table, bridged by
  `tripleData.map _ = ⟨literal⟩ := by rfl`) is feasible in principle and is tracked as
  future work; the `rfl` bridge and the reflected enumeration are confirmed, only the
  final `decide` is RAM-bound.

## 5. Provenance & references

Extracted from a larger private research project on the view-obstruction spectrum (the
accompanying `δ₂(4) ≤ 3/14` paper is not yet public). Follows N. Kravitz, *Barely lonely
runners and very lonely runners*, Combinatorial Theory **1** (2021), arXiv:1912.06034.
