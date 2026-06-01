/-
# The n = 3 view-obstruction coordinate bound (Kravitz Theorem 7.2), formalized

A sorry-free Lean 4 / Mathlib formalization that every sorted primitive integer
triple `(p, q, r)` with maximal-loneliness deficit `D(p,q,r) ≥ 3/14` has bounded
top coordinate `r ≤ 30` — the hard direction underlying the classification

  `D(p,q,r) ≥ 3/14  ⟺  (p,q,r) ∈ {(1,2,3),(1,2,6),(1,3,4),(1,5,6),(2,3,5)}`.

## How the bound is actually proved (no overclaiming)

The unbounded tail (`r > 30`) is closed by an **arithmetic-progression covering**
(`Pigeonhole.ap_hits_interval` ⟶ `KravitzCovering.double_band_*`): once `r > 30`,
the relevant pair-sums are `≥ 33`, the covering step fits inside the `2/7`-band,
and the AP spans a full period — so both runners are forced into the band, giving
`ML ≥ 2/7`, i.e. `D ≤ 3/14`. The finite remainder (`r ≤ 30`) is closed by a
verified enumeration. The capstone is `KravitzPieceA.coord_bound`.

NOTE: this proof does **not** use the three-distance (three-gap) theorem — the
bounded regime makes the simpler AP-pigeonhole covering sufficient.

## Trust surface

`#print axioms` confirms the strict coordinate bound (`coord_bound`,
`D_lt_of_large`) rests on only Lean's three standard axioms
`[propext, Classical.choice, Quot.sound]` — no `sorry`. The full classification
capstones (`D_le_of_not_123`, `unique_above_threshold`) additionally use
`native_decide` (a compiled finite enumeration), which adds two trust axioms;
this is disclosed explicitly in `KravitzPieceA.lean`.

Following Kravitz, "Barely lonely runners and very lonely runners,"
Combinatorial Theory 1 (2021), arXiv:1912.06034.
-/

-- Core definitions: nearest-integer norm, maximal loneliness, the D-value.
import LonelyRunnerN3.NearestInteger
import LonelyRunnerN3.MaxLoneliness
import LonelyRunnerN3.DValue

-- Subtorus / coherence / certificate infrastructure.
import LonelyRunnerN3.Subtorus
import LonelyRunnerN3.SubtorusMono
import LonelyRunnerN3.Coherence
import LonelyRunnerN3.RationalCert
import LonelyRunnerN3.PermInvariance

-- Lipschitz / confinement tooling for the loneliness function.
import LonelyRunnerN3.NearestIntLipschitz
import LonelyRunnerN3.Confinement
import LonelyRunnerN3.CoordConstruction

-- The arithmetic-progression covering engine.
import LonelyRunnerN3.Pigeonhole
import LonelyRunnerN3.Sweep

-- The Kravitz coordinate-bound chain.
import LonelyRunnerN3.KravitzCovering
import LonelyRunnerN3.KravitzCaseA
import LonelyRunnerN3.KravitzHookup
import LonelyRunnerN3.KravitzStrict

-- The finite classification and the capstone `coord_bound`.
import LonelyRunnerN3.D3Classify
import LonelyRunnerN3.KravitzPieceA
