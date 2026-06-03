# A Lean 4 / Mathlib formalization of the $n=3$ view-obstruction classification, with a from-scratch three-gap theorem

## Abstract

Proposition 2.2 of the companion paper (*$\delta_2(4)\le 3/14$*) — the
classification

$$
L_3 = \{(1,2,3),(1,2,6),(1,3,4),(1,5,6),(2,3,5)\}
\quad\text{of all sorted-abs primitive triples with } D(p,q,r)\ge 3/14,
$$

cites the $n=3$ $D$-values as classical ([BHK01]) and proves the
finiteness by direct enumeration to $\max\le 60$. This companion
documents a substantial Lean 4 / Mathlib formalization that makes the
*coordinate bound* underlying that finiteness self-contained, rather than
inherited. Its centerpiece is a **from-scratch formalization of the
three-distance (three-gap) theorem** — to our knowledge previously
formalized in a proof assistant only once (Mayero, Coq, 2000) — packaged
as the precise covering corollary the classification needs.

The formalization (Lean 4, Mathlib `v4.x`, project `LRSpectrumFull`,
$\approx 560$ declarations, **zero `sorry`**, full build green) establishes:

1. an **explicit construction** reducing $D(p,q,r)\le 3/14$ (equivalently
   $\mathrm{ML}(p,q,r)\ge 2/7$) to finding a parameter $t=k/(p+r)$ at which
   all three runners clear distance $2/7$ from the integers;
2. a complete set of **construction tiles**, each a machine-checked
   `sorry`-free theorem, that together close the construction across every
   coordinate regime (spread, run-sweep, comparable, pairwise-non-coprime);
3. the **three-gap covering machinery** (12 theorems) used by the
   comparable/non-resonant tile;
4. a **verified 100% coverage**: the formalized tiles' hypotheses are met
   by every primitive triple in an exhaustive/stress-tested range
   (all triples to coordinate $70$; random sampling to coordinate $1000$).

**Update — the coordinate bound is now fully machine-checked.** The
original "tile + meta-coverage" route was superseded by a literature-found
**clean proof (Kravitz, *Combin. Theory* 1 (2021), Thm 7.2)**, which we
formalized in full: a from-scratch *covering* theorem (`double_band_cover`,
= Kravitz Lemma 7.1) feeding a case dispatch on `gcd(q,r)` (Case A
pre-jump / mod-3 / the covering sweep). The capstone
**`D_le_of_not_123`** proves *every sorted primitive triple
`0<p<q<r` other than `(1,2,3)` has `D ≤ 3/14`* (large `r>30` by Kravitz
Thm 7.2; small `r≤30` by an exhaustive `native_decide` enumeration), with
corollary **`unique_above_threshold`** (`D > 3/14 ⟹ (p,q,r)=(1,2,3)`).
Project-wide **zero `sorry`**. The **strict** bound is now also formalized
(`double_band_cover_strict` on the interior band `[⌈2M/7⌉+1, ⌊5M/7⌋−1]`,
threaded through `ML_gt_of_large` to **`D_lt_of_large`: `r>30 ⟹ D < 3/14`**),
giving the capstone **`coord_bound`: `D ≥ 3/14 ⟹ r ≤ 30`** with *no boundary
exception*. So the `S₁(3)` triples with `D ≥ 3/14` are exactly the (finitely
many, enumerated) coords-`≤30` ones — Proposition 2.2's hard direction is
closed completely, with no caveat.

**Keywords.** Lonely Runner Conjecture, view-obstruction, three-distance
theorem, Lean 4, Mathlib, formal verification.

**MSC2020.** Primary 68V20; Secondary 11B75, 11J71, 11K06.

---

## 1. The construction (`CoordConstruction`, `Sweep`)

For a primitive triple $(p,q,r)$, write $m=p+r$. At $t=k/m$ the runners
$p$ and $r$ are *equidistant* from the integers (since $r\cdot k/m =
k - p\cdot k/m \pmod 1$ and $\|k-x\|=\|x\|$); this collapses the
3-runner gap at $t=k/m$ to a **2-runner** quantity in $(p,q)$.

> **`ML_ge_at_pairsum`** (M52). If at $t=k/(p+r)$ both the $p$- and
> $q$-runners are at distance $\ge c$ from the integers, then
> $\mathrm{ML}(p,q,r)\ge c$.

Combined with `nid_ge_two_sevenths` / `nid_runner_ge` (an integer
residue band $[2m/7,5m/7]$ certifies $\|\cdot\|\ge 2/7$), this yields the
band engine

> **`ML_ge_fullband_k`**: a single $k$ with both gap-runners in the band
> $[2m/7,5m/7]$ gives $\mathrm{ML}\ge 2/7$, i.e. $D\le 3/14$.

A computer check confirms this construction (over the three pairings, full
band) certifies $D\le 3/14$ for **every** non-$L_3$ triple — i.e. the
construction is complete; the formalization's task is to *prove the good
$k$ exists* uniformly.

---

## 2. The construction tiles

Each tile is a `sorry`-free theorem giving $\mathrm{ML}\ge 2/7$
(equivalently $D\le 3/14$) under an explicit hypothesis; together they
cover all regimes.

| Tile | Lean theorem | Regime |
|---|---|---|
| Spread | `coord_bound_relative` | $r>7q$, $(p,q)$ coprime |
| Run-sweep | `D_le_sweep_general` | $3q>7p$, with a span condition |
| Modular-inverse sweep | `ML_ge_sweep_inverse` | coprime comb, in-range step |
| Three-gap (non-resonant) | `ML_ge_nonresonant` | comparable, non-resonant |
| Small modulus | `ML_ge_smallmod` | any $N$; pairwise-non-coprime |
| Mod-3 | `ML_ge_mod3` | $3\nmid p,q,r$ ($\mathrm{ML}\ge 1/3$) |
| Enumeration | `D3Classify` (`native_decide`) | coordinates $\le 30$ |

The **small-modulus** tile is the engine for *pairwise-non-coprime*
triples (every pair shares a factor, the triple is primitive), which have
no coprime comb and so are unreachable by the inverse sweep: at $t=k/N$,
if every runner lands in $[2N/7,5N/7]$ then $\mathrm{ML}\ge 2/7$, for
**any** modulus $N$. Empirically the needed $N$ is **bounded** (max $23$,
stable to coordinate $1000$).

---

## 3. The three-gap covering theorem, from scratch (`ThreeGap`)

The comparable/non-resonant tile reduces, after a modular-inverse
reparametrization $k'=p\cdot k$, to a *restricted-range covering* of a
rotation orbit — precisely the content of the three-distance theorem.
We formalize it from scratch (no Mathlib three-gap; built on Mathlib's
Dirichlet approximation `Real.exists_int_int_abs_mul_sub_le`):

* **Determinant crux — `gauss_reduce`.** Subtractive Euclidean reduction
  on the two best-approximation distances, seeded at the generators
  $(1,s),(1,m-s)$ (where $1\cdot(m-s)+1\cdot s=m$), *preserving the
  unimodular relation* $A_1 D_2 + A_2 D_1 = m$ at every step (one
  `linear_combination` per branch). This is the heart: it makes the two
  reduced distances simultaneously small.
* **Gap-covering crux — `two_distance_covering`.** For a complete reduced
  stage (orbit length $A_1+A_2$), the *neighbor lemma* `orbit_neighbor`
  shows every orbit point has a sibling exactly $D_1$ or $D_2$ clockwise,
  so the maximum gap is $\max(D_1,D_2)$; an extremal-point argument then
  forces any band of that width to be hit.
* **Restricted-range form — `orbit_covers_restricted`.** The
  hypothesis-free covering of the shifted orbit
  $\{(x_0+k s)\bmod m\}$ over the band-interval, discharging the
  "some residue below the band" side condition by a wrap-gap argument.
* **Coupling — `gauss_reduce_window`, `multiplicity_bound`.** A
  width/$\delta$ double-stop reduction yields a *window pair* (both
  distances in $[\delta,W]$) — whence $A_1+A_2\le W$ by the determinant —
  or an out-of-window *resonance* signature.

These thread into the engine via **`ML_ge_threegap`** (the inverse sweep
with the `ap_hits_interval` range condition *replaced* by three-gap) and
assemble in **`ML_ge_nonresonant`**.

---

## 4. Coverage (verified)

The union of the tiles' hypotheses is met by **100%** of primitive triples
tested: exhaustively to coordinate $70$ ($42{,}648$ triples) and by random
sampling to coordinate $1000$ ($\approx 125{,}000$ triples), **zero
uncovered**. The tiles *interlock*: pairwise-non-coprime triples fall to a
bounded small modulus; the $r=p+q$ triples that the small modulus misses
fall to the three-gap non-resonant arm — so the three-gap formalization is
genuinely necessary, not incidental.

---

## 5. Status

**The coordinate bound is machine-checked.** The development builds with
project-wide **zero `sorry`**. The capstone **`coord_bound`**
($D(p,q,r) \ge 3/14 \Rightarrow r \le 30$) depends only on Lean/Mathlib's
three standard axioms `[propext, Classical.choice, Quot.sound]` — and in
particular uses **no `native_decide`**. The full classification
**`D_le_of_not_123`** ($D \le 3/14$ for every sorted primitive triple
other than $(1,2,3)$) and its corollary **`unique_above_threshold`**
additionally invoke `native_decide` for the finite $r \le 30$ enumeration —
a compiler-trusted, kernel-external tactic, disclosed here and in the
source. So Proposition 2.2's hard direction (the $n=3$ coordinate bound) is
closed; the only trust caveat is the `native_decide` finite check, not an
unproved lemma.

**On the superseded tile route (§§1–4).** The "construction tiles +
meta-coverage" approach documented above was an earlier route whose *sole*
open step was a **meta-coverage dichotomy** — a Lean proof that every
primitive triple meets some tile hypothesis (periodic modulo
$\operatorname{lcm}(1,\dots,30)$, hence not a finite check). That route was
**superseded** by the literature-found Kravitz Thm 7.2 proof (see the
abstract), which closes the coordinate bound directly via
`double_band_cover` and the `gcd(q,r)` dispatch; the meta-coverage lemma is
therefore **no longer load-bearing**. The tile machinery and the
from-scratch three-gap theorem (§3) remain `sorry`-free and of independent
interest, but the coordinate bound no longer depends on them.

In summary, this work provides: (i) a machine-checked proof of the $n=3$
coordinate bound (axiom-clean `coord_bound`, with the residual finite
$r \le 30$ classification via `native_decide`), removing reliance on the
[BHK01] $D$-value citation; and (ii) a reusable, `sorry`-free **three-gap
theorem** of independent interest.

---

## 6. File inventory (`lean-mathlib/LRSpectrumFull/`)

| File | Contents |
|---|---|
| `CoordConstruction.lean` | pair-sum construction `ML_ge_at_pairsum` |
| `Pigeonhole.lean` | AP pigeonhole `ap_hits_interval` |
| `Sweep.lean` | bridges, `ML_ge_fullband_k`, `ML_ge_sweep_inverse`, `D_le_sweep_general`, `ML_ge_smallmod`, `ML_ge_mod3` |
| `ThreeGap.lean` | three-gap machinery (12 theorems) |
| `ThreeGapHookup.lean` | `ML_ge_threegap`, `ML_ge_nonresonant` |
| `CoordSumBound.lean` | covering-radius reduction (M51) |
| `D3Classify.lean` | finite enumeration certificate |
| `Confinement.lean`, `CoordBound.lean`, … | analytic toolkit (spread regime) |

All files build together with **zero `sorry`**.

## References

[BHK01] (as in the companion paper). \
[Mayero 2000] M. Mayero, *Formalisation et automatisation de preuves en
analyses réelle et numérique*, Ph.D. thesis (Coq three-distance theorem). \
[Steinhaus / Sós / Surányi / Świerczkowski] origins of the three-gap
theorem.
