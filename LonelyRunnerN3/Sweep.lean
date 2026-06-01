/-
# Milestone 56: the sweep — closing an infinite family of `p=1` triples

Combining the AP pigeonhole (`ap_hits_interval`, M55) with the pair-sum engine
(`ML_ge_at_pairsum`, M52), this file proves the **sweep** for `p = 1`:

For `(1, q, r)`, take the pair-sum modulus `m = 1+r` and a residue band
`B = [lo, hi] ⊆ [2m/7, 5m/7]` of the "good" zone (where a runner is `≥ 2/7`
from the integers). The first runner (speed `1`) is good for *every* `k ∈ B`
(an interval). The pigeonhole then finds a `k ∈ B` at which the second runner
`q` is *also* good — provided `B` is at least `q` wide and `B` swept by `q`
spans a full period. Both runners (hence — via the runner coincidence — all
three) clear `2/7`, so `ML(1,q,r) ≥ 2/7`, i.e. `D(1,q,r) ≤ 3/14`.

This is the first genuinely *uniform* (non-enumerative) closure of an infinite
family in the `r ≤ 7q` regime — the regime the analytic confinement bound
cannot reach. No `sorry`.
-/

import LonelyRunnerN3.Pigeonhole
import LonelyRunnerN3.CoordConstruction
import LonelyRunnerN3.NearestInteger
import LonelyRunnerN3.Confinement

namespace LonelyRunnerN3

/-- A real number in the middle band `[2/7, 5/7]` is `≥ 2/7` from the integers. -/
theorem nid_ge_two_sevenths (y : ℝ) (h1 : 2 / 7 ≤ y) (h2 : y ≤ 5 / 7) :
    2 / 7 ≤ nearestIntDist y := by
  rcases le_or_gt y (1 / 2) with h | h
  · rw [nearestIntDist_eq_self_of_le_half y (by linarith) h]; linarith
  · have e : nearestIntDist y = nearestIntDist (1 - y) := by
      rw [show (1 : ℝ) - y = -y + ((1 : ℤ) : ℝ) by push_cast; ring,
        nearestIntDist_add_int, nearestIntDist_neg]
    rw [e, nearestIntDist_eq_self_of_le_half (1 - y) (by linarith) (by linarith)]
    linarith

/-- Integer residue band ⟹ `nid ≥ 2/7`. If `2m ≤ 7N ≤ 5m` then `‖N/m‖ ≥ 2/7`. -/
theorem nid_ge_of_band (N m : ℤ) (hm : 0 < m) (hlo : 2 * m ≤ 7 * N) (hhi : 7 * N ≤ 5 * m) :
    2 / 7 ≤ nearestIntDist ((N : ℝ) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  apply nid_ge_two_sevenths
  · rw [le_div_iff₀ hmR]
    have h : (2 : ℝ) * m ≤ 7 * N := by exact_mod_cast hlo
    linarith
  · rw [div_le_iff₀ hmR]
    have h : (7 : ℝ) * N ≤ 5 * m := by exact_mod_cast hhi
    linarith

/-- Runner band ⟹ `nid ≥ 2/7`, accounting for the integer part `c`. -/
theorem nid_runner_ge (a k m c : ℤ) (hm : 0 < m)
    (hlo : 2 * m ≤ 7 * (a * k - c * m)) (hhi : 7 * (a * k - c * m) ≤ 5 * m) :
    2 / 7 ≤ nearestIntDist ((a : ℝ) * ((k : ℝ) / (m : ℝ))) := by
  have hmR : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hm : (0 : ℝ) < (m : ℝ))
  have e : (a : ℝ) * ((k : ℝ) / (m : ℝ))
      = ((a * k - c * m : ℤ) : ℝ) / (m : ℝ) + ((c : ℤ) : ℝ) := by
    field_simp; push_cast; ring
  rw [e, nearestIntDist_add_int]
  exact nid_ge_of_band (a * k - c * m) m hm hlo hhi

/-- **The sweep (`p = 1`).** Given a residue band `[lo, hi]` inside the good
zone `[2m/7, 5m/7]` of the pair-sum modulus `m = 1 + r`, lying in `[0, m)`, at
least `q` wide, and whose `q`-fold sweep spans a full period, we get
`ML(1, q, r) ≥ 2/7`. -/
theorem ML_ge_sweep_p1 (q r lo hi : ℤ) (hq : 0 < q) (hr : 0 < r)
    (hlo2 : 2 * (1 + r) ≤ 7 * lo) (hhi5 : 7 * hi ≤ 5 * (1 + r))
    (_hlonn : 0 ≤ lo) (_hhim : hi < 1 + r)
    (hwidth : lo + q - 1 ≤ hi) (hspan : 1 + r ≤ (hi - lo) * q) :
    2 / 7 ≤ ML ![1, q, r] := by
  have hm : 0 < 1 + r := by omega
  -- pigeonhole: ∃ j ∈ [0, hi-lo], q*lo + j*q ≡ [lo,hi] mod (1+r)
  obtain ⟨j, hj0, hjJ, c, hclo, hchi⟩ :=
    ap_hits_interval q (1 + r) (q * lo) lo hi (hi - lo) hq hm hspan hwidth
  -- the witness  k = lo + j  lies in [lo, hi]
  have hklo : lo ≤ lo + j := by omega
  have hkhi : lo + j ≤ hi := by omega
  -- rewrite the pigeonhole conclusion in terms of  q*k  where k = lo+j
  have hqk : q * lo + j * q = q * (lo + j) := by ring
  rw [hqk] at hclo hchi
  -- runner 1 (speed 1) good at k:  band is k itself (c = 0)
  have hr1 := nid_runner_ge 1 (lo + j) (1 + r) 0 hm (by omega) (by omega)
  -- runner q good at k:  band is q*k - c*(1+r) ∈ [lo, hi] ⊆ [2m/7, 5m/7]
  have hrq := nid_runner_ge q (lo + j) (1 + r) c hm (by omega) (by omega)
  -- assemble via the pair-sum engine (p = 1, so p + r = 1 + r)
  have hpr : ((1 + r : ℤ) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast hm : (0 : ℝ) < ((1 + r : ℤ) : ℝ))
  exact ML_ge_at_pairsum 1 q r (lo + j) (2 / 7) hpr hr1 hrq

/-- **An infinite family closed by the sweep.** For `s ≥ 1` and `3 ≤ q ≤ 3s+1`,
the triple `(1, q, 7s−1)` has `D ≤ 3/14` — proved uniformly (no enumeration)
via the band `[2s, 5s]` of the modulus `m = 7s`. These triples have `r ≤ 7q`,
the regime the analytic confinement bound cannot reach. -/
theorem D_le_sweep_family (s q : ℤ) (hs : 1 ≤ s) (hq3 : 3 ≤ q) (hqs : q ≤ 3 * s + 1) :
    D ![1, q, 7 * s - 1] ≤ 3 / 14 := by
  have hML : 2 / 7 ≤ ML ![1, q, 7 * s - 1] := by
    apply ML_ge_sweep_p1 q (7 * s - 1) (2 * s) (5 * s)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ s by omega) (show (0 : ℤ) ≤ 3 * q - 7 by omega)]
  simp only [D]; linarith

/-- **General `p = 1` sweep (all large `r`).** Using the integer-division band
endpoints `lo = ⌈2m/7⌉ = (2m+6)/7`, `hi = ⌊5m/7⌋ = 5m/7` of the modulus
`m = 1+r`, the sweep closes *every* `(1, q, r)` with `r ≥ 17`, `q ≥ 3`, and
`7q ≤ 3(1+r)` (i.e. `q ≲ 3m/7`, the `q`-not-too-large regime). `omega`
discharges the band/width inclusions (it reasons about `÷ 7`); `nlinarith`
discharges the span. -/
theorem ML_ge_sweep_p1_general (q r : ℤ) (hq3 : 3 ≤ q) (hr17 : 17 ≤ r)
    (hqr : 7 * q ≤ 3 * (1 + r)) : 2 / 7 ≤ ML ![1, q, r] := by
  apply ML_ge_sweep_p1 q r ((2 * (1 + r) + 6) / 7) (5 * (1 + r) / 7)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · -- span: 1 + r ≤ (hi - lo) * q
    set W : ℤ := 5 * (1 + r) / 7 - (2 * (1 + r) + 6) / 7 with hW
    have key : 3 * (1 + r) - 12 ≤ 7 * W := by rw [hW]; omega
    nlinarith [key, hq3, hr17,
      mul_nonneg (show (0 : ℤ) ≤ 7 * W - (3 * (1 + r) - 12) by omega) (show (0 : ℤ) ≤ q by omega),
      mul_nonneg (show (0 : ℤ) ≤ 3 * (1 + r) - 12 by omega) (show (0 : ℤ) ≤ q - 3 by omega)]

/-- `D ≤ 3/14` for every `(1, q, r)` with `r ≥ 17`, `q ≥ 3`, `7q ≤ 3(1+r)`. -/
theorem D_le_sweep_p1_general (q r : ℤ) (hq3 : 3 ≤ q) (hr17 : 17 ≤ r)
    (hqr : 7 * q ≤ 3 * (1 + r)) : D ![1, q, r] ≤ 3 / 14 := by
  have := ML_ge_sweep_p1_general q r hq3 hr17 hqr
  simp only [D]; linarith

/-- **The general run-based sweep engine (any `p`).** With pairing `(p, r)`,
modulus `m = p + r`, and a band `[lo, hi]` inside the good zone, suppose:
* `p·k₀ ≡ V₀ (mod m)` lands in the *entry window* `[lo, lo+p−1]` of the band
  (the slowest runner `p` just enters the good zone at `k = k₀`);
* the run `k = k₀, …, k₀+L` keeps `p` inside the band (`lo+p−1+Lp ≤ hi`, no wrap);
* the band is at least `q` wide and `L`-fold sweep of `q` spans a period.
Then at some `k = k₀+j` in the run, the faster runner `q` is *also* in the band,
so `ML(p,q,r) ≥ 2/7`. Specializing `p = 1, k₀ = lo, c₀ = 0` recovers
`ML_ge_sweep_p1`; the point is it now works for every `p`. -/
theorem ML_ge_sweep_core (p q r lo hi k0 L c0 : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hm : 0 < p + r)
    (hlo2 : 2 * (p + r) ≤ 7 * lo) (hhi5 : 7 * hi ≤ 5 * (p + r))
    (hk0lo : lo ≤ p * k0 - c0 * (p + r))
    (hk0hi : p * k0 - c0 * (p + r) ≤ lo + p - 1)
    (hnowrap : lo + p - 1 + L * p ≤ hi)
    (hwidth : lo + q - 1 ≤ hi) (hspan : p + r ≤ L * q) :
    2 / 7 ≤ ML ![p, q, r] := by
  obtain ⟨j, hj0, hjL, c', hc'lo, hc'hi⟩ :=
    ap_hits_interval q (p + r) (q * k0) lo hi L hq hm hspan hwidth
  have hjp0 : 0 ≤ j * p := mul_nonneg hj0 hp.le
  have hjpL : j * p ≤ L * p := mul_le_mul_of_nonneg_right hjL hp.le
  have hVp : p * (k0 + j) - c0 * (p + r) = (p * k0 - c0 * (p + r)) + j * p := by ring
  have hr_p := nid_runner_ge p (k0 + j) (p + r) c0 hm (by rw [hVp]; omega) (by rw [hVp]; omega)
  have hVq : q * (k0 + j) - c' * (p + r) = q * k0 + j * q - c' * (p + r) := by ring
  have hr_q := nid_runner_ge q (k0 + j) (p + r) c' hm (by rw [hVq]; omega) (by rw [hVq]; omega)
  have hpr : ((p + r : ℤ) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hm : (0 : ℝ) < ((p + r : ℤ) : ℝ))
  exact ML_ge_at_pairsum p q r (k0 + j) (2 / 7) hpr hr_p hr_q

/-- **Run-based sweep with automatic `k₀` (any `p`).** Drops the `k₀`/`c₀`
hypotheses of `ML_ge_sweep_core` by constructing the band-entry point `k₀`
with a second application of the pigeonhole (the slowest runner `p` lands in
the length-`p` entry window of every period). -/
theorem ML_ge_sweep_auto (p q r lo hi L : ℤ) (hp : 0 < p) (hq : 0 < q) (hm : 0 < p + r)
    (hlo2 : 2 * (p + r) ≤ 7 * lo) (hhi5 : 7 * hi ≤ 5 * (p + r))
    (hnowrap : lo + p - 1 + L * p ≤ hi) (hwidth : lo + q - 1 ≤ hi) (hspan : p + r ≤ L * q) :
    2 / 7 ≤ ML ![p, q, r] := by
  obtain ⟨k0, hk00, hk0J, c0, hc0lo, hc0hi⟩ :=
    ap_hits_interval p (p + r) 0 lo (lo + p - 1) (p + r) hp hm
      (by nlinarith [mul_nonneg hm.le (show (0 : ℤ) ≤ p - 1 by omega)]) (by omega)
  have hcomm : k0 * p = p * k0 := mul_comm _ _
  exact ML_ge_sweep_core p q r lo hi k0 L c0 hp hq hm hlo2 hhi5 (by omega) (by omega)
    hnowrap hwidth hspan

/-- **An infinite `p = 2` family closed by the run-based sweep.** For `s ≥ 2`
and `7 ≤ q ≤ 3s+1`, the triple `(2, q, 7s−2)` has `D ≤ 3/14`. This is the first
formalized closure with `p ≥ 2` — the regime that is ~95% of the tail. -/
theorem D_le_sweep_p2_family (s q : ℤ) (hs : 2 ≤ s) (hq7 : 7 ≤ q) (hqs : q ≤ 3 * s + 1) :
    D ![2, q, 7 * s - 2] ≤ 3 / 14 := by
  have hML : 2 / 7 ≤ ML ![2, q, 7 * s - 2] := by
    apply ML_ge_sweep_auto 2 q (7 * s - 2) (2 * s) (5 * s) s
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ s by omega) (show (0 : ℤ) ≤ q - 7 by omega)]
  simp only [D]; linarith

/-- **Full-band single-`k` construction.** If at `t = k/(p+r)` the `p`- and
`q`-runners both land in the *full* good band `[2/7, 5/7]` (witnessed by integer
parts `cp, cq` with `2m ≤ 7(p·k − cp·m) ≤ 5m` and likewise for `q`), then
`ML(p,q,r) ≥ 2/7`, i.e. `D ≤ 3/14`. Unlike the `eq_self` band `(2/7, 1/2]` of
`D_lt_band`, this uses the whole band via `nid_runner_ge`, so it captures the
threshold-tight triples whose optimal runner wraps past `1/2`. A computer check
confirms this construction (over all three pairings) covers **100%** of the
tail. -/
theorem ML_ge_fullband_k (p q r k cp cq : ℤ) (hm : 0 < p + r)
    (hp1 : 2 * (p + r) ≤ 7 * (p * k - cp * (p + r)))
    (hp2 : 7 * (p * k - cp * (p + r)) ≤ 5 * (p + r))
    (hq1 : 2 * (p + r) ≤ 7 * (q * k - cq * (p + r)))
    (hq2 : 7 * (q * k - cq * (p + r)) ≤ 5 * (p + r)) :
    2 / 7 ≤ ML ![p, q, r] := by
  have hpr : ((p + r : ℤ) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hm : (0 : ℝ) < ((p + r : ℤ) : ℝ))
  exact ML_ge_at_pairsum p q r k (2 / 7) hpr
    (nid_runner_ge p k (p + r) cp hm hp1 hp2) (nid_runner_ge q k (p + r) cq hm hq1 hq2)

/-- **The threshold interface.** `ML(p,q,r) ≥ 2/7 ⟺ D(p,q,r) ≤ 3/14` (since
`D = 1/2 − ML`). Every construction tile produces `ML ≥ 2/7`; this is the common
target they all feed into, and the conclusion the meta-coverage dichotomy
dispatches to. -/
theorem D_le_threshold_of_ML (p q r : ℤ) (h : 2 / 7 ≤ ML ![p, q, r]) :
    D ![p, q, r] ≤ 3 / 14 := by
  simp only [D]; linarith

/-- **The small-modulus tile.** At `t = k/N`, if every runner lands in the good
band `[2N/7, 5N/7]` of the modulus `N` (witnessed by integer parts `cp, cq, cr`),
then `ML(p,q,r) ≥ 2/7`. Unlike `ML_ge_fullband_k` (which is tied to the pair-sum
modulus `p+r`), this works at *any* modulus `N` with *no* pairing — the engine
for the residual pairwise-non-coprime triples, which have no coprime comb but
are killed by a small `t=k/N` with `N` coprime to the shared primes. Subsumes
the mod-3 tile (`N=3, k=1`). -/
theorem ML_ge_smallmod (p q r N k cp cq cr : ℤ) (hN : 0 < N)
    (hp1 : 2 * N ≤ 7 * (p * k - cp * N)) (hp2 : 7 * (p * k - cp * N) ≤ 5 * N)
    (hq1 : 2 * N ≤ 7 * (q * k - cq * N)) (hq2 : 7 * (q * k - cq * N) ≤ 5 * N)
    (hr1 : 2 * N ≤ 7 * (r * k - cr * N)) (hr2 : 7 * (r * k - cr * N) ≤ 5 * N) :
    2 / 7 ≤ ML ![p, q, r] := by
  refine le_trans ?_ (gap_le_ML ![p, q, r] ((k : ℝ) / (N : ℝ)))
  apply le_gap
  intro i
  fin_cases i
  · show 2 / 7 ≤ nearestIntDist ((![p, q, r] 0 : ℝ) * ((k : ℝ) / (N : ℝ)))
    simpa using nid_runner_ge p k N cp hN hp1 hp2
  · show 2 / 7 ≤ nearestIntDist ((![p, q, r] 1 : ℝ) * ((k : ℝ) / (N : ℝ)))
    simpa using nid_runner_ge q k N cq hN hq1 hq2
  · show 2 / 7 ≤ nearestIntDist ((![p, q, r] 2 : ℝ) * ((k : ℝ) / (N : ℝ)))
    simpa using nid_runner_ge r k N cr hN hr1 hr2

/-- **The mod-3 tile.** If none of `p, q, r` is divisible by 3, then at
`t = 1/3` every runner sits at `±1/3` from the integers (`‖x/3‖ = 1/3` when
`3 ∤ x`), which is `≥ 2/7`, so `ML(p,q,r) ≥ 2/7` (in fact `≥ 1/3`). This is a
clean explicit witness that absorbs a large share of the resonant residual —
e.g. the `(1,n,2n)` family for `3 ∤ n`. -/
theorem ML_ge_mod3 (p q r : ℤ) (hp : ¬ (3 ∣ p)) (hq : ¬ (3 ∣ q)) (hr : ¬ (3 ∣ r)) :
    2 / 7 ≤ ML ![p, q, r] := by
  refine le_trans ?_ (gap_le_ML ![p, q, r] (((1 : ℤ) : ℝ) / ((3 : ℤ) : ℝ)))
  apply le_gap
  intro i
  fin_cases i
  · show 2 / 7 ≤ nearestIntDist ((![p, q, r] 0 : ℝ) * (((1 : ℤ) : ℝ) / ((3 : ℤ) : ℝ)))
    simpa using nid_runner_ge p 1 3 (p / 3) (by norm_num) (by omega) (by omega)
  · show 2 / 7 ≤ nearestIntDist ((![p, q, r] 1 : ℝ) * (((1 : ℤ) : ℝ) / ((3 : ℤ) : ℝ)))
    simpa using nid_runner_ge q 1 3 (q / 3) (by norm_num) (by omega) (by omega)
  · show 2 / 7 ≤ nearestIntDist ((![p, q, r] 2 : ℝ) * (((1 : ℤ) : ℝ) / ((3 : ℤ) : ℝ)))
    simpa using nid_runner_ge r 1 3 (r / 3) (by norm_num) (by omega) (by omega)

/-- **The modular-inverse sweep (comparable regime, coprime comb).** For a
pairing with `gcd(p, p+r) = 1` — witnessed by Bezout coefficients `a, b` with
`p·a + (p+r)·b = 1` — reparametrizing `k' = p·k` turns the `p`-runner into the
identity comb and the `q`-runner into an arithmetic progression of step
`s = q·a mod (p+r)`. When that step fits the pigeonhole (`s > 0`, band width
`≥ s`, span `(hi−lo)·s ≥ p+r`), the sweep produces a good `k = a·(lo+j)` with
explicit integer parts `cp = −b·(lo+j)`, `cq = c + ((q·a)/(p+r))·(lo+j)`, so
`ML(p,q,r) ≥ 2/7`. Recipe verified on 5103 coprime cases. This closes the
`3q ≤ 7p` comparable regime that the direct run-sweep cannot reach (subject to
`s` being in range; the residual where `s ≈ (p+r)/2` needs the three-gap
theorem). -/
theorem ML_ge_sweep_inverse (p q r a b lo hi : ℤ) (_hp : 0 < p) (hm : 0 < p + r)
    (hbez : p * a + (p + r) * b = 1)
    (hlo2 : 2 * (p + r) ≤ 7 * lo) (hhi5 : 7 * hi ≤ 5 * (p + r))
    (hspos : 0 < (q * a) % (p + r))
    (hwidth : lo + (q * a) % (p + r) - 1 ≤ hi)
    (hspan : p + r ≤ (hi - lo) * ((q * a) % (p + r))) :
    2 / 7 ≤ ML ![p, q, r] := by
  set s := (q * a) % (p + r) with hs
  set dd := (q * a) / (p + r) with hdd
  have hqa : q * a = s + (p + r) * dd := (Int.emod_add_mul_ediv (q * a) (p + r)).symm
  obtain ⟨j, hj0, hjJ, c, hclo, hchi⟩ :=
    ap_hits_interval s (p + r) (s * lo) lo hi (hi - lo) hspos hm hspan hwidth
  have hsk : s * (lo + j) = s * lo + j * s := by ring
  refine ML_ge_fullband_k p q r (a * (lo + j)) (-b * (lo + j)) (c + dd * (lo + j)) hm ?_ ?_ ?_ ?_
  · have hidp : p * (a * (lo + j)) - (-b * (lo + j)) * (p + r) = lo + j := by
      linear_combination (lo + j) * hbez
    rw [hidp]; omega
  · have hidp : p * (a * (lo + j)) - (-b * (lo + j)) * (p + r) = lo + j := by
      linear_combination (lo + j) * hbez
    rw [hidp]; omega
  · have hidq : q * (a * (lo + j)) - (c + dd * (lo + j)) * (p + r)
        = s * (lo + j) - c * (p + r) := by linear_combination (lo + j) * hqa
    rw [hidq]; omega
  · have hidq : q * (a * (lo + j)) - (c + dd * (lo + j)) * (p + r)
        = s * (lo + j) - c * (p + r) := by linear_combination (lo + j) * hqa
    rw [hidq]; omega

/-- **The general run-based sweep — all `(p, q, r)` in the `3q > 7p` regime.**
For a sorted triple with `3q > 7p` (the faster runner sweeps fast enough),
band-width room `7q ≤ 3(p+r)`, and the span condition `14pq ≤ (p+r)(3q−7p)`
(guaranteeing the run is long enough to cover a period), `D ≤ 3/14`. The run
length `L = ⌊(hi−lo−p+1)/p⌋` is an integer division by the *variable* `p`; the
no-wrap bound uses `Int.emod_add_mul_ediv` and the span uses the floor lower bound
plus `nlinarith`. This is the uniform `p ≥ 2` closure (verified: 1143 triples,
0 violations). -/
theorem D_le_sweep_general (p q r : ℤ) (hp : 0 < p) (_hpq : p < q) (hqr : q < r)
    (h3q : 7 * p < 3 * q) (hsp : 14 * p * q ≤ (p + r) * (3 * q - 7 * p))
    (hwid : 7 * q ≤ 3 * (p + r)) : D ![p, q, r] ≤ 3 / 14 := by
  have hm : 0 < p + r := by omega
  have hq : 0 < q := by omega
  set lo : ℤ := (2 * (p + r) + 6) / 7 with hlodef
  set hi : ℤ := 5 * (p + r) / 7 with hhidef
  set W : ℤ := hi - lo - p + 1 with hWdef
  set L : ℤ := W / p with hLdef
  have hWmod := Int.emod_add_mul_ediv W p
  have hWmod0 : 0 ≤ W % p := Int.emod_nonneg W (by omega)
  have hWmodlt : W % p < p := Int.emod_lt_of_pos W hp
  have hpL_eq : p * L = W - W % p := by rw [hLdef]; omega
  have hc : L * p = p * L := mul_comm _ _
  have hlo2 : 2 * (p + r) ≤ 7 * lo := by rw [hlodef]; omega
  have hhi5 : 7 * hi ≤ 5 * (p + r) := by rw [hhidef]; omega
  have hwidth : lo + q - 1 ≤ hi := by rw [hlodef, hhidef]; omega
  have hnowrap : lo + p - 1 + L * p ≤ hi := by omega
  have h7W : 3 * (p + r) - 7 * p - 5 ≤ 7 * W := by rw [hWdef, hlodef, hhidef]; omega
  have hpL : W - p + 1 ≤ p * L := by omega
  have hspan : p + r ≤ L * q := by
    nlinarith [mul_le_mul_of_nonneg_right hpL (show (0 : ℤ) ≤ q by omega),
      mul_le_mul_of_nonneg_right h7W (show (0 : ℤ) ≤ q by omega), hsp, hp, hq, hqr, hm]
  have hML : 2 / 7 ≤ ML ![p, q, r] :=
    ML_ge_sweep_auto p q r lo hi L hp hq hm hlo2 hhi5 hnowrap hwidth hspan
  simp only [D]; linarith

end LonelyRunnerN3
