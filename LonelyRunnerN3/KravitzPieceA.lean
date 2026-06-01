/-
# Piece A closed: the n=3 coordinate bound

Combines the two halves into the full coordinate bound (the hard direction of paper
Prop 2.2): **every sorted primitive triple `0<p<q<r` other than `(1,2,3)` has `D ≤ 3/14`.**

- Large coordinates `r > 30`: `D_le_of_large` (Kravitz Theorem 7.2, this formalization).
- Small coordinates `r ≤ 30`: the finite `native_decide` enumeration `triple_outside`
  (`D3Classify`), here shown *exhaustive* over all sorted primitive triples in range.

`(1,2,3)` is the unique triple with `D > 3/14` (`D = 1/4`); all others lie at or below the
`3/14` threshold. No `sorry`.
-/

import LonelyRunnerN3.KravitzHookup
import LonelyRunnerN3.KravitzStrict
import LonelyRunnerN3.D3Classify

namespace LonelyRunnerN3

/-- The coords-`≤30` certificate list is exhaustive over sorted primitive triples
(other than `(1,2,3)`). Pure `native_decide`. -/
theorem r30_exhaustive_nat :
    ∀ p ∈ List.range 31, ∀ q ∈ List.range 31, ∀ r ∈ List.range 31,
      0 < p → p < q → q < r → Int.gcd (p : ℤ) (Int.gcd (q : ℤ) (r : ℤ)) = 1 →
      ¬(p = 1 ∧ q = 2 ∧ r = 3) → ((p : ℤ), (q : ℤ), (r : ℤ)) ∈ tripleData.map Prod.fst := by
  native_decide

/-- `ℤ`-form of exhaustiveness: a sorted primitive triple with `r ≤ 30` (≠ `(1,2,3)`) is listed. -/
theorem r30_listed (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r) (hr : r ≤ 30)
    (hg : Int.gcd p (Int.gcd q r) = 1) (hne : ¬(p = 1 ∧ q = 2 ∧ r = 3)) :
    (p, q, r) ∈ tripleData.map Prod.fst := by
  have e1 : ((p.toNat : ℤ)) = p := Int.toNat_of_nonneg (by omega)
  have e2 : ((q.toNat : ℤ)) = q := Int.toNat_of_nonneg (by omega)
  have e3 : ((r.toNat : ℤ)) = r := Int.toNat_of_nonneg (by omega)
  have hmem := r30_exhaustive_nat p.toNat (by simp only [List.mem_range]; omega)
    q.toNat (by simp only [List.mem_range]; omega) r.toNat (by simp only [List.mem_range]; omega)
    (by omega) (by omega) (by omega) (by rw [e1, e2, e3]; exact hg)
    (by rintro ⟨h1, h2, h3⟩; exact hne ⟨by omega, by omega, by omega⟩)
  rw [e1, e2, e3] at hmem; exact hmem

/-- **Piece A — the coordinate bound (Kravitz Theorem 7.2, lower direction), fully closed.**
For a sorted primitive triple `0 < p < q < r` with `(p,q,r) ≠ (1,2,3)` (primitivity in the
usable form `IsCoprime p (gcd q r)`, `IsCoprime q (gcd p r)`), we have `D(p,q,r) ≤ 3/14`.
Hence `(1,2,3)` (with `D = 1/4`) is the unique primitive triple strictly above the `3/14`
threshold, and the `S₁(3) ∩ (3/14, 1/2]` band is `{(1,2,3)}` — closing the hard direction of
Proposition 2.2 with no remaining coordinate hypothesis. -/
theorem D_le_of_not_123 (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hcop_p : IsCoprime p (Int.gcd q r : ℤ)) (hcop_q : IsCoprime q (Int.gcd p r : ℤ))
    (hne : ¬(p = 1 ∧ q = 2 ∧ r = 3)) :
    D ![p, q, r] ≤ 3 / 14 := by
  rcases le_or_gt r 30 with hle | hgt
  · have hg : Int.gcd p (Int.gcd q r) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop_p
    obtain ⟨pp, hpp_mem, hpp_eq⟩ := List.mem_map.mp (r30_listed p q r hp hpq hqr hle hg hne)
    have hd := triple_outside pp hpp_mem
    rw [hpp_eq] at hd
    simpa [mkV] using hd
  · exact D_le_of_large p q r hp hpq hqr hgt hcop_p hcop_q

/-- **THE COORDINATE BOUND (no caveat).** For a sorted primitive triple, `D(p,q,r) ≥ 3/14`
forces `r ≤ 30`. (The strict large-coordinate bound `D_lt_of_large` rules out `D = 3/14` for
`r > 30`, so there is no boundary exception.) Combined with the finite enumeration, the
`S₁(3)` triples at or above `3/14` are *exactly* the five members of `L₃` — closing the hard
direction of Proposition 2.2 completely. -/
theorem coord_bound (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hcop_p : IsCoprime p (Int.gcd q r : ℤ)) (hcop_q : IsCoprime q (Int.gcd p r : ℤ))
    (hD : 3 / 14 ≤ D ![p, q, r]) : r ≤ 30 := by
  by_contra h
  exact absurd (D_lt_of_large p q r hp hpq hqr (by omega) hcop_p hcop_q) (not_lt.mpr hD)

/-- **`(1,2,3)` is the unique primitive triple strictly above the `3/14` threshold.** The
direct consequence of the coordinate bound: `D(p,q,r) > 3/14 ⟹ (p,q,r) = (1,2,3)`. This is
the `n=3` input needed for `δ₂(4) ≤ 3/14` — the band `S₁(3) ∩ (3/14, 1/2]` is `{(1,2,3)}`. -/
theorem unique_above_threshold (p q r : ℤ) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hcop_p : IsCoprime p (Int.gcd q r : ℤ)) (hcop_q : IsCoprime q (Int.gcd p r : ℤ))
    (hD : 3 / 14 < D ![p, q, r]) : p = 1 ∧ q = 2 ∧ r = 3 := by
  by_contra h
  exact absurd (D_le_of_not_123 p q r hp hpq hqr hcop_p hcop_q h) (not_le.mpr hD)

/-- **Demonstration:** a concrete large triple `(7, 50, 53)` (`r=53 > 30`, coprime structure)
is below threshold — the machine proves `D(7,50,53) ≤ 3/14`. -/
example : D ![7, 50, 53] ≤ 3 / 14 :=
  D_le_of_not_123 7 50 53 (by norm_num) (by norm_num) (by norm_num)
    (by rw [show (Int.gcd 50 53 : ℤ) = 1 from by decide]; exact isCoprime_one_right)
    (by rw [show (Int.gcd 7 53 : ℤ) = 1 from by decide]; exact isCoprime_one_right)
    (by norm_num)

-- ============================================================================
-- AXIOM AUDIT: force Lean to list every foundational axiom each capstone rests on.
-- A genuine proof shows ONLY [propext, Classical.choice, Quot.sound]. The presence
-- of `sorryAx` would mean a `sorry` was hidden somewhere in the dependency tree.
-- ============================================================================
#print axioms coord_bound
#print axioms D_le_of_not_123
#print axioms unique_above_threshold
#print axioms D_lt_of_large
#print axioms ML_gt_of_large
#print axioms double_band_cover
#print axioms double_band_cover_strict

end LonelyRunnerN3
