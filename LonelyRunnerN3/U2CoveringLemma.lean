/-
# The `{1,2,3}` covering lemma (combinatorial core of the n = 4 realization upper bound)

`min(‖n‖, ‖2n‖, ‖3n‖)_q ≤ ⌊q/4⌋`, where `‖x‖_q` is the distance from `x` to the nearest
multiple of `q`. Equivalently: one of `n, 2n, 3n` lies within `⌊q/4⌋` of a multiple of `q`.
This is the exact discrete `{1,2,3}` covering radius `M(q) = ⌊q/4⌋` (the `≤` half).

A companion to the n = 3 coordinate bound: this is the `m`-free statement that the
realization upper bound for the n = 4 U² family `{4m+3, 8, 4m+11, 4m+19}` reduces to. Via the
substitution `n = (A+8)p` the four runners at the dominant modulus `q = 8m+30` become the
`m`-independent multipliers `(3, −2, 1, −1)`, collapsing the tight four-runner covering to this
single lemma (see `U2_REALIZATION_PROOF.md` in the `lonely-runner-n4-spectrum` repository). It
closes the proof that `U²` realizes every `k ≡ 12 (mod 16)` with a proved exact value, hence
that the finite symmetric difference of Jain–Kravitz Theorem 1.3 is exactly `{1/3, 2/7}`.

Elementary, no `sorry`: reduce `n` to its residue `a = n mod q ∈ [0, q)`, then five explicit
`(coefficient, multiple)` choices tile `[0, q)`, each verified by `omega`.
-/
import Mathlib.Tactic

namespace LonelyRunnerN3
namespace Covering

/-- **The `{1,2,3}` covering lemma.** For `q > 0` and any integer `n`, some `c ∈ {1,2,3}`
makes `c·n` lie within `q/4` of a multiple `j·q` (i.e. `|c·n − j·q| ≤ ⌊q/4⌋`, written as
`4·|c·n − j·q| ≤ q`). Equivalently the discrete covering radius satisfies
`max_n min(‖n‖,‖2n‖,‖3n‖)_q ≤ ⌊q/4⌋`. -/
theorem one_two_three_cover (q : ℤ) (hq : 0 < q) (n : ℤ) :
    ∃ c j : ℤ, (c = 1 ∨ c = 2 ∨ c = 3) ∧
      4 * (c * n - j * q) ≤ q ∧ -q ≤ 4 * (c * n - j * q) := by
  -- residue reduction: n = q·d + a with 0 ≤ a < q
  obtain ⟨a, d, ha0, haq, hn⟩ : ∃ a d : ℤ, 0 ≤ a ∧ a < q ∧ n = q * d + a :=
    ⟨n % q, n / q, Int.emod_nonneg n (by omega), Int.emod_lt_of_pos n hq, by
      have := Int.mul_ediv_add_emod n q; omega⟩
  -- five (coefficient c, multiple j = c·d + e) choices tiling a ∈ [0, q)
  by_cases h1 : 4 * a ≤ q
  · -- a ≤ q/4 : runner 1 at j = d
    refine ⟨1, d, Or.inl rfl, ?_, ?_⟩ <;>
      · rw [show (1 : ℤ) * n - d * q = a by rw [hn]; ring]; omega
  · by_cases h2 : 12 * a ≤ 5 * q
    · -- q/4 < a ≤ 5q/12 : runner 3 at j = 3d + 1  (3a − q near 0)
      refine ⟨3, 3 * d + 1, Or.inr (Or.inr rfl), ?_, ?_⟩ <;>
        · rw [show (3 : ℤ) * n - (3 * d + 1) * q = 3 * a - q by rw [hn]; ring]; omega
    · by_cases h3 : 8 * a ≤ 5 * q
      · -- 5q/12 < a ≤ 5q/8 : runner 2 at j = 2d + 1  (2a − q near 0)
        refine ⟨2, 2 * d + 1, Or.inr (Or.inl rfl), ?_, ?_⟩ <;>
          · rw [show (2 : ℤ) * n - (2 * d + 1) * q = 2 * a - q by rw [hn]; ring]; omega
      · by_cases h4 : 12 * a ≤ 9 * q
        · -- 5q/8 < a ≤ 3q/4 : runner 3 at j = 3d + 2  (3a − 2q near 0)
          refine ⟨3, 3 * d + 2, Or.inr (Or.inr rfl), ?_, ?_⟩ <;>
            · rw [show (3 : ℤ) * n - (3 * d + 2) * q = 3 * a - 2 * q by rw [hn]; ring]; omega
        · -- 3q/4 < a < q : runner 1 at j = d + 1  (a − q near 0)
          refine ⟨1, d + 1, Or.inl rfl, ?_, ?_⟩ <;>
            · rw [show (1 : ℤ) * n - (d + 1) * q = a - q by rw [hn]; ring]; omega

/-- The covering radius is **at most** `⌊q/4⌋`, stated for the nearest-multiple distance
`|c·n − j·q|` minimized over the three runners. -/
theorem cover_dist_le (q : ℤ) (hq : 0 < q) (n : ℤ) :
    ∃ c j : ℤ, (c = 1 ∨ c = 2 ∨ c = 3) ∧ |c * n - j * q| ≤ q / 4 := by
  obtain ⟨c, j, hc, h1, h2⟩ := one_two_three_cover q hq n
  exact ⟨c, j, hc, by rw [abs_le]; omega⟩

end Covering
end LonelyRunnerN3
