/-
# U¹-family loneliness lower bound (n = 4 Lonely Runner; exceptional-element 2/7 work)

A companion application of the same loneliness infrastructure (`nearestIntDist`, `ML`,
`gap_le_ML`) used for the n = 3 coordinate bound, to the n = 4 spectrum near `1/4`.

For the U¹ subtorus speeds `{1, 2, 3, 4j}` (`j ≥ 1`), the rational time
`t = j/(4j+1)` certifies `ML(1,2,3,4j) ≥ j/(4j+1)`, hence the deficit
`D = 1/2 − ML ≤ 1/4 + 1/(16j+4)`.

This is the constructive (lower-bound) half of the U¹ characterization
`S(U¹) ∩ (1/4, 1/2] = { 1/4 + 1/(16j+4) : j ≥ 1 }` (companion note `U1_FAMILY.md` in the
`lonely-runner-n4-spectrum` repository), which pins the realized values to `k ≡ 4 (mod 16)`
and so excludes `k = 12` (`D = 1/3`) and `k = 28` (`D = 2/7`), the two exceptional elements
of the finite symmetric difference in Jain–Kravitz Theorem 1.3.

The fourth runner is handled by the integer-shift collapse already used in
`CoordConstruction.nid_runner_swap`: since `4j·t = j − t`, we get `‖4j·t‖ = ‖−t‖ = ‖t‖`.
Elementary, no `sorry`. At `t = j/(4j+1)` the four runner distances are
`‖1·t‖ = j/(4j+1)`, `‖2·t‖ = 2j/(4j+1)`, `‖3·t‖ = (j+1)/(4j+1)`, `‖4j·t‖ = j/(4j+1)`,
whose minimum is `j/(4j+1)`.
-/
import LonelyRunnerN3.NearestInteger
import LonelyRunnerN3.MaxLoneliness
import LonelyRunnerN3.DValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace LonelyRunnerN3
namespace U1Family

/-- **U¹ family lower bound.** At `t = j/(4j+1)` every runner of `{1,2,3,4j}`
is at nearest-integer distance `≥ j/(4j+1)`, so `ML(1,2,3,4j) ≥ j/(4j+1)`.
Equivalently `D(1,2,3,4j) ≤ 1/2 − j/(4j+1) = 1/4 + 1/(16j+4)`. -/
theorem ML_u1_family_ge (j : ℕ) (hj : 1 ≤ j) :
    ((j : ℝ) / (4 * (j : ℝ) + 1)) ≤ ML ![(1 : ℤ), 2, 3, 4 * (j : ℤ)] := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hd : (0 : ℝ) < 4 * (j : ℝ) + 1 := by linarith
  set t : ℝ := (j : ℝ) / (4 * (j : ℝ) + 1) with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hd]; linarith
  have h2 : 2 * t < 1 := by
    rw [ht, show (2 : ℝ) * ((j : ℝ) / (4 * (j : ℝ) + 1))
      = (2 * (j : ℝ)) / (4 * (j : ℝ) + 1) by ring, div_lt_one hd]; linarith
  have h3 : 3 * t < 1 := by
    rw [ht, show (3 : ℝ) * ((j : ℝ) / (4 * (j : ℝ) + 1))
      = (3 * (j : ℝ)) / (4 * (j : ℝ) + 1) by ring, div_lt_one hd]; linarith
  have h4 : 4 * t < 1 := by
    rw [ht, show (4 : ℝ) * ((j : ℝ) / (4 * (j : ℝ) + 1))
      = (4 * (j : ℝ)) / (4 * (j : ℝ) + 1) by ring, div_lt_one hd]; linarith
  -- the four runner distances at `t`, each `≥ t = j/(4j+1)`
  have hb1 : t ≤ nearestIntDist (((1 : ℤ) : ℝ) * t) := by
    rw [Int.cast_one, one_mul]; exact nearestIntDist_ge ht0 ht1 le_rfl (by linarith)
  have hb2 : t ≤ nearestIntDist (((2 : ℤ) : ℝ) * t) := by
    rw [show ((2 : ℤ) : ℝ) * t = 2 * t by push_cast; ring]
    exact nearestIntDist_ge (by linarith) h2 (by linarith) (by linarith)
  have hb3 : t ≤ nearestIntDist (((3 : ℤ) : ℝ) * t) := by
    rw [show ((3 : ℤ) : ℝ) * t = 3 * t by push_cast; ring]
    exact nearestIntDist_ge (by linarith) h3 (by linarith) (by linarith)
  -- fourth runner: `4j·t = -t + j`, so `‖4j·t‖ = ‖-t‖ = ‖t‖`
  have hb4 : t ≤ nearestIntDist (((4 * (j : ℤ)) : ℝ) * t) := by
    rw [show (4 : ℝ) * ((j : ℤ) : ℝ) * t = -t + ((j : ℤ) : ℝ) by
          rw [ht]; field_simp; push_cast; ring,
        nearestIntDist_add_int, nearestIntDist_neg]
    exact nearestIntDist_ge ht0 ht1 le_rfl (by linarith)
  refine le_trans ?_ (gap_le_ML _ t)
  apply le_gap
  intro i
  fin_cases i
  · simpa using hb1
  · simpa using hb2
  · simpa using hb3
  · simpa using hb4

/-- **Deficit form.** `D(1,2,3,4j) ≤ 1/4 + 1/(16j+4)`. Together with the matching upper
bound on `ML` (the value is in fact exactly `j/(4j+1)`; proved in the companion note
`U1_FAMILY.md`), the U¹ family realizes precisely the deficits `1/4 + 1/(16j+4)`, i.e.
`1/4 + 1/k` with `k ≡ 4 (mod 16)`. In particular it never realizes `2/7` (`k = 28`) or
`1/3` (`k = 12`), the two exceptional elements. -/
theorem D_u1_family_le (j : ℕ) (hj : 1 ≤ j) :
    D ![(1 : ℤ), 2, 3, 4 * (j : ℤ)] ≤ 1 / 4 + 1 / (16 * (j : ℝ) + 4) := by
  have hpos : (0 : ℝ) < 4 * (j : ℝ) + 1 := by positivity
  have e : (1 : ℝ) / 2 - (j : ℝ) / (4 * (j : ℝ) + 1) = 1 / 4 + 1 / (16 * (j : ℝ) + 4) := by
    have h1 : (4 * (j : ℝ) + 1) ≠ 0 := ne_of_gt hpos
    have h2 : (16 * (j : ℝ) + 4) ≠ 0 := by positivity
    field_simp
    ring
  have h := ML_u1_family_ge j hj
  unfold D
  linarith [h, e]

end U1Family
end LonelyRunnerN3
