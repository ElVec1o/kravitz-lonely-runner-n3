/-
# Master theorem: the n = 4 symmetric difference is exactly `{1/3, 2/7}`

This file states the headline result of the n = 4 exceptional-element work and proves the
**final assembly** sorry-free. It is honest about its trust surface (read this carefully).

## What is proved where

The complete, elementary proof of the result lives, with dependency-free exact-rational
verifiers, in the separate `lonely-runner-n4-spectrum` repository. It has two directions:

* **Realization (forward).** Every `k ≡ 4 (mod 8)`, `k ≥ 20`, `k ≠ 28` is realized by a
  `1`-dimensional subtorus of `U¹ ∪ U²`, at deficit `D = 1/4 + 1/k`. (`U¹` family `(1, 4j)`
  for `k ≡ 4 mod 16`; `U²` family `(4m+3, 8)` and `(1,7)` for `k ≡ 12 mod 16`.)
* **Exclusion (backward).** Every realized deficit in `(1/4, 1/2]` is `1/4 + 1/k` for some
  such `k`; in particular `1/3` and `2/7` are realized by no subtorus.

This file takes those two directions as **explicit, named hypotheses** (`realization`,
`exclusion`) — exactly as `PrimitiveWallReduction` took its `CoveringBound` — and proves the
remaining content: that the symmetric difference between the realized set and the
Jain–Kravitz progression is *exactly* `{1/3, 2/7}`. That final step (a finite arithmetic on
the index `k`) is what is machine-checked here.

## What is fully machine-checked (no hypotheses)

Two key lemmas of the directions above are formalized sorry-free in this repository and are
imported here as genuine, unconditional theorems:

* `Covering.one_two_three_cover` — the `{1,2,3}` covering lemma `min(‖n‖,‖2n‖,‖3n‖)_q ≤ ⌊q/4⌋`,
  the `m`-free core to which the `U²` realization **upper** bound reduces.  Axioms: `[propext, Quot.sound]`.
* `U1Family.ML_u1_family_ge` — `ML(1,2,3,4j) ≥ j/(4j+1)`, the `U¹` realization **lower** bound.

`#print axioms symmetric_difference` shows only `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`): the assembly is genuinely proved, conditional on the two named directions.
-/
import LonelyRunnerN3.U1FamilyBound
import LonelyRunnerN3.U2CoveringLemma
import Mathlib.Tactic

namespace LonelyRunnerN3
namespace Master

/-- The **realized** index set of the n = 4 spectrum in `(1/4, 1/2]`:
`k ≡ 4 (mod 8)`, `k ≥ 20`, and `k ≠ 28`. -/
def TargetK (k : ℕ) : Prop := k % 8 = 4 ∧ 20 ≤ k ∧ k ≠ 28

/-- The **Jain–Kravitz progression** index set: `k ≡ 4 (mod 8)`, `k ≥ 12`
(so `1/4 + 1/k ∈ (1/4, 1/3]`). -/
def ProgK (k : ℕ) : Prop := k % 8 = 4 ∧ 12 ≤ k

/-- `k ↦ 1/4 + 1/k` is injective on positive integers. -/
theorem val_inj {k k' : ℕ} (hk : 1 ≤ k) (hk' : 1 ≤ k')
    (h : (1 : ℝ) / 4 + 1 / (k : ℝ) = 1 / 4 + 1 / (k' : ℝ)) : k = k' := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk'0 : (0 : ℝ) < (k' : ℝ) := by exact_mod_cast hk'
  have e : (1 : ℝ) / (k : ℝ) = 1 / (k' : ℝ) := by linarith
  rw [div_eq_div_iff hk0.ne' hk'0.ne', one_mul, one_mul] at e
  exact_mod_cast e.symm

/-- **Master theorem (symmetric difference).** Let `Realized : ℝ → Prop` be the predicate
"realized by a `1`-dimensional subtorus of `U¹ ∪ U²` in `(1/4, 1/2]`". Given the two proved
directions — `realization` (every target index is realized) and `exclusion` (every realized
value is a target index) — the **symmetric difference** between the realized set and the
Jain–Kravitz progression `{1/4 + 1/k : k ≡ 4 mod 8, k ≥ 12}` is exactly `{1/3, 2/7}`. -/
theorem symmetric_difference
    (Realized : ℝ → Prop)
    (realization : ∀ k : ℕ, TargetK k → Realized (1 / 4 + 1 / (k : ℝ)))
    (exclusion : ∀ d : ℝ, Realized d → ∃ k : ℕ, TargetK k ∧ d = 1 / 4 + 1 / (k : ℝ)) :
    ∀ d : ℝ,
      (((∃ k : ℕ, ProgK k ∧ d = 1 / 4 + 1 / (k : ℝ)) ∧ ¬ Realized d) ∨
        (Realized d ∧ ¬ ∃ k : ℕ, ProgK k ∧ d = 1 / 4 + 1 / (k : ℝ)))
      ↔ (d = 1 / 3 ∨ d = 2 / 7) := by
  intro d
  constructor
  · rintro (⟨⟨k, ⟨hk4, hk12⟩, hd⟩, hnr⟩ | ⟨hr, hnp⟩)
    · -- in the progression but not realized  ⇒  k = 12 or k = 28
      -- ¬ Realized d, with d = 1/4 + 1/k, forces ¬ TargetK k (contrapositive of `realization`)
      have hntk : ¬ TargetK k := by
        intro htk; apply hnr; rw [hd]; exact realization k htk
      have : k < 20 ∨ k = 28 := by
        by_contra hcon
        exact hntk ⟨hk4, by omega, by omega⟩
      -- k ≡ 4 (mod 8) with 12 ≤ k < 20 gives k = 12; else k = 28
      have hk : k = 12 ∨ k = 28 := by omega
      rcases hk with rfl | rfl
      · left; rw [hd]; norm_num
      · right; rw [hd]; norm_num
    · -- realized but not in the progression: impossible (realized ⇒ in progression)
      obtain ⟨k, ⟨hk4, hk20, _⟩, hd⟩ := exclusion d hr
      exact absurd ⟨k, ⟨hk4, by omega⟩, hd⟩ hnp
  · -- 1/3 and 2/7 are each in the progression and not realized
    rintro (rfl | rfl)
    · refine Or.inl ⟨⟨12, ⟨by norm_num, by norm_num⟩, by norm_num⟩, ?_⟩
      intro hr
      obtain ⟨k, htk, hd⟩ := exclusion _ hr
      have hk1 : 1 ≤ k := le_trans (by norm_num) htk.2.1
      have hk12 : k = 12 := val_inj hk1 (by norm_num) (by rw [← hd]; norm_num)
      exact absurd (hk12 ▸ htk).2.1 (by norm_num)
    · refine Or.inl ⟨⟨28, ⟨by norm_num, by norm_num⟩, by norm_num⟩, ?_⟩
      intro hr
      obtain ⟨k, htk, hd⟩ := exclusion _ hr
      have hk1 : 1 ≤ k := le_trans (by norm_num) htk.2.1
      have hk28 : k = 28 := val_inj hk1 (by norm_num) (by rw [← hd]; norm_num)
      exact htk.2.2 hk28

end Master
end LonelyRunnerN3
