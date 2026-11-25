module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Geometric sums over `[1, k]`
-/

@[expose] public section

namespace Finset

/-- The recursion of the geometric sum over `[1, k]`. -/
theorem sum_Icc_one_pow_succ (r : ℝ) (k : ℕ) :
    ∑ ℓ ∈ Finset.Icc 1 (k + 1), r ^ ℓ = r + r * ∑ ℓ ∈ Finset.Icc 1 k, r ^ ℓ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 := Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1) fun ℓ => r ^ ℓ
    rw [Finset.sum_Icc_succ_top (by omega)]
    linear_combination ih - r * h2

end Finset
