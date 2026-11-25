module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.Monoid

/-!
# Sums of decaying exponentials

`∑_{t < n} exp (-(t M))` is continuous in `M` and tends to `1`, its term at `t = 0`, as `M → ∞`.
-/

@[expose] public section

open Filter Topology Finset

namespace Real

/-- A finite sum of exponentials `exp (-(t M))` is continuous in `M`. -/
theorem continuous_sum_range_exp_neg_mul (n : ℕ) :
    Continuous fun M : ℝ => ∑ t ∈ range n, Real.exp (-((t : ℝ) * M)) := by
  fun_prop

/-- `∑_{t < n} exp (-(t M))` tends to `1` as `M → ∞`, for `n ≥ 1`. -/
theorem tendsto_sum_range_exp_neg_mul_atTop {n : ℕ} (hn : 0 < n) :
    Tendsto (fun M : ℝ => ∑ t ∈ range n, Real.exp (-((t : ℝ) * M))) atTop (𝓝 1) := by
  have hterm : ∀ t ∈ range n, Tendsto (fun M : ℝ => Real.exp (-((t : ℝ) * M))) atTop
      (𝓝 (if t = 0 then 1 else 0)) := by
    intro t _
    by_cases ht : t = 0
    · subst ht
      simp
    · rw [ite_eq_right ht]
      have ht' : (0 : ℝ) < t := Nat.cast_pos.2 (by omega)
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop ht'))
  have := tendsto_finsetSum (range n) hterm
  simpa [Finset.sum_ite_eq', Finset.mem_range, hn] using this

end Real
