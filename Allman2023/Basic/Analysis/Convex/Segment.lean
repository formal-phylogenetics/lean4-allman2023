module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# Points of a segment that separate finitely many values

For two vectors `p₁`, `p₀` indexed by a finite set, all but finitely many `γ` make the entries of the
combination `γ p₁ + (1 - γ) p₀` pairwise distinct, as long as any two entries differ in one of the
vectors: each difference is a nonzero affine function of `γ`.
-/

@[expose] public section

/-- If any two entries differ in one of two vectors `p₁`, `p₀`, then some `γ ∈ (0, 1)` makes all the
entries of `γ p₁ + (1 - γ) p₀` distinct: for each two entries, the difference is a nonzero affine
function of `γ`, with at most one zero. -/
theorem exists_mem_Ioo_forall_ne {ι : Type*} (T : Finset ι) (p₁ p₀ : ι → ℝ)
    (h : ∀ r ∈ T, ∀ r' ∈ T, r ≠ r' → p₁ r ≠ p₁ r' ∨ p₀ r ≠ p₀ r') :
    ∃ γ ∈ Set.Ioo (0 : ℝ) 1, ∀ r ∈ T, ∀ r' ∈ T, r ≠ r' →
      γ * p₁ r + (1 - γ) * p₀ r ≠ γ * p₁ r' + (1 - γ) * p₀ r' := by
  let bad : ι → ι → Set ℝ := fun r r' => {γ | r ≠ r' ∧ γ * p₁ r + (1 - γ) * p₀ r = γ * p₁ r' + (1 - γ) * p₀ r'}
  have hsub : ∀ r ∈ T, ∀ r' ∈ T, (bad r r').Subsingleton := by
    rintro r hr r' hr' γ ⟨hne, hγ⟩ γ' ⟨-, hγ'⟩
    by_contra hγγ
    have hab : p₁ r - p₁ r' = p₀ r - p₀ r' := by
      have h0 : (γ - γ') * ((p₁ r - p₁ r') - (p₀ r - p₀ r')) = 0 := by linear_combination hγ - hγ'
      have := (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hγγ)
      linarith
    have hb : p₀ r - p₀ r' = 0 := by
      have h0 : γ * (p₁ r - p₁ r') + (1 - γ) * (p₀ r - p₀ r') = 0 := by linear_combination hγ
      rw [hab] at h0
      linear_combination h0
    rcases h r hr r' hr' hne with h' | h'
    · exact h' (by linarith)
    · exact h' (by linarith)
  have hfin : (⋃ r ∈ T, ⋃ r' ∈ T, bad r r').Finite :=
    T.finite_toSet.biUnion fun r hr => T.finite_toSet.biUnion fun r' hr' => (hsub r hr r' hr').finite
  obtain ⟨γ, hγ, hnot⟩ := (Set.Ioo_infinite (zero_lt_one' ℝ)).exists_notMem_finite hfin
  refine ⟨γ, hγ, fun r hr r' hr' hne heq => hnot ?_⟩
  exact Set.mem_biUnion hr (Set.mem_biUnion hr' ⟨hne, heq⟩)

/-! ### From (a) and (b) to the iff -/
