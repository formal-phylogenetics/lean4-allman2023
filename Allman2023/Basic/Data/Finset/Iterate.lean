module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Function.Iterate

/-!
# Iterating a growing map on finite sets

A map on the finite subsets of a finite type that never removes an element stops growing after as
many steps as the type has elements.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A growing map on finite sets stops growing, by the size of the type. -/
theorem iterate_card_fixed_of_subset (f : Finset α → Finset α) (hf : ∀ S, S ⊆ f S) {S : Finset α}
    (hS : S.Nonempty) : f (f^[Fintype.card α] S) = f^[Fintype.card α] S := by
  have key : ∀ k, f^[k + 1] S = f^[k] S ∨ k + 1 ≤ (f^[k] S).card := by
    intro k
    induction k with
    | zero => exact Or.inr (Finset.card_pos.mpr hS)
    | succ k ih =>
      by_cases he : f^[k + 1] S = f^[k] S
      · refine Or.inl ?_
        rw [Function.iterate_succ_apply', he]
        rwa [Function.iterate_succ_apply'] at he
      · refine Or.inr ?_
        rcases ih with ih | ih
        · exact absurd ih he
        · have hss : f^[k] S ⊂ f^[k + 1] S := by
            rw [Function.iterate_succ_apply']
            refine Finset.ssubset_iff_subset_ne.mpr ⟨hf _, fun h => he ?_⟩
            rw [Function.iterate_succ_apply', ← h]
          have := Finset.card_lt_card hss
          omega
  rcases key (Fintype.card α) with h | h
  · rwa [Function.iterate_succ_apply'] at h
  · have := Finset.card_le_univ (f^[Fintype.card α] S)
    omega

end Finset
