module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Sums over functions that are read on a subtype

A sum over all functions `ι → β` of a quantity that depends only on their restriction to a subtype
is the sum over the restrictions, times the number of ways to choose the other values.
-/

@[expose] public section

open Finset

namespace Fintype

/-- A sum over functions of what they do on a subtype. -/
theorem sum_comp_restrict {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] (p : ι → Prop) [DecidablePred p] [Fintype {i // p i}]
    (A : Finset ι) (hA : ∀ i, i ∈ A ↔ ¬ p i) (h : ({i // p i} → β) → ℝ) :
    ∑ f : ι → β, h (fun i => f i.1) = (Fintype.card β : ℝ) ^ #A * ∑ f : {i // p i} → β, h f := by
  rw [← (Equiv.piEquivPiSubtypeProd p fun _ => β).symm.sum_comp, Fintype.sum_prod_type_right]
  have hconst : ∀ (g : {i // ¬ p i} → β), ∑ f : {i // p i} → β,
      h (fun i => (Equiv.piEquivPiSubtypeProd p fun _ => β).symm (f, g) i.1) =
        ∑ f : {i // p i} → β, h f := by
    intro g
    refine Finset.sum_congr rfl fun f _ => congrArg h (funext fun i => ?_)
    simp [Equiv.piEquivPiSubtypeProd, i.2]
  simp only [hconst, sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun]
  push_cast
  rw [Fintype.card_of_subtype A hA]

end Fintype
