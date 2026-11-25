# General mathematics

Lemmas that say nothing about phylogenetics, filed by field as Mathlib files them and named as
Mathlib would name them, in Mathlib's namespaces, so that they can be contributed to Mathlib. They
import only Mathlib.

| File | Contents | Where it could go |
| --- | --- | --- |
| `Data/Finset/Card.lean` | the elements of a set of five are distinct (`Finset.ne_of_card_eq_five`); a set of four is nontrivial and has four names (`Finset.nontrivial_coe_of_card_eq_four`, `Finset.exists_eq_of_card_eq_four`); a third element of a set of two (`Finset.eq_of_mem_of_card_eq_two`); a type of four elements is nontrivial, has four distinct elements, and four distinct elements are all of it (`Fintype.nontrivial_of_card_eq_four`, `Fintype.exists_card_eq_four`, `Fintype.eq_or_eq_or_eq_or_eq_of_card_eq_four`) | `Mathlib/Data/Finset/Card.lean`, `Mathlib/Data/Fintype/Card.lean` |
| `Data/Finset/Iterate.lean` | a map on finite sets that never removes an element is fixed after as many steps as the type has elements (`Finset.iterate_card_fixed_of_subset`) | `Mathlib/Data/Fintype/Card.lean` |
| `Data/Set/Subtype.lean` | the image in the ambient type of the complement of a point of a subtype (`Set.image_val_compl_singleton`) | `Mathlib/Data/Set/Image.lean` |
| `Algebra/BigOperators/Pi.lean` | a sum over all functions of a quantity read on a subtype (`Fintype.sum_comp_restrict`) | `Mathlib/Data/Fintype/BigOperators.lean` |
| `Algebra/BigOperators/Intervals.lean` | the recursion of the geometric sum over `[1, k]` (`Finset.sum_Icc_one_pow_succ`) | `Mathlib/Algebra/BigOperators/Intervals.lean` |
| `Analysis/SpecialFunctions/Exp.lean` | `∑_{t < n} exp (-(t M))` is continuous in `M` and tends to `1` as `M → ∞` (`Real.continuous_sum_range_exp_neg_mul`, `Real.tendsto_sum_range_exp_neg_mul_atTop`) | `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `Analysis/Convex/Segment.lean` | some point of `(0, 1)` makes the entries of `γ p₁ + (1 - γ) p₀` distinct when any two entries differ in `p₁` or `p₀` (`exists_mem_Ioo_forall_ne`), which the proof of Theorem 1 uses to choose the parameters `γ` | `Mathlib/Analysis/Convex/Segment.lean` |

Some general facts stay where they are used, because they rest on the paper's notation: the
permutations of a set of four taxa that name its three quartet trees (`Allman2023.card_acbd`,
`Allman2023.insert_acbd`, …), and the arithmetic of the indices of the network `𝒩(k)⁺` of
Proposition 1.

Before adding a lemma, search Mathlib and lean4-phylogenetics (`Phylogenetics/ForMathlib/`): a
lemma that a second repository of the collection needs moves up the tree, to the lowest node above
both (lean4-phylogenetics, docs/CONVENTIONS.md, Section 4).
