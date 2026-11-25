module

public import Phylogenetics.Tree.Splits

/-!
# Semple, Steel 2005: a tree is determined by the quartet trees it displays

Allman et al. 2023 cite C. Semple and M. Steel, *Phylogenetics*, Oxford University Press, 2005,
together with Rhodes 2020, in the proof of Theorem 4: "the collection of displayed quartets determine
the tree". The library `Phylogenetics` proves the form that the proof uses, Steel's quartet theorem
for a split with two taxa on each side, as `Phylogenetics.mem_of_forall_displays`; it is restated
here, in the namespace of the source. See the `README.md` of this directory for what was read.
-/

@[expose] public section

namespace External.SempleSteel2005

open Finset Phylogenetics

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The displayed quartets determine the tree** (Semple, Steel 2005), for one split: an unrooted
tree, given by the sides of its splits, that displays every quartet tree with its cherries on the two
sides of `A | Aᶜ`, each side with at least two taxa, has the split `A | Aᶜ`. Proved in the library,
as `Phylogenetics.mem_of_forall_displays`. -/
theorem mem_of_forall_displays {T : Finset (Finset X)} (hT : IsUnrootedTree T) {A : Finset X}
    (hA : 2 ≤ A.card) (hA' : 2 ≤ Aᶜ.card) (h : ∀ s ∈ bipartitionQuartets A, Displays T s) : A ∈ T :=
  Phylogenetics.mem_of_forall_displays hT hA hA' h

end External.SempleSteel2005
