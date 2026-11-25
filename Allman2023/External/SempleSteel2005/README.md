# Semple, Steel 2005: the displayed quartets determine the tree

Source: C. Semple, M. Steel, *Phylogenetics*, Oxford University Press, 2005. **The book wasn't
read** for this statement.

Allman et al. 2023 cite it with Rhodes 2020 in the proof of Theorem 4: "But the collection of
displayed quartets determine the tree (Semple and Steel 2005; Rhodes 2020), so the tree of blobs is
identifiable". The proof applies it to the reduced unrooted tree of blobs, given by the sides of its
splits, and to the quartet trees that it displays.

`Quartets.lean` states the form that the proof uses, for one split: an unrooted tree that displays
every quartet tree with its cherries on the two sides of `A | Aᶜ`, each side with at least two taxa,
has that split (`External.SempleSteel2005.mem_of_forall_displays`). Splits with one taxon on a side
are those of the pendant edges, which every tree has. The paper's
`Allman2023.treeFromQuartets_displays` (`a:claim:displayed-determine`) deduces from it that the
splits of a tree are exactly those all of whose quartet trees it displays.

It is proved in lean4-phylogenetics, as `Phylogenetics.mem_of_forall_displays` in
`Phylogenetics/Tree/Splits.lean`, which calls it the case of Steel's quartet theorem for splits with
two taxa on each side. The argument roots the tree at a taxon `b` of `Aᶜ` and shows that the least
cluster containing `A` is `A`: otherwise that cluster has a taxon `b₂` outside `A`, one of its children
separates two taxa `a₁`, `a₂` of `A`, and the tree cannot display the quartet tree `a₁a₂|bb₂`.
