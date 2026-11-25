# The results the paper cites

One directory per source, `Allman2023/External/<Source>/`, with modules
`Allman2023.External.<Source>.…`, declarations in the namespace `External.<Source>`, and a
`README.md` giving the source, the statement, how the paper uses it, whether the source was read,
and the argument that proves it. Each result is stated in its source's terms and proved; none is
assumed. These modules import Mathlib, `Allman2023/Basic/` and the libraries this repository
requires, never the paper's library.

A source that another repository of the collection already formalizes (lean4-phylogenetics, the
hubs lean4-phylo-network and lean4-tob, or the repository of a paper) is not formalized again: its statement here is proved
from that repository's theorem (lean4-phylogenetics, docs/CONVENTIONS.md, Sections 4 and 6).

| Source | Where | What the paper uses |
| --- | --- | --- |
| Semple, Steel 2005 | [`SempleSteel2005/`](SempleSteel2005) | the displayed quartets determine the tree, in the proof of Theorem 4; proved in lean4-phylogenetics (`Phylogenetics.mem_of_forall_displays`) and restated here |
| Rhodes 2020 | lean4-phylo-network, `PhyloNetwork/External/Rhodes2020/`, in the namespace `External.Rhodes2020` | the quartet intertaxon distance and its Theorem 2, cited with Semple and Steel in the proof of Theorem 4 and used in step 4 of the outline of an algorithm in Section 5 (`External.Rhodes2020.theorem2`, `External.Rhodes2020.exists_isExactBuilder`) |

The paper cites other works for definitions (Steel 2016 for the LSA, Gusfield et al. 2007 for the
tree of blobs, Baños 2019 for the semidirected network) and, in passing, for statements that no
proof uses (Allman, Degnan, Rhodes 2011 and Baños 2019 on the concordance factors of trees and of
level-1 networks; Sayyari, Mirarab 2016 on the lengths of edges). Those statements are proved in
the paper's library, on the paper's objects, and listed in `Allman2023/README.md`. The proof of
Theorem 4 also uses the uniqueness half of the Splits Equivalence Theorem (Semple, Steel 2003,
Theorem 3.1.4), for the form of the theorem with isomorphic trees; the paper doesn't cite it, and it
is proved in lean4-phylogenetics (`Phylogenetics.SplitsEquivalence.xTree_unique`).

## What the sources share with the paper's library

The cited results are stated on the definitions of lean4-phylogenetics and of the hub (split
families, quartet trees, `Displays`, `quartetDistance`), so the sources need no definition of the
paper. No module here imports the paper's library.
