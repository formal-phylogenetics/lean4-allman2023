# Allman et al. 2023: the tree of blobs of a species network, identifiability, in Lean

[![CI](https://github.com/vltanh/lean4-allman2023/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-allman2023/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network: identifiability under the coalescent*, [J. Math. Biol. 86 (2023), 10](https://doi.org/10.1007/s00285-022-01838-9), read in the PMC author manuscript and the [arXiv TeX](https://arxiv.org/abs/2205.03466). The tree of blobs of a phylogenetic network is what remains when its reticulate parts, the blobs, are contracted. The paper proves that under the network multispecies coalescent, for generic parameters, the reduced unrooted tree of blobs of a binary species network is identifiable from the distribution of gene quartet topologies, with no assumption on the level of the network. On four taxa, the concordance factor detects a 4-blob (Theorem 1). On more taxa, the B-quartet Inference Rule (Theorem 2) finds all B-quartets from the concordance factors (Theorem 3), and from these the tree is recovered (Theorem 4).

Every numbered result is proved, by the paper's arguments except the departures that [Section 7 of the report](docs/Allman2023/REPORT.md#7-departures-from-the-papers-proofs) lists. The formalization is unconditional: no result of the literature is assumed, and there is no `sorry` or `axiom` outside the Challenge's statements. Lemma 2 is proved for a connected subnetwork, which its proof and all its uses assume (E55). No person has reviewed the proofs.

This paper is one of the four of the hub [lean4-phylo-tree-of-blobs](https://github.com/vltanh/lean4-phylo-tree-of-blobs), a sub-hub of [lean4-phylo-network](https://github.com/vltanh/lean4-phylo-network), which presents them; TINNiK, TOB-QMC and ECToBlob build on it.

## Status

| Part of the paper | Status |
| --- | --- |
| §2: Definitions 1 to 15, and what the section says of blobs, trees of blobs and the LSA | proved |
| §3: Lemma 1, Theorem 1, Corollary 1, Proposition 1 and its converse | proved |
| §4: Lemma 2, Corollary 2, Theorem 2, Lemma 3, Theorem 3 | proved; Lemma 2 for a connected subnetwork (E55) |
| §5: Theorem 4 | proved, and with the trees isomorphic as labelled graphs |
| §5: the outline of an algorithm, the distance between blobs, the lengths of edges between trivial blobs | proved; the last for internal edges (E64) |
| Figures 1, 2, 3 and 9 | their claims proved |
| Cited results: Semple, Steel 2005 and Rhodes 2020 (Theorem 4); Rhodes 2020, Theorem 2 (the outline) | proved, in lean4-phylogenetics and lean4-phylo-network, and stated in [`Allman2023/External/`](Allman2023/External) |
| Baños's bound on the concordance factors of all level-1 networks, quoted before Proposition 1 | not formalized; nothing uses it |

[Section 9 of the report](docs/Allman2023/REPORT.md#9-not-formalized) lists what is not formalized, and [`Allman2023/README.md`](Allman2023/README.md) what the paper says in passing and where it is proved.

## Main results

The statements of record are the theorems of the Challenge, [`palomar/Allman2023/Challenge.lean`](palomar/Allman2023/Challenge.lean), in the namespace `Allman2023Challenge`. The Challenge imports only Mathlib, and its definitions are those of [`Allman2023/Defs.lean`](Allman2023/Defs.lean), copied by [`scripts/sync_challenge_defs.py`](scripts/sync_challenge_defs.py): the paper's networks (Definition 1), parameters (Definition 3), concordance factors under the network multispecies coalescent (Definition 14), cut concordance factors (Definition 15), B-quartets (Definition 12), and the reduced unrooted tree of blobs (Definitions 10 and 11), given by the sides of its splits, which are those of the cut edges of the network. [`palomar/Allman2023/Solution.lean`](palomar/Allman2023/Solution.lean) proves each of them, under the same name, from the library, through the bridges of [`Allman2023/Bridge/`](Allman2023/Bridge). They keep the paper's hypotheses.

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem 1 | [`Allman2023Challenge.theorem1`](palomar/Allman2023/Challenge.lean#L574) | on four taxa, for generic parameters, the reduced unrooted tree of blobs has the topology `ab\|cd` exactly when `CF_abcd` is strictly `(ab\|cd)`-cut, and is unresolved exactly when `CF_abcd` is non-cut |
| Corollary 1 | [`Allman2023Challenge.corollary1`](palomar/Allman2023/Challenge.lean#L586) | on any number of taxa, for generic parameters, [`readTopology`](Allman2023/Networks/Concordance.lean#L295), a function of `CF_abcd` alone, reads the topology of the reduced unrooted tree of blobs of each induced 4-taxon network |
| Proposition 1 | [`Allman2023Challenge.proposition1`](palomar/Allman2023/Challenge.lean#L595) | for all parameters, the concordance factor of a 4-taxon network whose reduced tree of blobs is `ab\|cd` is a triple `(p, q, q)` with `0 < p, q < 1` and `p + 2q = 1` |
| Proposition 1, converse | [`Allman2023Challenge.proposition1_converse`](palomar/Allman2023/Challenge.lean#L605) | every such triple arises on such a network |
| Theorem 2 | [`Allman2023Challenge.theorem2`](palomar/Allman2023/Challenge.lean#L617) | the B-quartet Inference Rule: if `{a, b, c, d}` and `{b, c, d, e}` are B-quartets, and one of `{a, b, c, e}`, `{a, b, d, e}`, `{a, c, d, e}` is, on its induced network, a T-quartet with `a, e` separated or a B-quartet, then all three are B-quartets |
| Theorem 3 | [`Allman2023Challenge.theorem3`](palomar/Allman2023/Challenge.lean#L629) | for generic parameters, the sets that `CF`-detectability and the Inference Rule give from the concordance factors, [`CFInferred`](Allman2023/Networks/Concordance.lean#L321), are exactly the B-quartets |
| Theorem 4 | [`Allman2023Challenge.theorem4`](palomar/Allman2023/Challenge.lean#L639) | one function `F`, chosen before the network, recovers the reduced unrooted tree of blobs from the distribution of gene quartet topologies, for generic parameters on every binary network |

### Also proved in the library

| Paper | Lean | Statement |
| --- | --- | --- |
| Lemma 1 | [`Allman2023.lemma1`](Allman2023/FourTaxa/Lemma1.lean#L50) | on four taxa, `𝒩⁻` has either one 4-blob, an unresolved tree of blobs and a B-quartet, or two 3-blobs, a resolved tree and a T-quartet; its other blobs without a taxon are 2-blobs |
| Lemma 2 | [`Allman2023.lemma2`](Allman2023/LargeNetworks/Lemma2.lean#L146) | a set of taxa that determines a blob of a connected subnetwork determines a blob of the network, and the cut edges of that blob leading to the taxa are in the subnetwork |
| Lemma 2, literally | [`Allman2023.lemma2_needs_connected`](Allman2023/LargeNetworks/Lemma2Counterexample.lean#L163) | without a connected subnetwork, the hypotheses of Lemma 2 hold and no blob of the network is determined (E55) |
| Corollary 2 | [`Allman2023.corollary2`](Allman2023/LargeNetworks/Corollary2.lean#L53) | a B-quartet on an induced network is a B-quartet on the network |
| Lemma 3 | [`Allman2023.lemma3`](Allman2023/LargeNetworks/Lemma3.lean#L35) | if `{a, b, c, d}` is a B-quartet and the network induced on `X ∖ {α}` has a cut edge separating `a, b` from `c, d`, then `{a, b, c, α}` is a B-quartet on the network induced on `X ∖ {d}` |
| Theorem 4, isomorphic trees | [`Allman2023.theorem4_iso`](Allman2023/MainResult/Theorem4.lean#L134) | two networks with the same distribution of gene quartet topologies, off null sets of parameters, have isomorphic reduced unrooted trees of blobs, as labelled graphs |
| §5, the outline | [`Allman2023.Algorithm.outline_consistent`](Allman2023/MainResult/Algorithm.lean#L232) | for any test right on each set of four taxa with probability tending to one, and an exact tree builder, the steps of the outline return the tree of blobs with probability tending to one |
| §5, the distance between blobs | [`Allman2023.InPassing.blobDistance_not_identifiable`](Allman2023/MainResult/BlobDistance.lean#L115) | on `𝒩(k)⁺`, for every `k ≥ 1` and stem length `ε₀ > 0`, a segment of concordance factors arises at `ε₀` and at every `ε′` near it |
| Before Proposition 1, Baños's range | [`Allman2023.NetworkNk.banos_range`](Allman2023/FourTaxa/NetworkOne.lean#L795) | `𝒩(1)⁺` is level-1 with tree of blobs `ab\|cd`, and the first entry of its concordance factor takes exactly the values in `(1/6, 1)` |

### The sources

| Source | Lean | Statement |
| --- | --- | --- |
| Semple, Steel 2005; Rhodes 2020, in the proof of Theorem 4 | [`External.SempleSteel2005.mem_of_forall_displays`](Allman2023/External/SempleSteel2005/Quartets.lean#L27) | an unrooted tree that displays every quartet tree across a split with two taxa on each side has that split; proved in lean4-phylogenetics, [`Phylogenetics.mem_of_forall_displays`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/Tree/Splits.lean#L638) |
| Rhodes 2020, Theorem 2, in step 4 of the outline | [`External.Rhodes2020.theorem2`](https://github.com/vltanh/lean4-phylo-network/blob/4ed2bb0f7085acbf1326f43e2a5c582ba4566125/PhyloNetwork/External/Rhodes2020/Theorem2.lean#L777) | the quartet intertaxon distance is a tree metric on the tree; proved in lean4-phylo-network |
| Semple, Steel 2003, Theorem 3.1.4 (not cited by the paper) | [`Phylogenetics.SplitsEquivalence.xTree_unique`](https://github.com/vltanh/lean4-phylogenetics/blob/3fcabfd7d191990dda268b0b3968d945b65eb59a/Phylogenetics/Tree/SplitsEquivalence.lean#L604) | a tree is determined by its splits, up to isomorphism, for [`Allman2023.theorem4_iso`](Allman2023/MainResult/Theorem4.lean#L134); proved in lean4-phylogenetics |

## What the audit found

| Finding | Where |
| --- | --- |
| No numbered result fails, reading a subnetwork as connected; read literally, Lemma 2 does, and its proof and all its uses assume the word | E55 |
| A side remark in the proof of Proposition 1 is false for some `ε` | E57 |
| The remark at line 252 that edge lengths between trivial blobs are identifiable holds for internal edges | E64 |
| The proofs have gaps, all filled with no change of statement | E56, E58–E62 |
| Misprints, some in the PMC manuscript only; "`k` or `M` varied" is loose | E57, E63, E65, E66 |
| Baños 2019, which the paper cites, has a misprint in the proof of its Proposition 7 | E81 |

[Section 3 of the report](docs/Allman2023/REPORT.md#3-errors-and-gaps-in-the-paper) gives each finding with its location, the paper's sentence, a Lean counterexample where there is one, and the repair; [Section 5](docs/Allman2023/REPORT.md#5-redundant-hypotheses) gives the redundant hypotheses, among them the binary hypothesis in Theorem 2, Lemma 3 and the combinatorial part of Theorem 3. The proofs follow the paper's arguments, except the departures in [Section 7 of the report](docs/Allman2023/REPORT.md#7-departures-from-the-papers-proofs), each with what the paper does, what Lean does and why: statement (b) of Theorem 1 also removes a stem, which the paper's step needs (E58); statement (a) of Theorem 1, Theorem 2 and Baños's claim depart where it isn't forced, and say so; Lemma 1, the remark on the distance between blobs, the outline of Section 5 and other remarks have no printed argument to follow.

## Trust

- `lake build` passes; the only warnings are the `sorry`s of the Challenge's statements. There is no `sorry`, `axiom`, `native_decide` or `implemented_by` in [`Allman2023/`](Allman2023) or in the Solution.
- [`scripts/Audit.lean`](scripts/Audit.lean) checks every declaration of this repository and of the libraries it requires, `Phylogenetics`, `PhyloNetwork` and `TreeOfBlobs`, including private and generated ones, against [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and writes the routes of the proofs.
- [`scripts/route_check.py`](scripts/route_check.py) compares those routes with the paper's, in [`docs/Allman2023/paper_routes.tsv`](docs/Allman2023/paper_routes.tsv); [`docs/Allman2023/route_differences.tsv`](docs/Allman2023/route_differences.tsv) records every difference, with its reason.
- Comparator checks that the Solution proves exactly the Challenge's statements, under Lean's kernel and NanoDa; [`scripts/check_kernels.sh`](scripts/check_kernels.sh) runs it, and con-ron on an export of the same theorems.
- **No person has reviewed the proofs.** Independent agents reviewed the statements against the paper, compared the proofs with the paper's, and checked the findings.

## Dependencies

- [Mathlib](https://github.com/leanprover-community/mathlib4), at `v4.37.0-rc1`.
- [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics), the library of the collection, pinned by commit in [`lakefile.toml`](lakefile.toml): networks, blobs and their contraction, the semidirected network, trees and quartets, Kingman's coalescent and the network multispecies coalescent, null sets of parameters and the analytic argument behind generic parameters.
- [lean4-phylo-network](https://github.com/vltanh/lean4-phylo-network), the library of the hub of network estimation, pinned by commit: the theorem of Rhodes 2020, the chain of the coalescent on explicit networks, and independent samples.
- [lean4-phylo-tree-of-blobs](https://github.com/vltanh/lean4-phylo-tree-of-blobs), the library of this paper's hub, pinned by commit: the definitions of the algorithms of the later papers, among them the closure under the B-quartet Inference Rule (`BInferred`), which the outline of Section 5 uses.

## Palomar

No submission to Palomar is planned. [`palomar/Allman2023/`](palomar/Allman2023) has the files of an entry: the Challenge, which imports only Mathlib, the Solution, [`comparator.json`](palomar/Allman2023/comparator.json), which names them and the 7 theorems, and [`formalization.yaml`](palomar/Allman2023/formalization.yaml), the entry's metadata, with the statements aligned to the Challenge's theorems and every divergence from the paper. From the repository root, after `lake build`, run [`scripts/check_kernels.sh`](scripts/check_kernels.sh). CI checks that the Challenge's copy of the definitions is the block of [`Allman2023/Defs.lean`](Allman2023/Defs.lean) (`python3 scripts/sync_challenge_defs.py --check`).

## Building

From the root of the repository:

```sh
lake exe cache get
lake build
lake build Phylogenetics PhyloNetwork TreeOfBlobs                    # the libraries that the audit reads
lake env lean scripts/Audit.lean                                     # axioms and dependencies
python3 scripts/route_check.py check docs/Allman2023/paper_routes.tsv --accept docs/Allman2023/route_differences.tsv
scripts/check_kernels.sh                                             # Comparator: Lean's kernel, NanoDa; con-ron
python3 scripts/linkify_docs.py                                      # the documents' links to the code
```

- Toolchain: Lean and Mathlib `v4.37.0-rc1` ([`lean-toolchain`](lean-toolchain), [`lake-manifest.json`](lake-manifest.json)).
- `lake comparator`, `leanexport` and `con-ron` come from the toolchain, under `lake env`. The kernels' replays need much memory.
- [lean4-phylo-tree-of-blobs's `docs/CONFIGURATION.md`](https://github.com/vltanh/lean4-phylo-tree-of-blobs/blob/05a024a837076455c700e5d0f88637aa22432b45/docs/CONFIGURATION.md) records the versions, the decisions, and what "line N" means.

## Layout

| Folder | Content |
| --- | --- |
| [`Allman2023/`](Allman2023) | The Lean code; [its README](Allman2023/README.md) lists the modules by section of the paper, and what the paper says in passing |
| [`Allman2023/Basic/`](Allman2023/Basic) | General mathematics, in Mathlib's namespaces; [its README](Allman2023/Basic/README.md) says where each part could go |
| [`Allman2023/External/`](Allman2023/External) | The cited results, one directory per source, in the namespaces `External.<Source>`; [its README](Allman2023/External/README.md) lists them |
| [`Allman2023/Defs.lean`](Allman2023/Defs.lean), [`Allman2023/Bridge/`](Allman2023/Bridge) | The definitions of the Challenge, and the proof that they are the library's |
| [`Allman2023/Networks/`](Allman2023/Networks), [`Allman2023/FourTaxa/`](Allman2023/FourTaxa), [`Allman2023/LargeNetworks/`](Allman2023/LargeNetworks), [`Allman2023/MainResult/`](Allman2023/MainResult), [`Allman2023/Figures/`](Allman2023/Figures) | The paper's library, by its Sections 2, 3, 4 and 5, and its figures, in the namespace [`Allman2023`](Allman2023) |
| [`palomar/Allman2023/`](palomar/Allman2023) | The Challenge, the Solution, the Comparator configuration and the metadata |
| [`docs/Allman2023/`](docs/Allman2023) | [The report](docs/Allman2023/REPORT.md), [the credits](docs/Allman2023/CREDITS.md) and the routes of the proofs |
| [`scripts/`](scripts) | The audit, the route check, the copy of the definitions into the Challenge, the kernels, the links and the tables |

## Related work

From [Section 10 of the report](docs/Allman2023/REPORT.md#10-the-paper-in-the-literature).

- No other formalization of this paper was found. [lean4-allman2011](https://github.com/vltanh/lean4-allman2011), by the same owner, formalizes Allman, Degnan, Rhodes 2011, which the paper cites, and isn't used here.
- Before: the paper's own account cites level-1 work (SNaQ, Baños 2019, NANUQ) and takes the tree of blobs from Gusfield et al. 2007, which is formalized separately, in [lean4-gusfield2007](https://github.com/vltanh/lean4-gusfield2007).
- Since: TINNiK (2024) made the outline of Section 5 an algorithm with a consistency theorem, and TOB-QMC and ECToBlob build on the paper's results; all three are papers of the hub lean4-phylo-tree-of-blobs. "Beyond level-1" (2025) extends tree of blobs identifiability to common inheritance and the displayed tree model. Huber et al. 2025 and Frohn et al. 2025 give the tree of blobs from exact quarnets. Allman et al. 2024 settle the identifiability of edge lengths at level 1.
- No erratum, correction or counterexample to the paper was found, and no later work that restates Lemma 2.

## What's next

The natural next steps are to extend the generic results beyond independent inheritance, `ρ = 0`, where "Beyond level-1" has reached `ρ = 1` for binary networks, and to ask which lengths of cut edges are identifiable above level 1, which line 252 leaves to future work. [Section 11 of the report](docs/Allman2023/REPORT.md#11-whats-next) has these and the simpler arguments that the formalization found. A private `NEXT.md` holds the candidate follow-up papers.

## Credits

- Requested and supervised by The-Anh Vu-Le, who chose the papers, decided the library's boundary and the project's layout, and published the repository. **No person has reviewed the proofs.** Independent agents reviewed the statements and compared the proofs with the paper.
- Codex made the source audit and first foundations of the collection, on 2026-10-27. Claude (Opus 5.5) in Claude Code, with sub-agents, wrote the statements, proofs, audit and documents, following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure.
- Made in lean4-phylo-tree-of-blobs from 2026-10-31 to 2026-11-01, with the rest of the collection. [`docs/Allman2023/CREDITS.md`](docs/Allman2023/CREDITS.md) and lean4-phylo-tree-of-blobs's [`docs/CREDITS.md`](https://github.com/vltanh/lean4-phylo-tree-of-blobs/blob/05a024a837076455c700e5d0f88637aa22432b45/docs/CREDITS.md) have the details.

## License

[Apache-2.0](LICENSE).
