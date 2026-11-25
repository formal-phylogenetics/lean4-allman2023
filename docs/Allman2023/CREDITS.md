# Credits

Allman, Baños, Mitchell, Rhodes 2023, in Lean.

- **Maintainer:** The-Anh Vu-Le, who chose the paper, agreed to the corrections of its statements that
  [the report](REPORT.md) records, and decided the layout. **No person has reviewed the proofs.**
- **Formalization:** Claude (Opus 5.5) in Claude Code, with sub-agents, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure; the first foundations and
  the source audit by Codex. The work was done in [lean4-phylo-tree-of-blobs](https://github.com/vltanh/lean4-phylo-tree-of-blobs), with the other
  papers on the tree of blobs, from 2026-10-27 to 2026-11-04. The rounds, the agents and models, and the time and
  effort of each are in lean4-phylo-tree-of-blobs's
  [`docs/CREDITS.md`](https://github.com/vltanh/lean4-phylo-tree-of-blobs/blob/6e7bc494d26f3d7096a17adffbfde1cf559f0ae9/docs/CREDITS.md),
  at the last commit before the split.
- **Moved to this repository** on 2026-11-21, by Claude (Opus 5.5) in Claude Code, when lean4-phylo-tree-of-blobs became the hub
  of its papers. No statement and no proof changed: only module paths did. Every declaration keeps its name and its
  type, checked against lean4-phylo-tree-of-blobs at commit `6e7bc49`, and the audit and the route check pass here.
- **Moved to the collection's layout** on 2026-11-24, by Claude (Opus 5.5) in Claude Code, at the
  maintainer's decision that every repository of the collection takes it: the root [`Allman2023`](../../Allman2023), the
  paper's library by its sections, general lemmas in [`Allman2023/Basic/`](../../Allman2023/Basic) under Mathlib's names, the
  cited results in [`Allman2023/External/`](../../Allman2023/External), a Challenge that imports only Mathlib, with the paper's
  definitions in [`Allman2023/Defs.lean`](../../Allman2023/Defs.lean), its Solution and the bridges from those definitions to the
  library's, and the documents in `docs/Allman2023/`. The thin copies of the semidirected network of
  lean4-phylogenetics gave way to the library's, and the declarations took the namespace
  [`Allman2023`](../../Allman2023); `scripts/stmt_diff.py` against the commit before the move lists only these renames
  and replacements. The audit, the route check and Comparator pass.
