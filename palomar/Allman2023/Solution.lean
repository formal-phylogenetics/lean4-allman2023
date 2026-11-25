module

public import Allman2023.Bridge.Statements
public import Allman2023.Figures.Figure2
public import Allman2023.FourTaxa.CFDetectable
public import Allman2023.FourTaxa.NetworkOne
public import Allman2023.LargeNetworks.Lemma2Counterexample
public import Allman2023.MainResult.Algorithm
public import Allman2023.MainResult.BlobDistance
public import Allman2023.MainResult.Theorem4
public import Allman2023.Networks.CycleFamily

/-! # Allman, Baños, Mitchell, Rhodes 2023: the proofs of the statements of record

Restates each theorem of `Allman2023.Challenge` word for word, in the namespace
`Allman2023Challenge`, and proves it from the library, through the bridges of `Allman2023.Bridge`
between the Challenge's definitions and the library's. It is the entry point of the library. -/

public section

namespace Allman2023Challenge

open Finset Allman2023.Model

universe u

/-- **Theorem 1** (`CF`-detectability of 4-blobs on 4-taxon networks). On a binary rooted phylogenetic
network on four taxa, for generic parameters: the reduced unrooted tree of blobs has the quartet tree
topology `ab|cd` if and only if `CF_abcd` is strictly `(ab|cd)`-cut, and it has the unresolved
topology if and only if `CF_abcd` is non-cut. -/
theorem theorem1 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    (N : Network V E X) (hN : N.IsBinaryNetwork) (hcard : Fintype.card X = 4) :
    N.ForGenericParams fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      (Displays N.treeOfBlobs (quartetTree a b c d h) ↔
        IsStrictlyCutAtFirst (N.cfTriple θ a b c d h)) ∧
      ((∀ s : QuartetTree X, s.taxa = {a, b, c, d} → ¬ Displays N.treeOfBlobs s) ↔
        IsNonCutCF (N.cfTriple θ a b c d h)) := by
  exact Allman2023.Model.theorem1 N hN hcard

/-- **Corollary 1**. On a binary rooted phylogenetic network, for generic parameters, the topology of
the reduced unrooted tree of blobs of the network induced on each set of four taxa is identifiable
from its concordance factor: it is what `readTopology` reads from `CF_abcd`. -/
theorem corollary1 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    (N : Network V E X) (hN : N.IsBinaryNetwork) :
    N.ForGenericParams fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      N.InducedTopologyIs a b c d h (readTopology (N.cfTriple θ a b c d h)) := by
  exact Allman2023.Model.corollary1 N hN

/-- **Proposition 1**. On a binary rooted phylogenetic network on four taxa whose reduced tree of
blobs has the quartet topology `ab|cd`, for all parameters, `CF_abcd = (p, q, q)` with `0 < p, q < 1`
and `p + 2q = 1`. -/
theorem proposition1 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    (N : Network V E X) (hN : N.IsBinaryNetwork) (hcard : Fintype.card X = 4) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (hT : Displays N.treeOfBlobs (quartetTree a b c d h))
    {θ : Params E} (hθ : N.IsMetric θ) :
    ∃ p q : ℝ, N.cfTriple θ a b c d h = (p, q, q) ∧ 0 < p ∧ p < 1 ∧ 0 < q ∧ q < 1 ∧ p + 2 * q = 1 := by
  exact Allman2023.Model.proposition1 N hN hcard h hT hθ

/-- **Proposition 1, the converse**. Every triple `(p, q, q)` with `0 < p, q < 1` and `p + 2q = 1` is
`CF_abcd` on a binary rooted phylogenetic network on four taxa, with some parameters, whose reduced
tree of blobs has the quartet topology `ab|cd`. -/
theorem proposition1_converse {X : Type u} [Fintype X] [DecidableEq X] (hcard : Fintype.card X = 4)
    {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) (hpq : p + 2 * q = 1) :
    ∃ (V : Type u) (E : Type) (_ : Fintype V) (_ : Fintype E) (N : Network V E X) (θ : Params E),
      N.IsBinaryNetwork ∧ N.IsMetric θ ∧ Displays N.treeOfBlobs (quartetTree a b c d h) ∧
        N.cfTriple θ a b c d h = (p, q, q) := by
  exact Allman2023.Model.proposition1_converse hcard h hp hp1 hq hq1 hpq

/-- **Theorem 2** (the B-quartet Inference Rule). On a binary rooted phylogenetic network, if
`{a, b, c, d}` and `{b, c, d, e}` are B-quartets, and one of `{a, b, c, e}`, `{a, b, d, e}`,
`{a, c, d, e}` is, on its induced 4-taxon network, (a) a T-quartet with `a` and `e` separated in the
reduced unrooted tree of blobs, or (b) a B-quartet, then all three are B-quartets. -/
theorem theorem2 {V E X : Type*} [DecidableEq X] (N : Network V E X) (hN : N.IsBinaryNetwork)
    {a b c d e : X} (h5 : ({a, b, c, d, e} : Finset X).card = 5) (habcd : N.IsBlobQuartet {a, b, c, d})
    (hbcde : N.IsBlobQuartet {b, c, d, e}) {t : Finset X}
    (ht : t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)))
    (hrule : (∃ s : QuartetTree X, s.taxa = t ∧ N.InducedCutSplit s ∧ Separated s a e) ∨
      ∀ s : QuartetTree X, s.taxa = t → ¬ N.InducedCutSplit s) :
    N.IsBlobQuartet {a, b, c, e} ∧ N.IsBlobQuartet {a, b, d, e} ∧ N.IsBlobQuartet {a, c, d, e} := by
  exact Allman2023.Model.theorem2 N hN h5 habcd hbcde ht hrule

/-- **Theorem 3**. On a binary rooted phylogenetic network, for generic parameters, the sets of four
taxa that `CF`-detectability and applications of the B-quartet Inference Rule give from the
concordance factors are exactly the B-quartets. -/
theorem theorem3 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    (N : Network V E X) (hN : N.IsBinaryNetwork) :
    N.ForGenericParams fun θ => ∀ Q : Finset X, Q.card = 4 →
      (CFInferred (N.cf θ) Q ↔ N.IsBlobQuartet Q) := by
  exact Allman2023.Model.theorem3 N hN

/-- **Theorem 4**. The reduced unrooted tree of blobs is identifiable from the distribution of gene
quartet topologies under the network multispecies coalescent, for generic parameters: one function
`F`, chosen before the network, recovers it from the concordance factors of all quartet trees, for
generic parameters on every binary rooted phylogenetic network on the taxa. -/
theorem theorem4 (X : Type*) [Fintype X] [DecidableEq X] (hX : Nontrivial X) :
    ∃ F : (QuartetTree X → ℝ) → Finset (Finset X),
      ∀ (V E : Type u) [Fintype V] [Fintype E] (N : Network V E X), N.IsBinaryNetwork →
        N.ForGenericParams fun θ => F (N.cf θ) = N.treeOfBlobs := by
  exact Allman2023.Model.theorem4 X hX

end Allman2023Challenge

end
