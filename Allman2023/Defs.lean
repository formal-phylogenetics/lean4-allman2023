module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Combinatorics.Graph.Connected.EdgeCut
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Instances.Matrix

/-! # The definitions of the Challenge

The definitions that the Challenge states its theorems with, between the markers of
`scripts/sync_challenge_defs.py`, which copies them word for word into the Challenge,
`palomar/Allman2023/Challenge.lean` (formalize-math-paper, `references/palomar.md`, Section 2).

This module imports exactly what the Challenge imports: Lean, Mathlib, and nothing from this
repository, from `Phylogenetics` or from any other repository of the collection. The definitions
are those of the paper, written in Mathlib's vocabulary, and they follow the definitions of
`Phylogenetics` that the library uses, so that `Allman2023.Bridge` proves that the two agree. -/

-- BEGIN SHARED DEFINITIONS

/-! ## Networks

A rooted network is a directed multigraph with named edges (two edges may join the same two nodes), a
root and a labelling of the taxa by nodes. Its numerical parameters are a length for every edge, in
coalescent units, and an inheritance probability for every edge. -/

@[expose] public noncomputable section

open Finset MeasureTheory
open scoped Classical

namespace Allman2023.Model

/-- A directed multigraph: each edge `e` goes from `source e` to `target e`. -/
structure Digraph (V E : Type*) where
  source : E → V
  target : E → V

namespace Digraph

variable {V E : Type*} (G : Digraph V E)

/-- An edge leads from `u` to `v`. -/
def Adj (u v : V) : Prop := ∃ e, G.source e = u ∧ G.target e = v

/-- A directed path, possibly empty, leads from `u` to `v`. -/
def Reaches : V → V → Prop := Relation.ReflTransGen G.Adj

/-- No nonempty directed path from a node to itself. -/
def IsAcyclic : Prop := ∀ v, ¬ Relation.TransGen G.Adj v v

/-- The number of edges entering `v`. -/
def indegree (v : V) : ℕ := {e | G.target e = v}.ncard

/-- The number of edges leaving `v`. -/
def outdegree (v : V) : ℕ := {e | G.source e = v}.ncard

/-- The edge `e` crosses the bipartition `S | Sᶜ` of the nodes, in either direction. -/
def Crosses (e : E) (S : Set V) : Prop :=
  (G.source e ∈ S ∧ G.target e ∉ S) ∨ (G.target e ∈ S ∧ G.source e ∉ S)

/-- An edge of `F` joins `u` and `v`, in either direction. -/
def AdjOn (F : Set E) (u v : V) : Prop :=
  ∃ e ∈ F, (G.source e = u ∧ G.target e = v) ∨ (G.source e = v ∧ G.target e = u)

/-- An undirected walk, possibly empty, along edges of `F` joins `u` and `v`. -/
def Walks (F : Set E) : V → V → Prop := Relation.ReflTransGen (G.AdjOn F)

/-- The undirected graph is connected. -/
def IsConnected : Prop := ∀ u v, G.Walks Set.univ u v

/-- The undirected multigraph, Mathlib's `Graph`, with the same nodes and the same named edges. -/
def underlying : Graph V E where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e u v := (G.source e = u ∧ G.target e = v) ∨ (G.source e = v ∧ G.target e = u)
  isLink_symm := by
    intro e _
    constructor
    intro u v h
    exact h.symm
  eq_or_eq_of_isLink_of_isLink := by
    intro e u v x y h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · exact Or.inl (h.1.symm.trans h'.1)
    · exact Or.inr (h.1.symm.trans h'.1)
    · exact Or.inr (h.2.symm.trans h'.2)
    · exact Or.inl (h.2.symm.trans h'.2)
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun _ => ⟨G.source e, G.target e, Or.inl ⟨rfl, rfl⟩⟩, fun _ => Set.mem_univ e⟩
  left_mem_of_isLink := by intro e u v _; exact Set.mem_univ u

/-- **Definition 2**: a *cut edge*, an edge whose deletion disconnects the undirected graph: a
bridge of Mathlib's `Graph`, the only edge of an edge cut. Parallel edges are not cut edges. -/
def IsCutEdge (e : E) : Prop := G.underlying.IsBridge e

/-- Two nodes are in the same *blob* (Definition 7): an undirected walk that uses no cut edge joins
them. The blobs are the connected components that remain when the cut edges are deleted. -/
def blobSetoid : Setoid V where
  r := G.Walks {e | ¬ G.IsCutEdge e}
  iseqv := ⟨fun _ => .refl, fun h => by
    induction h with
    | refl => exact .refl
    | tail _ hab ih =>
      obtain ⟨e, he, h⟩ := hab
      exact Relation.ReflTransGen.head ⟨e, he, h.symm⟩ ih, fun h h' => h.trans h'⟩

/-- The blobs of the graph. -/
abbrev BlobVertex := Quotient G.blobSetoid

/-- The blob of a node. -/
def blobOf (v : V) : G.BlobVertex := Quotient.mk G.blobSetoid v

/-- An edge is *incident* to a blob when exactly one of its ends is in the blob (Definition 7). -/
def IsIncidentToBlob (e : E) (b : G.BlobVertex) : Prop :=
  Xor (G.blobOf (G.source e) = b) (G.blobOf (G.target e) = b)

/-- The cut edges incident to a blob. -/
def incidentCutEdges (b : G.BlobVertex) : Set E := {e | G.IsCutEdge e ∧ G.IsIncidentToBlob e b}

/-- **Definition 8**: the blob `b` is *determined by* the set `S` of labels (`|S| ≥ 3`): deleting the
cut edges incident to `b` leaves the elements of `S` in `|S|` distinct connected components. -/
def IsDeterminedBy {ι : Type*} (ℓ : ι → V) (b : G.BlobVertex) (S : Finset ι) : Prop :=
  3 ≤ S.card ∧ ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ G.Walks (G.incidentCutEdges b)ᶜ (ℓ s) (ℓ t)

end Digraph

/-- A rooted network on the taxa `X`: a directed multigraph, its root, and the node of each taxon. -/
structure Network (V E X : Type*) where
  graph : Digraph V E
  root : V
  leaf : X → V

/-- The numerical parameters of a network: edge lengths, in coalescent units, and inheritance
probabilities. -/
structure Params (E : Type*) where
  length : E → ℝ
  inheritance : E → ℝ

namespace Network

variable {V E X : Type*} (N : Network V E X)

/-- A *tree node* (Definition 1): in-degree 1 and out-degree 2. -/
def IsTreeNode (v : V) : Prop := N.graph.indegree v = 1 ∧ N.graph.outdegree v = 2

/-- A *hybrid node* (Definition 1): in-degree 2 and out-degree 1. -/
def IsHybridNode (v : V) : Prop := N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1

/-- A *hybrid edge* (Definition 1): its child is a hybrid node. -/
def IsHybridEdge (e : E) : Prop := N.IsHybridNode (N.graph.target e)

/-- A *tree edge* (Definition 1): its child is a tree node or a leaf. -/
def IsTreeEdge (e : E) : Prop := N.IsTreeNode (N.graph.target e) ∨ ∃ x, N.leaf x = N.graph.target e

/-- **Definition 1**: a *topological rooted binary phylogenetic network* on the taxa `X`: a finite
connected directed acyclic graph whose nodes are the root (in-degree 0, out-degree 2), the leaves
(in-degree 1, out-degree 0), labelled bijectively by the taxa, the tree nodes and the hybrid nodes.
Parallel edges are allowed. -/
structure IsBinaryNetwork : Prop where
  finite_vertices : Finite V
  finite_arcs : Finite E
  connected : N.graph.IsConnected
  acyclic : N.graph.IsAcyclic
  root_in : N.graph.indegree N.root = 0
  root_out : N.graph.outdegree N.root = 2
  leaf_in : ∀ x, N.graph.indegree (N.leaf x) = 1
  leaf_out : ∀ x, N.graph.outdegree (N.leaf x) = 0
  leaf_injective : Function.Injective N.leaf
  node_cases : ∀ v, v = N.root ∨ (∃ x, N.leaf x = v) ∨ N.IsTreeNode v ∨ N.IsHybridNode v

/-- **Definition 3**: the numerical parameters of a *metric rooted binary phylogenetic network*: a
tree edge has positive length, a hybrid edge non-negative length, and the hybridization parameters
of the two hybrid edges with the same child are positive and sum to `1`. A tree edge has inheritance
probability `1`: every lineage on it follows it. -/
def IsMetric (θ : Params E) : Prop :=
  (∀ e, N.IsTreeEdge e → 0 < θ.length e) ∧ (∀ e, N.IsHybridEdge e → 0 ≤ θ.length e) ∧
    (∀ e e', e ≠ e' → N.IsHybridEdge e → N.graph.target e = N.graph.target e' →
      0 < θ.inheritance e ∧ 0 < θ.inheritance e' ∧ θ.inheritance e + θ.inheritance e' = 1) ∧
    ∀ e, N.IsTreeEdge e → θ.inheritance e = 1

/-- `A` is the set of taxa on one side of a cut edge: some edge is the only edge crossing a
bipartition `S | Sᶜ` of the nodes, and the taxa in `S` are `A`. -/
def HasCutSplit (A : Set X) : Prop :=
  ∃ (e : E) (S : Set V), (∀ f, N.graph.Crosses f S ↔ f = e) ∧ N.leaf ⁻¹' S = A

/-- The nodes above a taxon of `Y`. -/
def ancestralVertices (Y : Set X) : Set V := {v | ∃ x ∈ Y, N.graph.Reaches v (N.leaf x)}

/-- The edges above a taxon of `Y`. They and the nodes above form the subnetwork that induces the
network on `Y` (Definition 6), before its nodes of degree 2 are suppressed. -/
def ancestralArcs (Y : Set X) : Set E := {e | N.graph.target e ∈ N.ancestralVertices Y}

/-- `A ∩ Y | Y \ A` is the split of a cut edge of the network induced on `Y` (Definition 6): some
edge of the subnetwork above `Y` is the only one of its edges crossing a bipartition of the nodes
whose side `S` holds exactly the taxa of `A` among those of `Y`. Suppressing the nodes of degree 2
and what is above the LSA of `Y` doesn't change such splits. -/
def HasCutSplitOn (Y A : Set X) : Prop :=
  ∃ e ∈ N.ancestralArcs Y, ∃ S : Set V,
    (∀ f ∈ N.ancestralArcs Y, N.graph.Crosses f S ↔ f = e) ∧ ∀ x ∈ Y, N.leaf x ∈ S ↔ x ∈ A

/-- **Definition 12**: the set `Q` of four taxa is a *B-quartet*: some blob is determined by `Q`. -/
def IsBlobQuartet (Q : Finset X) : Prop :=
  Q.card = 4 ∧ ∃ b, N.graph.IsDeterminedBy N.leaf b Q

end Network

/-! ## Quartet trees and trees of blobs

An unrooted tree on the taxa is given by the family of the sides of its splits, and a resolved
quartet tree `ab|cd` by the pair of its cherries. -/

/-- The unrooted tree of a rooted tree `G`, given by its clusters: the sides of the splits of its
non-root clusters. -/
def unroot {L : Type*} [Fintype L] [DecidableEq L] (G : Finset (Finset L)) : Finset (Finset L) :=
  G.erase univ ∪ (G.erase univ).image compl

/-- A resolved quartet tree `ab|cd`: the pair of its two disjoint cherries `{a, b}`, `{c, d}`. -/
def IsQuartetTree {X : Type*} [DecidableEq X] (s : Finset (Finset X)) : Prop :=
  s.card = 2 ∧ (∀ B ∈ s, B.card = 2) ∧ ∀ B ∈ s, ∀ C ∈ s, B ≠ C → Disjoint B C

/-- The resolved quartet trees on `X`. -/
abbrev QuartetTree (X : Type*) [DecidableEq X] := {s : Finset (Finset X) // IsQuartetTree s}

/-- The four taxa of a quartet tree. -/
def QuartetTree.taxa {X : Type*} [DecidableEq X] (s : QuartetTree X) : Finset X := s.val.sup id

/-- Four elements of a set of four are distinct. -/
theorem ne_of_card_eq_four {X : Type*} [DecidableEq X] {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have ha : a ∉ ({b, c, d} : Finset X) := fun hm => by
    rw [insert_eq_of_mem hm] at h
    have h3 : ({b, c, d} : Finset X).card ≤ 3 := card_le_three
    rw [h] at h3
    exact absurd h3 (by decide)
  have hb : b ∉ ({c, d} : Finset X) := fun hm => by
    have h1 := card_insert_le a ({b, c, d} : Finset X)
    rw [insert_eq_of_mem hm] at h h1
    rw [h] at h1
    exact absurd (Nat.le_trans h1 (Nat.add_le_add_right card_le_two 1)) (by decide)
  have hc : c ≠ d := fun he => by
    rw [he, insert_eq_of_mem (mem_singleton_self d)] at h
    have h3 : ({a, b, d} : Finset X).card ≤ 3 := card_le_three
    rw [h] at h3
    exact absurd h3 (by decide)
  rw [mem_insert, mem_insert, mem_singleton, not_or, not_or] at ha
  rw [mem_insert, mem_singleton, not_or] at hb
  exact ⟨ha.1, ha.2.1, ha.2.2, hb.1, hb.2, hc⟩

/-- The set `{a, c, b, d}` is `{a, b, c, d}`. -/
theorem card_acbd {X : Type*} [DecidableEq X] {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) : ({a, c, b, d} : Finset X).card = 4 :=
  (congrArg (fun s => (insert a s).card) (insert_comm c b {d})).trans h

/-- The set `{a, d, b, c}` is `{a, b, c, d}`. -/
theorem card_adbc {X : Type*} [DecidableEq X] {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) : ({a, d, b, c} : Finset X).card = 4 :=
  (congrArg (fun s => (insert a s).card)
    ((insert_comm d b {c}).trans (congrArg (insert b) (pair_comm d c)))).trans h

/-- The quartet tree `ab|cd`, for four distinct taxa. -/
def quartetTree {X : Type*} [DecidableEq X] (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) :
    QuartetTree X :=
  ⟨{{a, b}, {c, d}}, by
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_eq_four h
    have hne' : ({a, b} : Finset X) ≠ {c, d} := fun he => by
      have : a ∈ ({c, d} : Finset X) := he ▸ mem_insert_self a {b}
      rw [mem_insert, mem_singleton] at this
      exact this.elim hac had
    refine ⟨card_pair hne', ?_, ?_⟩
    · intro B hB
      rw [mem_insert, mem_singleton] at hB
      rcases hB with rfl | rfl
      · exact card_pair hab
      · exact card_pair hcd
    · intro B hB C hC hBC
      rw [mem_insert, mem_singleton] at hB hC
      rcases hB with rfl | rfl <;> rcases hC with rfl | rfl
      · exact absurd rfl hBC
      · refine disjoint_left.2 fun x hx hx' => ?_
        rw [mem_insert, mem_singleton] at hx hx'
        rcases hx with rfl | rfl <;> rcases hx' with h' | h'
        · exact hac h'
        · exact had h'
        · exact hbc h'
        · exact hbd h'
      · refine disjoint_left.2 fun x hx hx' => ?_
        rw [mem_insert, mem_singleton] at hx hx'
        rcases hx with rfl | rfl <;> rcases hx' with h' | h'
        · exact hac h'.symm
        · exact hbc h'.symm
        · exact had h'.symm
        · exact hbd h'.symm
      · exact absurd rfl hBC⟩

/-- The tree `T`, given by the sides of its splits, *displays* the quartet tree `s`: some split
restricts to `s` on its four taxa. -/
def Displays {X : Type*} [DecidableEq X] (T : Finset (Finset X)) (s : QuartetTree X) : Prop :=
  ∃ A ∈ T, A ∩ s.taxa ∈ s.val

/-- The three quartet trees on the four taxa `q`. -/
def treesOn {X : Type*} [Fintype X] [DecidableEq X] (q : Finset X) : Finset (QuartetTree X) :=
  univ.filter fun r => r.taxa = q

/-- The two quartet trees on the taxa of `s` other than `s`. -/
def QuartetTree.alternatives {X : Type*} [Fintype X] [DecidableEq X] (s : QuartetTree X) :
    Finset (QuartetTree X) :=
  univ.filter fun r => r.taxa = s.taxa ∧ r ≠ s

/-- The taxa `a`, `e` are *separated* in the quartet tree `s`: they are in different cherries. -/
def Separated {X : Type*} [DecidableEq X] (s : QuartetTree X) (a e : X) : Prop :=
  a ∈ s.taxa ∧ e ∈ s.taxa ∧ ∀ B ∈ s.val, ¬ (a ∈ B ∧ e ∈ B)

namespace Network

variable {V E X : Type*} (N : Network V E X)

/-- **Definitions 10 and 11**: the *reduced unrooted tree of blobs* `T_rd(𝒩⁻)`, given by the sides
of its splits: the nonempty proper sets of taxa on one side of a cut edge. Contracting the blobs to
nodes leaves a tree whose edges are the cut edges; those above the LSA of the taxa, where `𝒩⁻` is
cut off, and the nodes of degree 2, which are suppressed, change no such side. -/
def treeOfBlobs [Fintype X] [DecidableEq X] : Finset (Finset X) :=
  univ.filter fun A => A.Nonempty ∧ Aᶜ.Nonempty ∧ N.HasCutSplit (A : Set X)

/-- The quartet tree `s` is displayed by the reduced unrooted tree of blobs of the network induced
on its four taxa (Definition 6): a cut edge of the induced network splits its cherries. -/
def InducedCutSplit [DecidableEq X] (s : QuartetTree X) : Prop :=
  ∃ B ∈ s.val, N.HasCutSplitOn (s.taxa : Set X) (B : Set X)

end Network

/-! ## The network multispecies coalescent

A forest of gene lineages on the leaves `L` is the set of its clusters, and its roots are its maximal
clusters. Along an edge of length `t` the lineages coalesce by Kingman's coalescent, each pair of
roots merging at rate `1`; above the root, for an infinite time. At a hybrid node each lineage
independently takes each of the two hybrid edges with its inheritance probability. -/

section Coalescent

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The roots of a forest: its maximal clusters. -/
def roots (F : Finset (Finset L)) : Finset (Finset L) := F.filter fun A => ∀ B ∈ F, A ⊆ B → B = A

/-- The generator of Kingman's coalescent on forests: each pair of distinct roots `A, B` merges at
rate `1`, adding the cluster `A ∪ B`. -/
def kingmanGenerator : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if G = F then -((#(roots F)).choose 2 : ℝ)
    else if ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F then 1 else 0

/-- Kingman's coalescent over a time `t`: `exp (t • Q)`. -/
def kingmanTransition (t : ℝ) : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  NormedSpace.exp (t • kingmanGenerator)

/-- Kingman's coalescent over an infinite time: the limits as `t → ∞`. -/
def kingmanAbsorption : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G => Filter.limUnder Filter.atTop fun t : ℝ => kingmanTransition t F G

/-- The part of the forest `F` below its roots in `A`. -/
def forestBelow (F A : Finset (Finset L)) : Finset (Finset L) := F.filter fun B => ∃ C ∈ A, B ⊆ C

end Coalescent

namespace Network

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable (N : Network V E X) (θ : Params E)

/-- The forest arriving at `v` from below: its taxon's lineage, if any, and the forests at the top of
the edges leaving `v`. -/
def arrivingForest (top : E → Finset (Finset X)) (v : V) : Finset (Finset X) :=
  ((univ.filter fun x => N.leaf x = v).image fun x => ({x} : Finset X)) ∪
    (univ.filter fun e => N.graph.source e = v).biUnion top

/-- The probability that the roots of the forest `F` arriving at `v` choose the edges entering `v`
that put the forests `bot e` at their bottoms: each root independently takes the edge `e` with the
inheritance probability of `e`. -/
def allocationFactor (F : Finset (Finset X)) (v : V) (bot : E → Finset (Finset X)) : ℝ :=
  ∑ a : {A // A ∈ roots F} → {e // N.graph.target e = v},
    if ∀ e : {e // N.graph.target e = v},
        bot e.val = forestBelow F ((univ.filter fun r => a r = e).image Subtype.val) then
      ∏ r, θ.inheritance (a r).val
    else 0

/-- The probability of a history: the forests `bot e` at the bottom and `top e` at the top of each
edge. -/
def historyWeight (bot top : E → Finset (Finset X)) : ℝ :=
  (∏ v ∈ univ.erase N.root, N.allocationFactor θ (N.arrivingForest top v) v bot) *
    ∏ e, kingmanTransition (θ.length e) (bot e) (top e)

/-- **The network multispecies coalescent**: the probability of the rooted gene tree `G` (its
clusters), one lineage per taxon. -/
def geneTreeDist (G : Finset (Finset X)) : ℝ :=
  ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    N.historyWeight θ bot top * kingmanAbsorption (N.arrivingForest top N.root) G

/-- **Definition 14**: the *quartet concordance factor* `CF_s` of the quartet tree `s`: the
probability that a gene tree displays `s`. -/
def cf (s : QuartetTree X) : ℝ :=
  ∑ G : Finset (Finset X), if Displays (unroot G) s then N.geneTreeDist θ G else 0

/-- **Definition 14**: the concordance factor of the taxa `a, b, c, d`, the ordered triple
`CF_abcd = (CF_{ab|cd}, CF_{ac|bd}, CF_{ad|bc})`. -/
def cfTriple (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) : ℝ × ℝ × ℝ :=
  (N.cf θ (quartetTree a b c d h),
    N.cf θ (quartetTree a c b d (card_acbd h)),
    N.cf θ (quartetTree a d b c (card_adbc h)))

end Network

/-! ## Generic parameters -/

namespace Network

variable {V E X : Type*} [Fintype E] (N : Network V E X)

/-- A set of parameters is *null*: Lebesgue-null in the coordinates given by all edge lengths and, at
each hybrid node, the inheritance probability of all but one of its hybrid edges, for every choice
of the edge left out. The coordinates of the other edges are dummies. -/
def IsGenericNull (A : Set (Params E)) : Prop :=
  ∀ d : V → E, (∀ v, N.IsHybridNode v → N.graph.target (d v) = v) →
    ((Measure.pi fun _ : E => (volume : Measure ℝ)).prod (Measure.pi fun _ : E => (volume : Measure ℝ)))
      {x | ∃ θ ∈ A, N.IsMetric θ ∧ θ.length = x.1 ∧
        ∀ e, N.IsHybridEdge e → e ≠ d (N.graph.target e) → θ.inheritance e = x.2 e} = 0

/-- `P` holds *for generic parameters*: the parameters of the metric network violating it form a null
set. -/
def ForGenericParams (P : Params E → Prop) : Prop := N.IsGenericNull {θ | N.IsMetric θ ∧ ¬ P θ}

end Network

/-! ## Cut concordance factors -/

/-- **Definition 15**: the concordance factor `t` is *cut*: two of its entries are equal. -/
def IsCutCF (t : ℝ × ℝ × ℝ) : Prop := t.1 = t.2.1 ∨ t.1 = t.2.2 ∨ t.2.1 = t.2.2

/-- **Definition 15**: `t = CF_abcd` is *strictly `(ab|cd)`-cut*: its last two entries are equal and
differ from the first. -/
def IsStrictlyCutAtFirst (t : ℝ × ℝ × ℝ) : Prop := t.1 ≠ t.2.1 ∧ t.2.1 = t.2.2

/-- **Definition 15**: the concordance factor `t` is *non-cut*. -/
def IsNonCutCF (t : ℝ × ℝ × ℝ) : Prop := ¬ IsCutCF t

/-- **Definition 15**, on the concordance factors `p` of all quartet trees: they are *strictly
`s`-cut*: equal on the two other quartet trees on the taxa of `s`, and different on `s`. -/
def IsStrictlyCutAt {X : Type*} [Fintype X] [DecidableEq X] (p : QuartetTree X → ℝ)
    (s : QuartetTree X) : Prop :=
  (∀ r ∈ s.alternatives, p r ≠ p s) ∧ ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p r = p r'

/-- The topologies of a tree on the taxa `a, b, c, d`: `ab|cd`, `ac|bd`, `ad|bc`, and the unresolved
one. -/
inductive QuartetTopology
  | first | second | third | star

/-- What `CF`-detectability reads from `t = CF_abcd`: strictly `(ab|cd)`-cut gives `ab|cd`, and so on;
otherwise the unresolved topology. -/
def readTopology (t : ℝ × ℝ × ℝ) : QuartetTopology :=
  if t.1 ≠ t.2.1 ∧ t.2.1 = t.2.2 then .first
  else if t.2.1 ≠ t.1 ∧ t.1 = t.2.2 then .second
  else if t.2.2 ≠ t.1 ∧ t.1 = t.2.1 then .third
  else .star

namespace Network

variable {V E X : Type*} [DecidableEq X] (N : Network V E X)

/-- The reduced unrooted tree of blobs of the network induced on `{a, b, c, d}` has the topology
`τ`: `ab|cd`, `ac|bd` or `ad|bc` when it displays that quartet tree, the unresolved topology when it
displays none. -/
def InducedTopologyIs (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) :
    QuartetTopology → Prop
  | .first => N.InducedCutSplit (quartetTree a b c d h)
  | .second => N.InducedCutSplit (quartetTree a c b d (card_acbd h))
  | .third => N.InducedCutSplit (quartetTree a d b c (card_adbc h))
  | .star => ∀ s : QuartetTree X, s.taxa = {a, b, c, d} → ¬ N.InducedCutSplit s

end Network

section Inferred

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `CF`-detectability reads the set `q` of four taxa as unresolved from the concordance factors
`p`. -/
def ReadsUnresolved (p : QuartetTree X → ℝ) (q : Finset X) : Prop :=
  ∃ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), ({a, b, c, d} : Finset X) = q ∧
    readTopology (p (quartetTree a b c d h), p (quartetTree a c b d (card_acbd h)),
      p (quartetTree a d b c (card_adbc h))) = .star

/-- The sets of four taxa that `CF`-detectability (Theorem 1) and applications of the B-quartet
Inference Rule (Theorem 2) give from the concordance factors `p`: those read as unresolved, and, for
`{a, b, c, d}` and `{b, c, d, e}` so given, the three sets `{a, b, c, e}`, `{a, b, d, e}`,
`{a, c, d, e}` when one of them is (a) strictly cut at a quartet tree separating `a` and `e`, or
(b) read as unresolved. It depends on `p` alone. -/
inductive CFInferred (p : QuartetTree X → ℝ) : Finset X → Prop
  | detected (Q : Finset X) : ReadsUnresolved p Q → CFInferred p Q
  | rule (a b c d e : X) (t q : Finset X) :
      ({a, b, c, d, e} : Finset X).card = 5 →
      CFInferred p {a, b, c, d} → CFInferred p {b, c, d, e} →
      t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      ((∃ s ∈ treesOn t, IsStrictlyCutAt p s ∧ Separated s a e) ∨ ReadsUnresolved p t) →
      q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      CFInferred p q

end Inferred

end Allman2023.Model

end

-- END SHARED DEFINITIONS
