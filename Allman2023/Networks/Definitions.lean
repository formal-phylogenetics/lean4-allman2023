module

public import Phylogenetics.NMSC.InducedParams
public import Phylogenetics.Network.TreeOfBlobs

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Definitions 1 to 5

*The tree of blobs of a species network: identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.

Networks as the paper defines them, tied to the representation of the library:

* `IsBinaryNetwork` is Definition 1, in the paper's words; `isBinaryNetwork_iff`: it is
  `RootedNetwork.IsPhylogenetic` with `RootedNetwork.IsBinary`.
* Definition 2 is `G.underlying.IsBridge e`, of the library.
* `IsMetricParams` is Definition 3; `isMetric_iff`: `RootedNetwork.IsMetric` is that, with the convention that
  a tree edge has inheritance `1`, a coordinate that Definition 3 does not have.
* `IsLSA` is Definition 4 (Steel 2016), for any nonempty set of nodes; `existsUnique_isLSA`, `isLSA_image_leaf_iff`.
* `lsaNode`, `lsaPlus` and `semidirected` are, for a network of Definition 1, the LSA of the taxa, the LSA network
  `𝒩⊕` of Definition 5 (`mem_belowVertices_univ_iff`, `mem_belowArcs_univ_iff`: what is kept is what is not above
  the LSA) and the semidirected unrooted network `𝒩⁻` of Definition 5: the library's `RootedNetwork.lsa`,
  `RootedNetwork.lsaPlus` and `RootedNetwork.semidirected`, of `Phylogenetics.Network.Semidirected`, whose
  `RootedNetwork.semidirectedMetric` gives the lengths of `𝒩⁻`.

Suppressing the root of `𝒩⊕` needs an edge out of the root that is not hybrid, because the paper's list of
suppressions has no case of two directed out-edges. `RootedNetwork.exists_isTreeArc_root` proves that it does not arise.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace Allman2023

variable {V E X : Type*}

/-! ### Definition 1 -/

section Definition1

variable (N : RootedNetwork V E X)

/-- A *tree node* of Definition 1: in-degree 1 and out-degree 2. -/
def IsTreeNode (v : V) : Prop := N.graph.indegree v = 1 ∧ N.graph.outdegree v = 2

/-- A *hybrid node* of Definition 1: in-degree 2 and out-degree 1. -/
def IsHybridNode (v : V) : Prop := N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1

/-- A *hybrid edge* of Definition 1: its child node is hybrid. -/
def IsHybridEdge (e : E) : Prop := IsHybridNode N (N.graph.target e)

/-- A *tree edge* of Definition 1: its child node is a tree node or a leaf. -/
def IsTreeEdge (e : E) : Prop :=
  IsTreeNode N (N.graph.target e) ∨ ∃ x, N.leaf x = N.graph.target e

/-- **Definition 1** (`a:def::network`). A *topological rooted binary phylogenetic network* on the taxa `X`: a
connected directed acyclic graph whose nodes are the root, the leaves, the tree nodes and the hybrid nodes, with
a bijective leaf labelling. The leaf labelling `f : V_L → X` of the paper is the inverse of `N.leaf : X → V`, and
`V_L` is the range of `N.leaf`. The four kinds of node are disjoint by their degrees, and `E = E_H ⊔ E_T` follows
from the kinds of node (`isTreeArc_iff`, `isHybridArc_iff`). The paper takes graphs to be finite without saying so,
and allows parallel edges, its 2-cycles. -/
structure IsBinaryNetwork : Prop where
  finite_vertices : Finite V
  finite_arcs : Finite E
  connected : N.graph.IsConnected
  acyclic : N.graph.IsAcyclic
  /-- The root has in-degree 0. -/
  root_in : N.graph.indegree N.root = 0
  /-- The root has out-degree 2. -/
  root_out : N.graph.outdegree N.root = 2
  /-- A leaf has in-degree 1. -/
  leaf_in : ∀ x, N.graph.indegree (N.leaf x) = 1
  /-- A leaf has out-degree 0. -/
  leaf_out : ∀ x, N.graph.outdegree (N.leaf x) = 0
  leaf_injective : Function.Injective N.leaf
  /-- `V = {r} ⊔ V_L ⊔ V_H ⊔ V_T`. -/
  node_cases : ∀ v, v = N.root ∨ (∃ x, N.leaf x = v) ∨ IsTreeNode N v ∨ IsHybridNode N v

variable {N}

namespace IsBinaryNetwork

variable (hN : IsBinaryNetwork N)
include hN

theorem finite_taxa : Finite X :=
  have := hN.finite_vertices
  Finite.of_injective _ hN.leaf_injective

theorem one_le_indegree {v : V} (hv : v ≠ N.root) : 1 ≤ N.graph.indegree v := by
  rcases hN.node_cases v with rfl | ⟨x, rfl⟩ | h | h
  · exact absurd rfl hv
  · rw [hN.leaf_in]
  · rw [h.1]
  · rw [h.1]
    omega

/-- "Thus the root is above all other nodes." -/
theorem root_reaches (v : V) : N.graph.Reaches N.root v := by
  have := hN.finite_vertices
  have := hN.finite_arcs
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj a b
  have : IsTrans V r := ⟨fun _ _ _ h h' => h.trans h'⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  induction v using hwf.induction with
  | _ v ih =>
    by_cases hv : v = N.root
    · subst hv
      exact .refl
    · obtain ⟨e, he⟩ := (N.graph.one_le_indegree_iff v).mp (hN.one_le_indegree hv)
      have hadj : N.graph.Adj (N.graph.source e) v := ⟨e, rfl, he⟩
      exact (ih _ (.single hadj)).tail hadj

theorem isPhylogenetic : N.IsPhylogenetic := by
  refine ⟨hN.finite_vertices, hN.finite_arcs, hN.finite_taxa, hN.acyclic, hN.root_reaches, hN.root_in,
    fun v hv => hN.one_le_indegree hv, hN.leaf_injective, hN.leaf_in, fun v => ⟨fun h => ?_, ?_⟩⟩
  · rcases hN.node_cases v with rfl | hx | h' | h'
    · rw [hN.root_out] at h
      exact absurd h (by norm_num)
    · exact hx
    · rw [h'.2] at h
      exact absurd h (by norm_num)
    · rw [h'.2] at h
      exact absurd h (by norm_num)
  · rintro ⟨x, rfl⟩
    exact hN.leaf_out x

theorem isBinary : N.IsBinary := by
  refine ⟨hN.root_out, fun v hv h0 => ?_⟩
  rcases hN.node_cases v with rfl | ⟨x, rfl⟩ | h | h
  · exact absurd rfl hv
  · exact absurd (hN.leaf_out x) h0
  · rw [h.1, h.2]
  · rw [h.1, h.2]

end IsBinaryNetwork

/-- **Definition 1 is the library's two predicates.** -/
theorem isBinaryNetwork_iff : IsBinaryNetwork N ↔ N.IsPhylogenetic ∧ N.IsBinary := by
  refine ⟨fun h => ⟨h.isPhylogenetic, h.isBinary⟩, fun ⟨hP, hB⟩ => ?_⟩
  have := hP.finite_arcs
  refine ⟨hP.finite_vertices, hP.finite_arcs, N.graph_connected hP, hP.acyclic, hP.root_indegree, hB.1,
    hP.leaf_indegree, fun x => (hP.leaves _).mpr ⟨x, rfl⟩, hP.leaf_injective, fun v => ?_⟩
  by_cases hr : v = N.root
  · exact Or.inl hr
  refine Or.inr ?_
  by_cases h0 : N.graph.outdegree v = 0
  · exact Or.inl ((hP.leaves v).mp h0)
  have h3 := hB.2 v hr h0
  have h1 := hP.nonroot_indegree v hr
  refine Or.inr ?_
  by_cases h' : N.graph.indegree v = 1
  · exact Or.inl ⟨h', by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- A *hybrid edge* of Definition 1 is a hybrid arc of the library. -/
theorem isHybridArc_iff (hN : IsBinaryNetwork N) (e : E) : N.IsHybridArc e ↔ IsHybridEdge N e := by
  have := hN.finite_arcs
  have hr : N.graph.target e ≠ N.root := fun h =>
    (N.graph.indegree_eq_zero_iff _).mp hN.root_in e h
  unfold IsHybridArc IsHybridEdge
  rcases hN.node_cases (N.graph.target e) with h | ⟨x, hx⟩ | h | h
  · exact absurd h hr
  · rw [← hx, hN.leaf_in, IsHybridNode, hN.leaf_in]
    simp
  · simp [IsHybridNode, h.1, h.2]
  · simp [IsHybridNode, h.1, h.2]

/-- A *tree edge* of Definition 1 is a tree arc of the library. -/
theorem isTreeArc_iff (hN : IsBinaryNetwork N) (e : E) : N.IsTreeArc e ↔ IsTreeEdge N e := by
  have := hN.finite_arcs
  have hr : N.graph.target e ≠ N.root := fun h =>
    (N.graph.indegree_eq_zero_iff _).mp hN.root_in e h
  unfold IsTreeArc IsTreeEdge
  rcases hN.node_cases (N.graph.target e) with h | hx | h | h
  · exact absurd h hr
  · obtain ⟨x, hx'⟩ := id hx
    simp only [← hx', hN.leaf_in, true_iff]
    exact Or.inr ⟨x, rfl⟩
  · simp [h.1, Or.inl h]
  · have hn : ¬ IsTreeNode N (N.graph.target e) := fun h' => by
      have := h.1.symm.trans h'.1
      omega
    have hl : ¬ ∃ x, N.leaf x = N.graph.target e := by
      rintro ⟨x, hx⟩
      have := h.2
      rw [← hx, hN.leaf_out] at this
      omega
    simp [h.1, hn, hl]

end Definition1

/-! ### Definition 2 -/

/-- **Definition 2** (`a:def:cutedge`). A *cut edge*: an edge whose deletion increases the number of connected components. This is
`G.underlying.IsBridge e`, Mathlib's bridge of the undirected graph, which keeps parallel edges apart;
`DirectedMultigraph.isBridge_iff_not_walks_delete` says that it is an edge whose deletion separates its ends. -/
abbrev IsCutEdge {W F : Type*} (G : DirectedMultigraph W F) (e : F) : Prop := G.underlying.IsBridge e


/-! ### Definition 3 -/

section Definition3

variable (N : RootedNetwork V E X)

/-- **Definition 3** (`a:def:metric`). The numerical parameters of a *metric rooted binary phylogenetic network*:
a tree edge has positive length, a hybrid edge has non-negative length, and the hybridization parameters of two
hybrid edges with the same child are positive and sum to 1. -/
structure IsMetricParams (θ : MetricData E) : Prop where
  tree_length_pos : ∀ e, IsTreeEdge N e → 0 < θ.length e
  hybrid_length_nonneg : ∀ e, IsHybridEdge N e → 0 ≤ θ.length e
  hybrid_param : ∀ e e', e ≠ e' → IsHybridEdge N e → N.graph.target e = N.graph.target e' →
    0 < θ.inheritance e ∧ 0 < θ.inheritance e' ∧ θ.inheritance e + θ.inheritance e' = 1

variable {N}

/-- The two edges into a hybrid node. -/
theorem IsHybridNode.exists_parents {v : V} (hv : IsHybridNode N v) :
    ∃ e e', e ≠ e' ∧ ∀ f, N.graph.target f = v ↔ f = e ∨ f = e' := by
  obtain ⟨e, e', hne, h⟩ := Set.ncard_eq_two.mp hv.1
  refine ⟨e, e', hne, fun f => ?_⟩
  have := Set.ext_iff.mp h f
  simpa using this

/-- **`RootedNetwork.IsMetric` is Definition 3, with the convention that a tree edge has inheritance `1`.**
`MetricData` has an inheritance coordinate on every arc, and Definition 3 has one on hybrid edges only. -/
theorem isMetric_iff [Fintype E] (hN : IsBinaryNetwork N) (θ : MetricData E) :
    N.IsMetric θ ↔ IsMetricParams N θ ∧ ∀ e, IsTreeEdge N e → θ.inheritance e = 1 := by
  have hsum : ∀ {v : V} {e e' : E}, e ≠ e' → (∀ f, N.graph.target f = v ↔ f = e ∨ f = e') →
      (∑ f, if N.graph.target f = v then θ.inheritance f else 0) =
        θ.inheritance e + θ.inheritance e' := by
    intro v e e' hne h
    rw [← Finset.sum_filter, show (Finset.univ.filter fun f => N.graph.target f = v) = {e, e'} by
      ext f
      simp [h f], Finset.sum_pair hne]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨⟨fun e he => h₁ e ((isTreeArc_iff hN e).mpr he),
      fun e he => h₂ e ((isHybridArc_iff hN e).mpr he), fun e e' hne he ht => ?_⟩,
      fun e he => h₃ e ((isTreeArc_iff hN e).mpr he)⟩
    have he' : IsHybridEdge N e' := by
      unfold IsHybridEdge at he ⊢
      rwa [← ht]
    refine ⟨h₄ e ((isHybridArc_iff hN e).mpr he), h₄ e' ((isHybridArc_iff hN e').mpr he'), ?_⟩
    obtain ⟨f, f', hff, hpar⟩ := IsHybridNode.exists_parents he
    have hef : (f = e ∧ f' = e') ∨ (f = e' ∧ f' = e) := by
      have h1 := (hpar e).mp rfl
      have h2 := (hpar e').mp ht.symm
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp_all
    have hall : ∀ g, N.graph.target g = N.graph.target e ↔ g = e ∨ g = e' := by
      intro g
      rw [hpar g]
      rcases hef with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact or_comm
    have hhyb : 2 ≤ N.graph.indegree (N.graph.target e) := by
      rw [he.1]
    rw [← hsum hne hall]
    exact h₅ _ hhyb
  · rintro ⟨⟨h₁, h₂, h₃⟩, h₄⟩
    refine ⟨fun e he => h₁ e ((isTreeArc_iff hN e).mp he),
      fun e he => h₂ e ((isHybridArc_iff hN e).mp he), fun e he => h₄ e ((isTreeArc_iff hN e).mp he),
      fun e he => ?_, fun v hv => ?_⟩
    · have he' := (isHybridArc_iff hN e).mp he
      obtain ⟨f, f', hff, hpar⟩ := IsHybridNode.exists_parents he'
      have hf : IsHybridEdge N f := by
        unfold IsHybridEdge
        rw [(hpar f).mpr (Or.inl rfl)]
        exact he'
      obtain ⟨p₁, p₂, -⟩ := h₃ f f' hff hf ((hpar f).mpr (Or.inl rfl) |>.trans ((hpar f').mpr (Or.inr rfl)).symm)
      rcases (hpar e).mp rfl with rfl | rfl
      · exact p₁
      · exact p₂
    · have hh : IsHybridNode N v := by
        rcases hN.node_cases v with rfl | ⟨x, rfl⟩ | h | h
        · rw [hN.root_in] at hv
          omega
        · rw [hN.leaf_in] at hv
          omega
        · rw [h.1] at hv
          omega
        · exact h
      obtain ⟨f, f', hff, hpar⟩ := hh.exists_parents
      have hf : IsHybridEdge N f := by
        unfold IsHybridEdge
        rw [(hpar f).mpr (Or.inl rfl)]
        exact hh
      rw [hsum hff hpar]
      exact (h₃ f f' hff hf ((hpar f).mpr (Or.inl rfl) |>.trans ((hpar f').mpr (Or.inr rfl)).symm)).2.2

end Definition3

/-! ### Definition 4 -/

section Definition4

variable (N : RootedNetwork V E X)

/-- The set `D` of Definition 4: the nodes on every directed path from the root to any `z ∈ Z`. -/
def stableNodes (Z : Set V) : Set V := {u | ∀ z ∈ Z, ¬ N.HasPathAvoiding N.root z u}

/-- **Definition 4** (`a:def::LSA`; Steel 2016). `v` is the *lowest stable ancestor* of the nonempty set of nodes
`Z`: the node of `D` below every other node of `D`. It exists and is unique: `existsUnique_isLSA`. -/
def IsLSA (Z : Set V) (v : V) : Prop :=
  v ∈ stableNodes N Z ∧ ∀ u ∈ stableNodes N Z, u ≠ v → N.graph.Reaches u v

variable {N}

/-- "The unique node": the LSA of a nonempty set of nodes exists and is unique. -/
theorem existsUnique_isLSA (hN : N.IsPhylogenetic) {Z : Set V} (hZ : Z.Nonempty) :
    ∃! v, IsLSA N Z v := by
  have : Finite V := hN.finite_vertices
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj b a
  have : IsTrans V r := ⟨fun _ _ _ h h' => h'.trans h⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  have hne : (stableNodes N Z).Nonempty := ⟨N.root, fun _ _ h => h.1 rfl⟩
  obtain ⟨v, hv, hmin⟩ := hwf.has_min _ hne
  obtain ⟨z, hz⟩ := hZ
  have hcomp : ∀ w ∈ stableNodes N Z, N.graph.Reaches w v := fun w hw => by
    rcases reaches_or_reaches_of_not_hasPathAvoiding (hN.root_reaches z) (hw z hz) (hv z hz) with h | h
    · exact h
    · rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | ht
      · exact .refl
      · exact absurd ht (hmin w hw)
  refine ⟨v, ⟨hv, fun w hw _ => hcomp w hw⟩, fun w hw => ?_⟩
  by_contra hne
  exact hne (eq_of_reaches_of_reaches hN.acyclic (hcomp w hw.1) (hw.2 v hv (Ne.symm hne)))

/-- **Definition 4 on a set of taxa is the library's least stable ancestor.** -/
theorem isLSA_image_leaf_iff {Y : Set X} {v : V} :
    IsLSA N (N.leaf '' Y) v ↔ N.IsLeastStableAncestor Y v := by
  have hst : ∀ u, u ∈ stableNodes N (N.leaf '' Y) ↔ N.IsStableAncestor Y u := fun u => by
    simp [stableNodes, IsStableAncestor]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨(hst v).mp h₁, fun w hw => ?_⟩
    by_cases hwv : w = v
    · rw [hwv]
      exact .refl
    · exact h₂ w ((hst w).mpr hw) hwv
  · rintro ⟨h₁, h₂⟩
    exact ⟨(hst v).mpr h₁, fun w hw _ => h₂ w ((hst w).mp hw)⟩

end Definition4

/-! ### Definition 5 -/

section LSANetwork

variable {N : RootedNetwork V E X}

/-- `LSA(𝒩⁺)`: the LSA of the leaves (Definition 4), the library's `RootedNetwork.lsa` of all the taxa. -/
abbrev lsaNode (hN : IsBinaryNetwork N) (hX : Nontrivial X) : V :=
  lsa hN.isPhylogenetic Set.univ Set.univ_nonempty

/-- `lsaNode` is the LSA of Definition 4 of the leaves. -/
theorem isLSA_lsaNode (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    IsLSA N (Set.range N.leaf) (lsaNode hN hX) := by
  rw [← Set.image_univ, isLSA_image_leaf_iff]
  exact lsa_spec hN.isPhylogenetic Set.univ Set.univ_nonempty

/-- **Definition 5, part 1** (`a:def::undirected`). The *LSA network* `𝒩⊕`: "deleting all edges and nodes above
`LSA(𝒩⁺)`, and designating `LSA(𝒩⁺)` as the root node". It is the library's `RootedNetwork.lsaPlus`, the library's
`lsaNetwork` on all the taxa, on the taxa `X` itself. `mem_belowVertices_univ_iff` and `mem_belowArcs_univ_iff` say
that it keeps what is not above the LSA. -/
abbrev lsaPlus (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    RootedNetwork (N.belowVertices (lsaNode hN hX) Set.univ) (N.belowArcs (lsaNode hN hX) Set.univ) X :=
  RootedNetwork.lsaPlus hN.isPhylogenetic hX

/-- A node is kept in `𝒩⊕` exactly when it is not strictly above the LSA. -/
theorem mem_belowVertices_univ_iff (hN : IsBinaryNetwork N) (hX : Nontrivial X) (v : V) :
    v ∈ N.belowVertices (lsaNode hN hX) Set.univ ↔
      ¬ (N.graph.Reaches v (lsaNode hN hX) ∧ v ≠ lsaNode hN hX) := by
  have hP := hN.isPhylogenetic
  have hst := (lsa_spec hP Set.univ Set.univ_nonempty).1
  constructor
  · rintro ⟨hv, -⟩ ⟨h, hne⟩
    exact hne (eq_of_reaches_of_reaches hP.acyclic h hv)
  · intro h
    refine ⟨?_, mem_ancestralVertices_univ hN.isPhylogenetic v⟩
    obtain ⟨x, hx⟩ := exists_reaches_leaf hP v
    by_cases hv : N.HasPathAvoiding N.root v (lsaNode hN hX)
    · -- a path to `v` avoids the LSA, so the path on to `x` must meet it after `v`
      by_contra hnr
      have hab : ¬ N.HasPathAvoiding v (N.leaf x) (lsaNode hN hX) := fun hp =>
        hst x (Set.mem_univ x) ⟨hv.1, hp.2.1, hv.2.2.trans hp.2.2⟩
      obtain ⟨h₁, -⟩ := reaches_of_not_hasPathAvoiding hx hab
      exact h ⟨h₁, fun hEq => hnr (hEq ▸ .refl)⟩
    · exact (reaches_of_not_hasPathAvoiding (hP.root_reaches v) hv).2

/-- An edge is kept in `𝒩⊕` exactly when it is not above the LSA. -/
theorem mem_belowArcs_univ_iff (hN : IsBinaryNetwork N) (hX : Nontrivial X) (e : E) :
    e ∈ N.belowArcs (lsaNode hN hX) Set.univ ↔ ¬ N.graph.Reaches (N.graph.target e) (lsaNode hN hX) := by
  have hP := hN.isPhylogenetic
  have hst := (lsa_spec hP Set.univ Set.univ_nonempty).1
  constructor
  · rintro ⟨hs, -⟩ h
    exact not_reaches_target_source hP.acyclic e (h.trans hs)
  · intro h
    refine ⟨?_, mem_ancestralVertices_univ hN.isPhylogenetic _⟩
    by_contra hnr
    have hv : N.HasPathAvoiding N.root (N.graph.source e) (lsaNode hN hX) := by
      by_contra hv
      exact hnr (reaches_of_not_hasPathAvoiding (hP.root_reaches _) hv).2
    obtain ⟨x, hx⟩ := exists_reaches_leaf hP (N.graph.target e)
    have hab : N.HasPathAvoiding (N.graph.target e) (N.leaf x) (lsaNode hN hX) := by
      by_contra hab
      exact h (reaches_of_not_hasPathAvoiding hx hab).1
    refine hst x (Set.mem_univ x) ⟨hv.1, hab.2.1, hv.2.2.trans (Relation.ReflTransGen.head
      ⟨⟨e, rfl, rfl⟩, hv.2.1, hab.1⟩ hab.2.2)⟩

end LSANetwork

/-! ### Definition 5: the semidirected unrooted network -/

section Semidirected

variable {N : RootedNetwork V E X}

/-- **Definition 5, part 2** (`a:def::undirected`). The *semidirected unrooted network* `𝒩⁻`: "the unrooted
network obtained from the LSA network `𝒩⊕` by undirecting all tree edges and suppressing the root, but retaining
directions of hybrid edges". It is the library's `RootedNetwork.semidirected`, which suppresses the root with
`RootedNetwork.unrootAt`, merging the tree edge `RootedNetwork.rootTreeArc` into the other edge of the root. If that
edge is hybrid, the merged edge is the paper's "single edge with the out-edge direction". The library's
`RootedNetwork.semidirectedMetric` gives its lengths and hybridization parameters: "for a metric graph the new edge is
assigned a length equal to the sum of lengths of the two replaced. If the out-edge was hybrid, the new edge is also
hybrid and retains the hybridization parameter". -/
abbrev semidirected (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    SemidirectedNetwork (SemidirectedVertex hN.isPhylogenetic hX)
      (SemidirectedArc hN.isPhylogenetic hN.isBinary hX) X :=
  RootedNetwork.semidirected hN.isPhylogenetic hN.isBinary hX

end Semidirected

end Allman2023

/-! ### Former names

The names under which the repositories that require this one, lean4-tinnik, lean4-tob-qmc,
lean4-nanuq and lean4-ectoblob, use these declarations: deprecated aliases of the theorems, and the
definitions exported under their former namespace, so that dot notation on their values finds the
lemmas of the new namespace. -/

@[deprecated (since := "2026-11-24")]
alias AllmanEtAl2023.IsBinaryNetwork.isBinary := Allman2023.IsBinaryNetwork.isBinary

@[deprecated (since := "2026-11-24")]
alias AllmanEtAl2023.IsBinaryNetwork.isPhylogenetic := Allman2023.IsBinaryNetwork.isPhylogenetic

@[deprecated (since := "2026-11-24")]
alias AllmanEtAl2023.mem_belowArcs_univ_iff := Allman2023.mem_belowArcs_univ_iff

namespace AllmanEtAl2023

export Allman2023 (IsBinaryNetwork lsaNode lsaPlus semidirected)

end AllmanEtAl2023


namespace AllmanEtAl2023

open Phylogenetics Phylogenetics.RootedNetwork

variable {V E X : Type*} {N : RootedNetwork V E X}

export Phylogenetics (SemidirectedNetwork)

/-- The nodes of `𝒩⁻`. -/
@[deprecated RootedNetwork.SemidirectedVertex +typeChanged (since := "2026-11-24")]
abbrev SemiV (hN : Allman2023.IsBinaryNetwork N) (hX : Nontrivial X) :=
  SemidirectedVertex hN.isPhylogenetic hX

/-- The edges of `𝒩⁻`. -/
@[deprecated RootedNetwork.SemidirectedArc +typeChanged (since := "2026-11-24")]
abbrev SemiE (hN : Allman2023.IsBinaryNetwork N) (hX : Nontrivial X) :=
  SemidirectedArc hN.isPhylogenetic hN.isBinary hX

/-- The edge out of the root of `𝒩⊕` that is merged into the other. -/
@[deprecated RootedNetwork.rootTreeArc +typeChanged (since := "2026-11-24")]
abbrev rootTreeArc (hN : Allman2023.IsBinaryNetwork N) (hX : Nontrivial X) :
    N.belowArcs (Allman2023.lsaNode hN hX) Set.univ :=
  RootedNetwork.rootTreeArc hN.isPhylogenetic hN.isBinary hX

set_option linter.deprecated false in
@[deprecated RootedNetwork.rootTreeArc_spec +typeChanged (since := "2026-11-24")]
theorem rootTreeArc_spec (hN : Allman2023.IsBinaryNetwork N) (hX : Nontrivial X) :
    (Allman2023.lsaPlus hN hX).graph.source (rootTreeArc hN hX) = (Allman2023.lsaPlus hN hX).root ∧
      (Allman2023.lsaPlus hN hX).IsTreeArc (rootTreeArc hN hX) :=
  RootedNetwork.rootTreeArc_spec hN.isPhylogenetic hN.isBinary hX

@[deprecated RootedNetwork.lsaPlus_isPhylogenetic +typeChanged (since := "2026-11-24")]
theorem lsaPlus_isPhylogenetic (hN : Allman2023.IsBinaryNetwork N) (hX : Nontrivial X) :
    (Allman2023.lsaPlus hN hX).IsPhylogenetic :=
  RootedNetwork.lsaPlus_isPhylogenetic hN.isPhylogenetic hX

@[deprecated RootedNetwork.mem_ancestralVertices_univ +typeChanged (since := "2026-11-24")]
theorem mem_ancestralVertices_univ (hN : Allman2023.IsBinaryNetwork N) (v : V) :
    v ∈ N.ancestralVertices Set.univ :=
  RootedNetwork.mem_ancestralVertices_univ hN.isPhylogenetic v

end AllmanEtAl2023
