module

public import Allman2023.Defs
public import Allman2023.Networks.Concordance
public import Allman2023.LargeNetworks.Rule
public import Phylogenetics.NMSC.Inheritance

/-!
# The Challenge's definitions are the library's

The Challenge states its theorems on the definitions of `Allman2023.Defs` (namespace
`Allman2023.Model`), written in Mathlib's vocabulary. The library states them on those of
`Phylogenetics` and of the paper's library. This module proves that the two agree: most are equal by
definition, once a network of the Challenge is read as one of the library (`Network.toRooted`).

* `Network.isBinaryNetwork_iff`: Definition 1.
* `Network.isMetric_iff`: Definition 3, on a network of Definition 1.
* `Network.cf_eq`, `Network.cfTriple_eq`: Definition 14, the network multispecies coalescent with
  independent inheritance (`nmscCF … 0`).
* `Network.forGenericParams_of`: a property that holds for generic parameters in the library's sense
  holds for generic parameters in the Challenge's.
* `Network.treeOfBlobs_eq`, `Network.inducedCutSplit_iff`, `Network.isBlobQuartet_iff`: the tree of
  blobs, its quartets on induced networks, and Definition 12.
* `cfInferred_iff`: what `CF`-detectability and the Inference Rule give from the concordance factors.
-/

@[expose] public noncomputable section

open Finset Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace Allman2023.Model

variable {V E X : Type*}

/-- A graph of the Challenge as a graph of the library. -/
def Digraph.toDM (G : Digraph V E) : DirectedMultigraph V E := ⟨G.source, G.target⟩

/-- A network of the Challenge as a network of the library. -/
def Network.toRooted (N : Network V E X) : RootedNetwork V E X := ⟨N.graph.toDM, N.root, N.leaf⟩

/-- A network of the library as a network of the Challenge. -/
def ofRooted (M : RootedNetwork V E X) : Network V E X :=
  ⟨⟨M.graph.source, M.graph.target⟩, M.root, M.leaf⟩

/-- Parameters of the Challenge as parameters of the library. -/
def Params.toMetric (θ : Params E) : MetricData E := ⟨θ.length, θ.inheritance⟩

/-- Parameters of the library as parameters of the Challenge. -/
def ofMetric (θ : MetricData E) : Params E := ⟨θ.length, θ.inheritance⟩

@[simp] theorem toRooted_ofRooted (M : RootedNetwork V E X) : (ofRooted M).toRooted = M := rfl

@[simp] theorem toMetric_ofMetric (θ : MetricData E) : (ofMetric θ).toMetric = θ := rfl

/-! ### Networks -/

namespace Network

variable (N : Network V E X)

/-- **Definition 1** is the library's. -/
theorem isBinaryNetwork_iff : N.IsBinaryNetwork ↔ Allman2023.IsBinaryNetwork N.toRooted := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem isHybridNode_iff (v : V) : N.IsHybridNode v ↔ Allman2023.IsHybridNode N.toRooted v := Iff.rfl

theorem isHybridEdge_iff (e : E) : N.IsHybridEdge e ↔ Allman2023.IsHybridEdge N.toRooted e := Iff.rfl

theorem isTreeEdge_iff (e : E) : N.IsTreeEdge e ↔ Allman2023.IsTreeEdge N.toRooted e := Iff.rfl

/-- **Definition 3**, with tree edges of inheritance `1`, is the library's parameters, on a network of
Definition 1. -/
theorem isMetric_iff [Fintype E] (hN : N.IsBinaryNetwork) (θ : Params E) :
    N.IsMetric θ ↔ N.toRooted.IsMetric θ.toMetric := by
  rw [Allman2023.isMetric_iff ((isBinaryNetwork_iff N).mp hN)]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h3⟩, h4⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩

theorem hasCutSplit_iff (A : Set X) : N.HasCutSplit A ↔ N.toRooted.HasCutSplit A := Iff.rfl

theorem hasCutSplitOn_iff (Y A : Set X) : N.HasCutSplitOn Y A ↔ N.toRooted.HasCutSplitOn Y A :=
  Iff.rfl

/-- **Definition 12** is the paper's library's. -/
theorem isBlobQuartet_iff (Q : Finset X) : N.IsBlobQuartet Q ↔ Allman2023.IsBlobQuartet N.toRooted Q :=
  Iff.rfl

end Network

/-! ### Quartet trees -/

section Quartets

variable [DecidableEq X]

/-- The quartet trees of the Challenge are the library's. -/
def quartetTreeEquiv : QuartetTree X ≃ Phylogenetics.QuartetTree X where
  toFun s := ⟨s.1, s.2⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem quartetTreeEquiv_val (s : QuartetTree X) : (quartetTreeEquiv s).1 = s.1 := rfl

@[simp] theorem quartetTreeEquiv_symm_val (s : Phylogenetics.QuartetTree X) :
    (quartetTreeEquiv.symm s).1 = s.1 := rfl

@[simp] theorem taxa_quartetTreeEquiv (s : QuartetTree X) :
    (quartetTreeEquiv s).taxa = s.taxa := rfl

@[simp] theorem taxa_quartetTreeEquiv_symm (s : Phylogenetics.QuartetTree X) :
    (quartetTreeEquiv.symm s).taxa = s.taxa := rfl

theorem quartetTreeEquiv_quartetTree (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) :
    quartetTreeEquiv (quartetTree a b c d h) = Phylogenetics.quartetTree a b c d h := rfl

theorem displays_iff (T : Finset (Finset X)) (s : QuartetTree X) :
    Displays T s ↔ Phylogenetics.Displays T (quartetTreeEquiv s) := Iff.rfl

theorem separated_iff (s : QuartetTree X) (a e : X) :
    Separated s a e ↔ Phylogenetics.Separated (quartetTreeEquiv s) a e := Iff.rfl

theorem inducedCutSplit_iff (N : Network V E X) (s : QuartetTree X) :
    N.InducedCutSplit s ↔ Phylogenetics.InducedCutSplit N.toRooted (quartetTreeEquiv s) := Iff.rfl

variable [Fintype X]

theorem mem_treesOn_iff {q : Finset X} {s : QuartetTree X} :
    s ∈ treesOn q ↔ quartetTreeEquiv s ∈ Phylogenetics.treesOn q := by
  simp [treesOn, Phylogenetics.mem_treesOn]

theorem mem_alternatives_iff {s r : QuartetTree X} :
    r ∈ s.alternatives ↔ quartetTreeEquiv r ∈ (quartetTreeEquiv s).alternatives := by
  rw [QuartetTree.alternatives, Phylogenetics.QuartetTree.alternatives, Finset.mem_filter,
    Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, taxa_quartetTreeEquiv, ne_eq, Equiv.apply_eq_iff_eq]

theorem isStrictlyCutAt_iff (p : Phylogenetics.QuartetTree X → ℝ) (s : QuartetTree X) :
    IsStrictlyCutAt (p ∘ quartetTreeEquiv) s ↔ Allman2023.IsStrictlyCutAt p (quartetTreeEquiv s) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
    · have := h1 (quartetTreeEquiv.symm r) (mem_alternatives_iff.mpr (by simpa using hr))
      simpa using this
    · have := h2 (quartetTreeEquiv.symm r) (mem_alternatives_iff.mpr (by simpa using hr))
        (quartetTreeEquiv.symm r') (mem_alternatives_iff.mpr (by simpa using hr'))
      simpa using this
  · rintro ⟨h1, h2⟩
    exact ⟨fun r hr => h1 _ (mem_alternatives_iff.mp hr),
      fun r hr r' hr' => h2 _ (mem_alternatives_iff.mp hr) _ (mem_alternatives_iff.mp hr')⟩

omit [Fintype X] in
theorem readTopology_eq_star_iff (t : ℝ × ℝ × ℝ) :
    readTopology t = .star ↔ Allman2023.readTopology t = .star := by
  unfold readTopology Allman2023.readTopology
  split_ifs <;> simp

omit [Fintype X] in
theorem readsUnresolved_iff (p : Phylogenetics.QuartetTree X → ℝ) (q : Finset X) :
    ReadsUnresolved (p ∘ quartetTreeEquiv) q ↔ Allman2023.ReadsUnresolved p q := by
  constructor
  · rintro ⟨a, b, c, d, h, hq, hr⟩
    exact ⟨a, b, c, d, h, hq, (readTopology_eq_star_iff _).mp hr⟩
  · rintro ⟨a, b, c, d, h, hq, hr⟩
    exact ⟨a, b, c, d, h, hq, (readTopology_eq_star_iff _).mpr hr⟩

/-- What `CF`-detectability and the Inference Rule give from the concordance factors is the paper's
library's `CFInferred`. -/
theorem cfInferred_iff (p : Phylogenetics.QuartetTree X → ℝ) (q : Finset X) :
    CFInferred (p ∘ quartetTreeEquiv) q ↔ Allman2023.CFInferred p q := by
  constructor
  · intro h
    induction h with
    | detected Q hQ => exact .detected Q ((readsUnresolved_iff p Q).mp hQ)
    | rule a b c d e t q h5 _ _ ht hr hq ih₁ ih₂ =>
      refine .rule a b c d e t q h5 ih₁ ih₂ ht ?_ hq
      rcases hr with ⟨s, hs, hcut, hsep⟩ | hr
      · exact Or.inl ⟨quartetTreeEquiv s, mem_treesOn_iff.mp hs, (isStrictlyCutAt_iff p s).mp hcut, hsep⟩
      · exact Or.inr ((readsUnresolved_iff p t).mp hr)
  · intro h
    induction h with
    | detected Q hQ => exact .detected Q ((readsUnresolved_iff p Q).mpr hQ)
    | rule a b c d e t q h5 _ _ ht hr hq ih₁ ih₂ =>
      refine .rule a b c d e t q h5 ih₁ ih₂ ht ?_ hq
      rcases hr with ⟨s, hs, hcut, hsep⟩ | hr
      · refine Or.inl ⟨quartetTreeEquiv.symm s, mem_treesOn_iff.mpr (by simpa using hs), ?_, hsep⟩
        exact (isStrictlyCutAt_iff p _).mpr (by simpa using hcut)
      · exact Or.inr ((readsUnresolved_iff p t).mpr hr)

end Quartets

/-! ### The coalescent -/

namespace Network

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : Network V E X) (θ : Params E)

omit [Fintype V] in
theorem arrivingForest_eq (top : E → Finset (Finset X)) (v : V) :
    N.arrivingForest top v = Phylogenetics.arrivingForest N.toRooted top v := rfl

omit [Fintype V] in
/-- The Challenge's allocation `∏ r, γ (a r)` is the library's `allocationWeight 0`. -/
theorem allocationFactor_eq (F : Finset (Finset X)) (v : V) (bot : E → Finset (Finset X)) :
    N.allocationFactor θ F v bot =
      Phylogenetics.allocationFactor N.toRooted θ.toMetric 0 F v bot := by
  unfold allocationFactor Phylogenetics.allocationFactor
  refine Finset.sum_congr rfl fun a _ => ?_
  exact ite_congr rfl (fun _ => (allocationWeight_rho_zero (γ := fun e :
    {e // N.toRooted.graph.target e = v} => θ.toMetric.inheritance e.val) a).symm) fun _ => rfl

theorem historyWeight_eq (bot top : E → Finset (Finset X)) :
    N.historyWeight θ bot top = Phylogenetics.historyWeight N.toRooted θ.toMetric 0 bot top := by
  unfold historyWeight Phylogenetics.historyWeight
  simp only [allocationFactor_eq, arrivingForest_eq]
  rfl

theorem geneTreeDist_eq (G : Finset (Finset X)) :
    N.geneTreeDist θ G = Phylogenetics.geneTreeDist N.toRooted θ.toMetric 0 G := by
  unfold geneTreeDist Phylogenetics.geneTreeDist
  simp only [historyWeight_eq, arrivingForest_eq]
  rfl

/-- **Definition 14**: the concordance factors of the Challenge are the library's, `nmscCF … 0`. -/
theorem cf_eq : N.cf θ = nmscCF N.toRooted θ.toMetric 0 ∘ quartetTreeEquiv := by
  funext s
  unfold cf
  simp only [Function.comp_apply, nmscCF, geneTreeDist_eq]
  rfl

/-- **Definition 14**, the ordered triple, is the paper's library's. -/
theorem cfTriple_eq (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) :
    N.cfTriple θ a b c d h = Allman2023.cfTriple N.toRooted θ.toMetric a b c d h := by
  simp only [cfTriple, Allman2023.cfTriple, cf_eq]
  rfl

omit [Fintype V] [Fintype E] in
/-- The reduced unrooted tree of blobs of the Challenge is the library's family of cut-edge splits. -/
theorem treeOfBlobs_eq : N.treeOfBlobs = Phylogenetics.treeOfBlobs N.toRooted := rfl

end Network

/-! ### Genericity -/

namespace Network

variable [Fintype E] (N : Network V E X)

/-- **Genericity transfers**: a property that holds for generic parameters in the library's sense
holds for generic parameters in the Challenge's. The Challenge's exceptional set, in the same
coordinates, is contained in the library's. -/
theorem forGenericParams_of (hN : N.IsBinaryNetwork) {P : Params E → Prop} {Q : MetricData E → Prop}
    (hPQ : ∀ θ, N.IsMetric θ → Q θ.toMetric → P θ)
    (h : Allman2023.ForGenericParams N.toRooted Q) : N.ForGenericParams P := by
  intro d hd
  have hb := (isBinaryNetwork_iff N).mp hN
  refine MeasureTheory.measure_mono_null ?_ (h d fun v hv => hd v ?_)
  · rintro x ⟨θ, ⟨hθ, hP⟩, -, hlen, hinh⟩
    exact ⟨θ.toMetric, ⟨(N.isMetric_iff hN θ).mp hθ, fun hQ => hP (hPQ θ hθ hQ)⟩,
      (N.isMetric_iff hN θ).mp hθ, hlen,
      fun e he hne => hinh e ((Allman2023.isHybridArc_iff hb e).mp he) hne⟩
  · rcases hb.node_cases v with rfl | ⟨y, rfl⟩ | h' | h'
    · rw [hb.root_in] at hv
      omega
    · rw [hb.leaf_in] at hv
      omega
    · change N.graph.indegree v = 1 ∧ _ at h'
      change 2 ≤ N.graph.indegree v at hv
      omega
    · exact h'

end Network

end Allman2023.Model
