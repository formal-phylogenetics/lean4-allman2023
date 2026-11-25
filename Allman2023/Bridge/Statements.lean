module

public import Allman2023.Bridge.Model
public import Allman2023.FourTaxa.Corollary1
public import Allman2023.FourTaxa.Proposition1
public import Allman2023.LargeNetworks.Theorem3
public import Allman2023.MainResult.Theorem4

/-!
# The main results on the Challenge's definitions

Theorems 1 to 4, Corollary 1 and Proposition 1, as the Challenge states them on the definitions of
`Allman2023.Defs`, proved from the paper's library through the bridges of `Allman2023.Bridge.Model`.
The library states the topology of the reduced unrooted tree of blobs `T_rd(𝒩⁻)`, and of those of
the induced networks, on the labelled graphs of Definition 11; the Challenge states them on the
quartet trees that these trees display, and `Allman2023.Bridges` proves that the two agree
(`Bridges.hasQuartetTopology_iff_displays`, `Bridges.hasStarTopology_iff_displaysUnresolved`,
`Bridges.splits_Trd`, `Bridges.inducedHasQuartetTopology_iff`, `Bridges.inducedHasStarTopology_iff`,
`Bridges.isBlobQuartetOnInduced_self_iff`).
-/

@[expose] public noncomputable section

open Finset Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace Allman2023.Model

universe u

variable {V E X : Type*}

section Displays

variable [Fintype X] [DecidableEq X]

theorem forall_not_displays_iff (T : Finset (Finset X)) (q : Finset X) :
    (∀ s : QuartetTree X, s.taxa = q → ¬ Displays T s) ↔
      ∀ s ∈ Phylogenetics.treesOn q, ¬ Phylogenetics.Displays T s := by
  constructor
  · intro h s hs
    exact h (quartetTreeEquiv.symm s) (by simpa using Phylogenetics.mem_treesOn.mp hs)
  · intro h s hs
    exact h (quartetTreeEquiv s) (Phylogenetics.mem_treesOn.mpr hs)

theorem forall_not_inducedCutSplit_iff (N : Network V E X) (q : Finset X) :
    (∀ s : QuartetTree X, s.taxa = q → ¬ N.InducedCutSplit s) ↔ ¬ IsTreelike N.toRooted q := by
  constructor
  · rintro h ⟨s, hs, hc⟩
    exact h (quartetTreeEquiv.symm s) (by simpa using Phylogenetics.mem_treesOn.mp hs) hc
  · intro h s hs hc
    exact h ⟨quartetTreeEquiv s, Phylogenetics.mem_treesOn.mpr hs, hc⟩

end Displays

/-- The topologies of the Challenge are the library's. -/
def topologyOfLib : Allman2023.QuartetTopology → QuartetTopology
  | .first => .first
  | .second => .second
  | .third => .third
  | .star => .star

theorem readTopology_eq (t : ℝ × ℝ × ℝ) : readTopology t = topologyOfLib (Allman2023.readTopology t) := by
  unfold readTopology Allman2023.readTopology
  split_ifs <;> rfl

/-- **Theorem 1** (`CF`-detectability of 4-blobs on 4-taxon networks), on the Challenge's definitions. -/
theorem theorem1 [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : Network V E X)
    (hN : N.IsBinaryNetwork) (hcard : Fintype.card X = 4) :
    N.ForGenericParams fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      (Displays N.treeOfBlobs (quartetTree a b c d h) ↔
        IsStrictlyCutAtFirst (N.cfTriple θ a b c d h)) ∧
      ((∀ s : QuartetTree X, s.taxa = {a, b, c, d} → ¬ Displays N.treeOfBlobs s) ↔
        IsNonCutCF (N.cfTriple θ a b c d h)) := by
  have hN' := (Network.isBinaryNetwork_iff N).mp hN
  have hX := Fintype.nontrivial_of_card_eq_four hcard
  refine N.forGenericParams_of hN (fun θ _ hQ a b c d h => ?_) (Allman2023.theorem1 hN' hcard)
  obtain ⟨h1, h2⟩ := hQ a b c d h
  rw [Network.cfTriple_eq]
  refine ⟨?_, ?_⟩
  · rw [displays_iff, Network.treeOfBlobs_eq, quartetTreeEquiv_quartetTree, ← Bridges.splits_Trd hN' hX,
      ← Bridges.hasQuartetTopology_iff_displays hN' hcard h]
    exact h1
  · rw [forall_not_displays_iff, Network.treeOfBlobs_eq, ← Bridges.splits_Trd hN' hX]
    refine Iff.trans ?_ h2
    rw [Bridges.hasStarTopology_iff_displaysUnresolved hN' hcard h, LabelledGraph.DisplaysUnresolved]
    exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩

/-- **Corollary 1**, on the Challenge's definitions. -/
theorem corollary1 [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : Network V E X)
    (hN : N.IsBinaryNetwork) :
    N.ForGenericParams fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      N.InducedTopologyIs a b c d h (readTopology (N.cfTriple θ a b c d h)) := by
  have hN' := (Network.isBinaryNetwork_iff N).mp hN
  refine N.forGenericParams_of hN (fun θ _ hQ a b c d h => ?_) (Allman2023.corollary1 hN')
  have hQ' := hQ a b c d h
  rw [Network.cfTriple_eq, readTopology_eq]
  generalize Allman2023.readTopology (Allman2023.cfTriple N.toRooted θ.toMetric a b c d h) = τ at hQ'
  cases τ with
  | first => exact (Bridges.inducedHasQuartetTopology_iff hN' h).mp hQ'
  | second => exact (Bridges.inducedHasQuartetTopology_iff hN' (card_acbd h)).mp hQ'
  | third => exact (Bridges.inducedHasQuartetTopology_iff hN' (card_adbc h)).mp hQ'
  | star =>
    exact (forall_not_inducedCutSplit_iff N _).mpr ((Bridges.inducedHasStarTopology_iff hN' h).mp hQ')

/-- **Proposition 1**, on the Challenge's definitions. -/
theorem proposition1 [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : Network V E X)
    (hN : N.IsBinaryNetwork) (hcard : Fintype.card X = 4) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (hT : Displays N.treeOfBlobs (quartetTree a b c d h))
    {θ : Params E} (hθ : N.IsMetric θ) :
    ∃ p q : ℝ, N.cfTriple θ a b c d h = (p, q, q) ∧ 0 < p ∧ p < 1 ∧ 0 < q ∧ q < 1 ∧ p + 2 * q = 1 := by
  have hN' := (Network.isBinaryNetwork_iff N).mp hN
  have hX := Fintype.nontrivial_of_card_eq_four hcard
  rw [Network.cfTriple_eq]
  refine Allman2023.proposition1 hN' hcard h ?_ ((N.isMetric_iff hN θ).mp hθ)
  rw [Bridges.hasQuartetTopology_iff_displays hN' hcard h, Bridges.splits_Trd hN' hX]
  exact hT

/-- **Proposition 1, the converse**, on the Challenge's definitions. -/
theorem proposition1_converse {X : Type u} [Fintype X] [DecidableEq X] (hcard : Fintype.card X = 4)
    {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) (hpq : p + 2 * q = 1) :
    ∃ (V : Type u) (E : Type) (_ : Fintype V) (_ : Fintype E) (N : Network V E X) (θ : Params E),
      N.IsBinaryNetwork ∧ N.IsMetric θ ∧ Displays N.treeOfBlobs (quartetTree a b c d h) ∧
        N.cfTriple θ a b c d h = (p, q, q) := by
  obtain ⟨V, E, _, _, M, hM, θ, hθ, hT, hcf⟩ := Allman2023.proposition1_converse hcard h hp hp1 hq hq1 hpq
  have hX := Fintype.nontrivial_of_card_eq_four hcard
  have hN : (ofRooted M).IsBinaryNetwork := (Network.isBinaryNetwork_iff _).mpr hM
  refine ⟨V, E, inferInstance, inferInstance, ofRooted M, ofMetric θ, hN,
    ((ofRooted M).isMetric_iff hN (ofMetric θ)).mpr hθ, ?_, ?_⟩
  · rw [displays_iff, Network.treeOfBlobs_eq, quartetTreeEquiv_quartetTree, toRooted_ofRooted,
      ← Bridges.splits_Trd hM hX, ← Bridges.hasQuartetTopology_iff_displays hM hcard h]
    exact hT
  · rw [Network.cfTriple_eq, toRooted_ofRooted, toMetric_ofMetric]
    exact hcf

/-- **Theorem 2** (the B-quartet Inference Rule), on the Challenge's definitions. -/
theorem theorem2 [DecidableEq X] (N : Network V E X) (hN : N.IsBinaryNetwork) {a b c d e : X}
    (h5 : ({a, b, c, d, e} : Finset X).card = 5) (habcd : N.IsBlobQuartet {a, b, c, d})
    (hbcde : N.IsBlobQuartet {b, c, d, e}) {t : Finset X}
    (ht : t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)))
    (hrule : (∃ s : QuartetTree X, s.taxa = t ∧ N.InducedCutSplit s ∧ Separated s a e) ∨
      ∀ s : QuartetTree X, s.taxa = t → ¬ N.InducedCutSplit s) :
    N.IsBlobQuartet {a, b, c, e} ∧ N.IsBlobQuartet {a, b, d, e} ∧ N.IsBlobQuartet {a, c, d, e} := by
  have hN' := (Network.isBinaryNetwork_iff N).mp hN
  have : Finite X := hN'.finite_taxa
  let _ : Fintype X := Fintype.ofFinite X
  refine Allman2023.theorem2 hN' h5 habcd hbcde ht ?_
  rcases hrule with ⟨s, hs, hc, hsep⟩ | hB
  · obtain ⟨u, v, w, z, h, hs'⟩ := TreeMetric.exists_eq_quartetTree (quartetTreeEquiv s)
    refine Or.inl ⟨u, v, w, z, h, ?_, ?_, ?_⟩
    · rw [← hs, ← taxa_quartetTreeEquiv, hs', quartetTree_taxa]
    · rw [Bridges.inducedHasQuartetTopology_iff hN' h, ← hs']
      exact hc
    · rw [← hs']
      exact hsep
  · have ht4 : t.card = 4 := by
      obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ := Finset.ne_of_card_eq_five h5
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact TreeMetric.card_four_of_ne hab hac hae hbc hbe hce
      · exact TreeMetric.card_four_of_ne hab had hae hbd hbe hde
      · exact TreeMetric.card_four_of_ne hac had hae hcd hce hde
    refine Or.inr ⟨ht4, (Bridges.isBlobQuartetOnInduced_self_iff hN' ht4).mpr ?_⟩
    exact (forall_not_inducedCutSplit_iff N t).mp hB

/-- **Theorem 3**, on the Challenge's definitions. -/
theorem theorem3 [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : Network V E X)
    (hN : N.IsBinaryNetwork) :
    N.ForGenericParams fun θ => ∀ Q : Finset X, Q.card = 4 →
      (CFInferred (N.cf θ) Q ↔ N.IsBlobQuartet Q) := by
  have hN' := (Network.isBinaryNetwork_iff N).mp hN
  refine N.forGenericParams_of hN (fun θ _ hQ Q hQ4 => ?_) (Allman2023.theorem3 hN')
  rw [Network.cf_eq, cfInferred_iff]
  exact hQ Q hQ4

/-- **Theorem 4**, on the Challenge's definitions. -/
theorem theorem4 (X : Type*) [Fintype X] [DecidableEq X] (hX : Nontrivial X) :
    ∃ F : (QuartetTree X → ℝ) → Finset (Finset X),
      ∀ (V E : Type u) [Fintype V] [Fintype E] (N : Network V E X), N.IsBinaryNetwork →
        N.ForGenericParams fun θ => F (N.cf θ) = N.treeOfBlobs := by
  obtain ⟨F, hF⟩ := Allman2023.theorem4 X hX
  refine ⟨fun p => F (p ∘ quartetTreeEquiv.symm), fun V E _ _ N hN => ?_⟩
  have hN' := (Network.isBinaryNetwork_iff N).mp hN
  refine N.forGenericParams_of hN (fun θ _ hQ => ?_) (hF V E N.toRooted hN')
  rw [Network.cf_eq, Network.treeOfBlobs_eq, ← Bridges.splits_Trd hN' hX, ← hQ]
  rfl

end Allman2023.Model
