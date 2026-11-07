/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLemmas
public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitSummand
public import WaveTurbulence.Foundations.VineEst.VineEstS4.OrderCore

/-! # V5W-B (ruling F2): transport of the root parent layers of the selected rows

The selected rows of a CL region read the root parent layers `coupleRootParents`/`treeRootParent` of their native
objects.  For a regional pair (both leaves internal) and an interior branch these are the core layers of the parent
atom in the region (`Flower.V5W.real_child`, `coupleRootParents_zero/_one`, `treeRootParent_eq`).  Hence two
reconstruction data of the same skeleton whose core layers agree on the region have the same root parent layers
(`coupleRootParents_congr`, `treeRootParent_congr`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.VineEst
open WaveTurbulence WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS4 TTree

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Both leaves of a regional pair are realization nodes of the region, other than its upper joint. -/
theorem regionalPair_leaves_real (hG : G.IsPlain) {p : SourcePair G} (hp : p ∈ clRegionalPairs hG U) :
    (p.firstLeaf hG).toNode ∈ clRealizationNodes G U ∧ (p.firstLeaf hG).toNode ≠ a.toNode ∧
      (p.secondLeaf hG).toNode ∈ clRealizationNodes G U ∧ (p.secondLeaf hG).toNode ≠ a.toNode := by
  have hint := (mem_clRegionalPairs G).mp hp
  refine ⟨(leaf_mem_clRealizationNodes _).mpr hint, (Mole.branch_toNode_ne_leaf a _).symm, ?_,
    (Mole.branch_toNode_ne_leaf a _).symm⟩
  have := (Mole.internal_leaf_pair_iff G U (p.firstLeaf hG)).mpr hint
  rw [pair_first_eq_second hG p] at this
  exact (leaf_mem_clRealizationNodes _).mpr this

/-- **Root parents of a regional pair** agree for two data of the same skeleton whose core layers agree on the region. -/
theorem coupleRootParents_congr (hB : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain)
    (D1 D2 : ReconstructionData G) (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
    (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2)
    (hl : ∀ v ∈ U, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
    (pp : ℕ) {p : SourcePair G} (hp : p ∈ clRegionalPairs hG U) (i : Fin 2) :
    Flower.V5W.coupleRootParents pp D1 hG layer1 hLayer1 p i = Flower.V5W.coupleRootParents pp D2 hG layer2 hLayer2 p i := by
  obtain ⟨hr1, hl1, hr2, hl2⟩ := regionalPair_leaves_real (a := a) hG hp
  obtain ⟨v1, i1, hv1, hx1⟩ := Flower.V5W.real_child hB R hr1 hl1
  obtain ⟨v2, i2, hv2, hx2⟩ := Flower.V5W.real_child hB R hr2 hl2
  fin_cases i
  · show Flower.V5W.coupleRootParents pp D1 hG layer1 hLayer1 p 0 = Flower.V5W.coupleRootParents pp D2 hG layer2 hLayer2 p 0
    rw [Flower.V5W.coupleRootParents_zero D1 hG layer1 hLayer1 pp p v1 i1 hx1,
      Flower.V5W.coupleRootParents_zero D2 hG layer2 hLayer2 pp p v1 i1 hx1, hl v1 hv1]
  · show Flower.V5W.coupleRootParents pp D1 hG layer1 hLayer1 p 1 = Flower.V5W.coupleRootParents pp D2 hG layer2 hLayer2 p 1
    rw [Flower.V5W.coupleRootParents_one D1 hG layer1 hLayer1 pp p v2 i2 hx2,
      Flower.V5W.coupleRootParents_one D2 hG layer2 hLayer2 pp p v2 i2 hx2, hl v2 hv2]

/-- **The root parent of an interior branch** agrees for two data of the same skeleton whose core layers agree on the
region. -/
theorem treeRootParent_congr (hB : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain)
    (D1 D2 : ReconstructionData G) (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
    (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2)
    (hl : ∀ v ∈ U, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
    (pp : ℕ) {v : GBranch G.tree} (hv : v ∈ clInteriorBranches R) :
    Flower.V5W.treeRootParent pp D1 hG layer1 hLayer1 v = Flower.V5W.treeRootParent pp D2 hG layer2 hLayer2 v := by
  have hvU : v ∈ U := Finset.mem_of_mem_erase hv
  have hva : v.toNode ≠ a.toNode := fun h => (Finset.mem_erase.mp hv).1 (Mole.branch_toNode_injective h)
  obtain ⟨c, i, hc, hxc⟩ := Flower.V5W.real_child hB R ((branch_mem_clRealizationNodes v).mpr hvU) hva
  rw [Flower.V5W.treeRootParent_eq D1 hG layer1 hLayer1 pp v c i hxc,
    Flower.V5W.treeRootParent_eq D2 hG layer2 hLayer2 pp v c i hxc, hl c hc]

private theorem parentLayer_of_root {w' : ℕ} (LG : LayeredGarden w') (top : ℕ) (x : GNode LG.garden.tree)
    (h : x.1.2 = []) : LG.parentLayer top x = top := by
  unfold LayeredGarden.parentLayer
  rw [if_pos h]

/-- **Root parents of any source pair** agree for two data of the same skeleton whose core layers agree on every
branch: a root leaf reads the top value, a non-root leaf the core layer of its parent atom. -/
theorem coupleRootParents_congr_all (hG : G.IsPlain) (D1 D2 : ReconstructionData G)
    (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
    (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2)
    (hl : ∀ v : GBranch G.tree, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
    (pp : ℕ) (p : SourcePair G) (i : Fin 2) :
    Flower.V5W.coupleRootParents pp D1 hG layer1 hLayer1 p i = Flower.V5W.coupleRootParents pp D2 hG layer2 hLayer2 p i := by
  fin_cases i
  · show Flower.V5W.coupleRootParents pp D1 hG layer1 hLayer1 p 0 = Flower.V5W.coupleRootParents pp D2 hG layer2 hLayer2 p 0
    by_cases h : (p.firstLeaf hG).toNode.1.2 = []
    · have e : ∀ (D : ReconstructionData G) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer),
          Flower.V5W.coupleRootParents pp D hG layer hLayer p 0 = pp := by
        intro D layer hLayer
        unfold Flower.V5W.coupleRootParents
        apply parentLayer_of_root
        change (inflatedPosition G D.tree (p.firstLeaf hG).toNode).2 ++ [] = []
        rw [List.append_nil, inflatedPosition, dif_pos h]
        exact h
      rw [e D1 layer1 hLayer1, e D2 layer2 hLayer2]
    · have hx := (Mole.parent_child_eq_node (p.firstLeaf hG).toNode h).symm
      rw [Flower.V5W.coupleRootParents_zero D1 hG layer1 hLayer1 pp p _ _ hx,
        Flower.V5W.coupleRootParents_zero D2 hG layer2 hLayer2 pp p _ _ hx, hl]
  · show Flower.V5W.coupleRootParents pp D1 hG layer1 hLayer1 p 1 = Flower.V5W.coupleRootParents pp D2 hG layer2 hLayer2 p 1
    by_cases h : (p.secondLeaf hG).toNode.1.2 = []
    · have e : ∀ (D : ReconstructionData G) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer),
          Flower.V5W.coupleRootParents pp D hG layer hLayer p 1 = pp := by
        intro D layer hLayer
        unfold Flower.V5W.coupleRootParents
        apply parentLayer_of_root
        change (inflatedPosition G D.tree (p.secondLeaf hG).toNode).2 ++ [] = []
        rw [List.append_nil, inflatedPosition, dif_pos h]
        exact h
      rw [e D1 layer1 hLayer1, e D2 layer2 hLayer2]
    · have hx := (Mole.parent_child_eq_node (p.secondLeaf hG).toNode h).symm
      rw [Flower.V5W.coupleRootParents_one D1 hG layer1 hLayer1 pp p _ _ hx,
        Flower.V5W.coupleRootParents_one D2 hG layer2 hLayer2 pp p _ _ hx, hl]

/-- **The root parent of any branch** agrees for two data of the same skeleton whose core layers agree on every
branch. -/
theorem treeRootParent_congr_all (hG : G.IsPlain) (D1 D2 : ReconstructionData G)
    (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
    (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2)
    (hl : ∀ v : GBranch G.tree, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
    (pp : ℕ) (v : GBranch G.tree) :
    Flower.V5W.treeRootParent pp D1 hG layer1 hLayer1 v = Flower.V5W.treeRootParent pp D2 hG layer2 hLayer2 v := by
  by_cases h : v.toNode.1.2 = []
  · have e : ∀ (D : ReconstructionData G) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer),
        Flower.V5W.treeRootParent pp D hG layer hLayer v = pp := by
      intro D layer hLayer
      unfold Flower.V5W.treeRootParent
      apply parentLayer_of_root
      change (inflatedPosition G D.tree v.toNode).2 ++ [] = []
      rw [List.append_nil, inflatedPosition, dif_pos h]
      exact h
    rw [e D1 layer1 hLayer1, e D2 layer2 hLayer2]
  · have hx := (Mole.parent_child_eq_node v.toNode h).symm
    rw [Flower.V5W.treeRootParent_eq D1 hG layer1 hLayer1 pp v _ _ hx,
      Flower.V5W.treeRootParent_eq D2 hG layer2 hLayer2 pp v _ _ hx, hl]

section SelData
variable {u : Unit} [S : RowSel u] {d : ℕ}

/-- **Agreement of the selection data** of two reconstruction data of one skeleton on a set of source pairs and a set
of branches: the incoherency indices of those rows, and the core layers of all branches (which fix the root parent
layers, `coupleRootParents_congr_all`). -/
def SelDataEq (hG : G.IsPlain) (D1 D2 : ReconstructionData G) (layer1 : GNode (D1.forest hG) → ℕ)
    (hLayer1 : IsLayering (D1.garden hG) layer1) (layer2 : GNode (D2.forest hG) → ℕ)
    (hLayer2 : IsLayering (D2.garden hG) layer2) (Ps : Finset (SourcePair G)) (Vs : Finset (GBranch G.tree)) : Prop :=
  (∀ p ∈ Ps, Flower.V5W.coupleIncoh D1 hG layer1 hLayer1 p = Flower.V5W.coupleIncoh D2 hG layer2 hLayer2 p) ∧
  (∀ v ∈ Vs, Flower.V5W.treeIncoh D1 hG layer1 hLayer1 v = Flower.V5W.treeIncoh D2 hG layer2 hLayer2 v) ∧
  (∀ v : GBranch G.tree, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)

theorem SelDataEq.refl (hG : G.IsPlain) (D : ReconstructionData G) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (Ps : Finset (SourcePair G)) (Vs : Finset (GBranch G.tree)) :
    SelDataEq hG D D layer hLayer layer hLayer Ps Vs :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem SelDataEq.symm {hG : G.IsPlain} {D1 D2 : ReconstructionData G} {layer1 : GNode (D1.forest hG) → ℕ}
    {hLayer1 : IsLayering (D1.garden hG) layer1} {layer2 : GNode (D2.forest hG) → ℕ}
    {hLayer2 : IsLayering (D2.garden hG) layer2} {Ps : Finset (SourcePair G)} {Vs : Finset (GBranch G.tree)}
    (h : SelDataEq hG D1 D2 layer1 hLayer1 layer2 hLayer2 Ps Vs) :
    SelDataEq hG D2 D1 layer2 hLayer2 layer1 hLayer1 Ps Vs :=
  ⟨fun p hp => (h.1 p hp).symm, fun v hv => (h.2.1 v hv).symm, fun v => (h.2.2 v).symm⟩

/-- Under `SelDataEq`, a couple row with equal native objects is the same selected row. -/
theorem selCoupleRow_of_selDataEq {hG : G.IsPlain} {D1 D2 : ReconstructionData G}
    {layer1 : GNode (D1.forest hG) → ℕ} {hLayer1 : IsLayering (D1.garden hG) layer1}
    {layer2 : GNode (D2.forest hG) → ℕ} {hLayer2 : IsLayering (D2.garden hG) layer2}
    {Ps : Finset (SourcePair G)} {Vs : Finset (GBranch G.tree)}
    (h : SelDataEq hG D1 D2 layer1 hLayer1 layer2 hLayer2 Ps Vs) {p : SourcePair G} (hp : p ∈ Ps)
    (hC : nativeCoupleLayered D1 hG layer1 hLayer1 p = nativeCoupleLayered D2 hG layer2 hLayer2 p)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (t s : ℝ) (k : Mom d) :
    selCoupleRow L γ δ F D1 hG layer1 hLayer1 p t s k = selCoupleRow L γ δ F D2 hG layer2 hLayer2 p t s k :=
  selCoupleRow_congr L γ δ F D2 hG layer2 hLayer2 p D1 hG layer1 hLayer1 p hC (h.1 p hp)
    (coupleRootParents_congr_all hG D1 D2 layer1 hLayer1 layer2 hLayer2 h.2.2 S.p p) t s k

/-- Under `SelDataEq`, a tree row with equal native objects is the same selected row. -/
theorem selTreeRow_of_selDataEq {hG : G.IsPlain} {D1 D2 : ReconstructionData G}
    {layer1 : GNode (D1.forest hG) → ℕ} {hLayer1 : IsLayering (D1.garden hG) layer1}
    {layer2 : GNode (D2.forest hG) → ℕ} {hLayer2 : IsLayering (D2.garden hG) layer2}
    {Ps : Finset (SourcePair G)} {Vs : Finset (GBranch G.tree)}
    (h : SelDataEq hG D1 D2 layer1 hLayer1 layer2 hLayer2 Ps Vs) {v : GBranch G.tree} (hv : v ∈ Vs)
    (hT : nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (t s : ℝ) (k : Mom d) :
    selTreeRow L γ δ F D1 hG layer1 hLayer1 v t s k = selTreeRow L γ δ F D2 hG layer2 hLayer2 v t s k :=
  selTreeRow_congr L γ δ F D2 hG layer2 hLayer2 v D1 hG layer1 hLayer1 v hT (h.2.1 v hv)
    (treeRootParent_congr_all hG D1 D2 layer1 hLayer1 layer2 hLayer2 h.2.2 S.p v) t s k

end SelData

end WaveTurbulence.VineEst
