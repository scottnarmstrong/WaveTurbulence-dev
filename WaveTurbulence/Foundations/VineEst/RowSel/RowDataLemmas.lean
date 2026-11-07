/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.RowData
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLRegionSupport
public import WaveTurbulence.Foundations.Molecule.LFTwist.SourcePairTransport

/-! # V5W-B (ruling F2): the row data read structurally, copied by source

Verbatim copies (statements, proofs, namespace `WaveTurbulence.Flower.V5W` unchanged) of V5W-0's
* `Flower/V5W/RowData.lean` (sha256 `7de6c466f12ddcffe94a8c1399fb30291e6d94ec2b1d8440e60b0d561bfda5e2`), section
  `Parents`: `parentLayer_coreChild`, `coupleRootParents_zero`, `coupleRootParents_one`, `treeRootParent_eq`,
  `eq_or_pair_of_pairOfLeaf` (lines 30–75, 100–116; the two `nodeRowIncoh` lemmas are not copied, `nodeRowIncoh` is not
  on main);
* `Flower/V5W/Rigid.lean` (sha256 `2a048381c05249b54f13822f2ad5e04e7a88c04de1f5dec893e9526d9a99b794`): `real_child`
  (lines 27–33).

The root of a native row attached at a child `v.child j` of a skeleton branch has, in the reconstructed garden, the
parent layer of the core of `v`; a realization node of a CL region other than its upper joint is a child of an atom of
the region.  These transport the root parent layers of the selected rows along the twist and rigid maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.LFTwist WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree

/-- A realization node of a CL region other than its upper joint is a child of an atom of the region. -/
theorem real_child {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) {x : GNode G.tree}
    (hx : x ∈ clRealizationNodes G U) (hxa : x ≠ a.toNode) :
    ∃ (v : GBranch G.tree) (j : Fin 3), v ∈ U ∧ x = v.child j := by
  obtain ⟨hn, hp⟩ := cl_realization_parent hB R x hx hxa
  exact ⟨x.parent hn, x.1.2.getLast hn, hp, (Mole.parent_child_eq_node x hn).symm⟩

section Parents
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

/-- A node attached directly below the core of a skeleton branch `v` has the parent layer of that core. -/
theorem parentLayer_coreChild (p : ℕ) (v : GBranch S.tree) (j : Fin 3) (a : GNode (D.forest hS))
    (ha : a.1 = addrExt (D.corePosition v) [j]) :
    (layeredReconstruction D hS layer hLayer).parentLayer p a = layer (D.coreBranch hS v).toNode := by
  have hne : a.1.2 ≠ [] := by
    rw [ha]
    simp [addrExt]
  unfold LayeredGarden.parentLayer
  rw [if_neg hne]
  refine congrArg layer (Subtype.ext ?_)
  change (a.1.1, a.1.2.dropLast) = D.corePosition v
  rw [ha]
  simp [addrExt]

theorem coupleRootParents_zero (p : ℕ) (pr : SourcePair S) (v : GBranch S.tree) (j : Fin 3)
    (hv : (pr.firstLeaf hS).toNode = v.child j) :
    coupleRootParents p D hS layer hLayer pr 0 = layer (D.coreBranch hS v).toNode := by
  unfold coupleRootParents
  refine parentLayer_coreChild D hS layer hLayer p v j _ ?_
  rw [← D.core_child_position v j, ← hv]
  change ((inflatedPosition S D.tree (pr.firstLeaf hS).toNode).1,
    (inflatedPosition S D.tree (pr.firstLeaf hS).toNode).2 ++ []) = _
  rw [List.append_nil]

theorem coupleRootParents_one (p : ℕ) (pr : SourcePair S) (v : GBranch S.tree) (j : Fin 3)
    (hv : (pr.secondLeaf hS).toNode = v.child j) :
    coupleRootParents p D hS layer hLayer pr 1 = layer (D.coreBranch hS v).toNode := by
  unfold coupleRootParents
  refine parentLayer_coreChild D hS layer hLayer p v j _ ?_
  rw [← D.core_child_position v j, ← hv]
  change ((inflatedPosition S D.tree (pr.secondLeaf hS).toNode).1,
    (inflatedPosition S D.tree (pr.secondLeaf hS).toNode).2 ++ []) = _
  rw [List.append_nil]

theorem treeRootParent_eq (p : ℕ) (v c : GBranch S.tree) (j : Fin 3) (hv : v.toNode = c.child j) :
    treeRootParent p D hS layer hLayer v = layer (D.coreBranch hS c).toNode := by
  unfold treeRootParent
  refine parentLayer_coreChild D hS layer hLayer p c j _ ?_
  rw [← D.core_child_position c j, ← hv]
  change addrExt (inflatedPosition S D.tree v.toNode) [] = _
  simp [addrExt]

/-- Two leaves with the same source pair are equal or partners. -/
theorem eq_or_pair_of_pairOfLeaf {l r : GLeaf S.tree} (h : pairOfLeaf S hS l = pairOfLeaf S hS r) :
    l = r ∨ l = S.pair r := by
  have h1 := pairOfLeaf_first_or_partner S hS l
  have h2 := pairOfLeaf_first_or_partner S hS r
  rw [h] at h1
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h1.symm.trans h2)
  · exact Or.inr (h1.symm.trans h2)
  · right
    have := congrArg S.pair (h1.symm.trans h2)
    rwa [S.pair_pair] at this
  · left
    have := congrArg S.pair (h1.symm.trans h2)
    rwa [S.pair_pair, S.pair_pair] at this

end Parents

end WaveTurbulence.Flower.V5W
