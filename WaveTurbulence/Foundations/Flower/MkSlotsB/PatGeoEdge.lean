/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeo
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCore
public import WaveTurbulence.Foundations.Molecule.ChainPartitions
public import WaveTurbulence.Foundations.IncohInst.LayerReg.Embed

/-! # B3s-HELPER3 B4 (2/4): the relaxed edges of the reconstruction of a member

On the reconstruction `LG = layeredReconstruction D hS layer hLayer` of a skeleton `S` (cap trees `J` single leaves,
`CapGeo`), a parent/child pair of branches BOTH pinned by `fixCap LG J pat t s` (any pattern) is
* (a) a core edge: both ends core branches `D.coreBranch hS b`, `D.coreBranch hS b'`, `b'` a skeleton child of `b`;
* (b) a slot top with its clock: `B = D.coreBranch hS b` and `C` the top (attached node) of the native object of the
  slot of the skeleton child `b.child i` — the top of the regular chain of a branch `b'` (`lonePath ≠ []`), or the
  root of the native couple of the pair of a leaf `σ`;
* (c) inside the native couple of a cap pair (`IsCapPair`), both ends in the same cap slot;
* (e) **a regular chain's terminal node above its core**: `C = D.coreBranch hS π` is a capped flower parent, the chain
  `D.tree π` is non-trivial, `B` is its terminal (penultimate lone-path) node, a native branch of the chain slot
  `.inr π`, and the pattern of the tree is `dParent` (`relaxedEdge_classification`).

Case (e) is NOT in the list of the B4 brief, and it occurs: D2b's `objCfg` (`ProtGeo/Pins.lean`) assigns the stem chain
whose port is the capped flower parent (`PortFP`) the configuration `.term` under `dParent` (its terminal node at `s`),
and the core branch below it (the chain's lower clock) is the capped flower parent at `s`. Configuration: a non-cap
tree whose capped flower `f` (paired with a cap root) is a child of the core branch `c = D.coreBranch π` (trivial cap
couple at the skeleton leaf of `f`), with a non-trivial regular chain `D.tree π` (lone path `[i₁, …, i₂ₘ]`, `m ≥ 1`) inflated
above `c`, pattern `dParent`: then `c` and its parent `B` (at `inflatedPosition π ++ lonePath.dropLast`, inside the
chain) are both pinned at `s`. Nothing prevents it (CapGeo only puts the stem, chain nodes included, in layer `p`).

Roots pinned at their upper time `t` (d): `rootPin_classification` — `pat = dRoot`, not a capped flower parent, and
the root is the core of a skeleton root with trivial chain, the top of its non-trivial chain, or the root of a native
couple (single-leaf skeleton tree). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntGeo
open WaveTurbulence.Flower.MkSlots.IntRest

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

/-! ## The attached top of a skeleton node -/

/-- **The top of the native object attached at the skeleton node `x`**: the core branch of `x` (a branch with trivial
chain), the top of the non-trivial chain of `x`, or the root on `x`'s side of the native couple of the pair of the
leaf `x`. -/
def AttachedTop (x : GNode S.tree) (C : GBranch (D.forest hS)) : Prop :=
  (∃ b' : GBranch S.tree, b'.toNode = x ∧ (D.tree b').lonePath = [] ∧ C = D.coreBranch hS b') ∨
  (∃ b' : GBranch S.tree, b'.toNode = x ∧ (D.tree b').lonePath ≠ [] ∧ C.1 = inflatedPosition S D.tree b'.toNode ∧
    slotOf D hS C.toNode = .inr b') ∨
  (∃ σ : GLeaf S.tree, σ.toNode = x ∧ C.toNode = attachedNode D hS σ.toNode ∧
    slotOf D hS C.toNode = .inl (pairOfLeaf S hS σ))

/-- The native top node of the chain slot `.inr b'`. -/
theorem slotOf_chainTop (b' : GBranch S.tree) (C : GBranch (D.forest hS))
    (hC : C.1 = inflatedPosition S D.tree b'.toNode) : slotOf D hS C.toNode = .inr b' := by
  let a : NativeNode D (.inr b') := ⟨((0 : Fin 1), []), TTree.nil_mem_nodes _⟩
  have he : nativeNodeAt D hS (.inr b') a = C.toNode := by
    apply Subtype.ext
    show addrExt (inflatedPosition S D.tree b'.toNode) [] = C.1
    rw [hC]
    simp [addrExt]
  rw [← he]
  exact slotOf_nativeNodeAt D hS _ a

/-- **Every branch attached at a skeleton node is the top of its native object.** -/
theorem attachedTop_of_eq (x : GNode S.tree) (C : GBranch (D.forest hS)) (hC : C.toNode = attachedNode D hS x) :
    AttachedTop D hS x C := by
  rcases (Comb.TreePath.mem_nodes_iff _ _).mp x.2 with hl | hbr
  · let σ : GLeaf S.tree := ⟨x.1, hl⟩
    have hσ : σ.toNode = x := rfl
    refine Or.inr (Or.inr ⟨σ, hσ, hσ ▸ hC, ?_⟩)
    rw [hC, ← hσ]
    exact slotOf_attached_leaf D hS σ
  · let b' : GBranch S.tree := ⟨x.1, hbr⟩
    have hb' : b'.toNode = x := rfl
    have hv : C.1 = inflatedPosition S D.tree b'.toNode := congrArg Subtype.val hC
    by_cases h0 : (D.tree b').lonePath = []
    · refine Or.inl ⟨b', hb', h0, Subtype.ext ?_⟩
      show C.1 = D.corePosition b'
      unfold ReconstructionData.corePosition
      rw [hv, h0]
      simp [addrExt]
    · exact Or.inr (Or.inl ⟨b', hb', h0, hv, slotOf_chainTop D hS b' C hv⟩)

/-! ## Capped flower parents: core branches or inside a cap native -/

/-- **A capped flower parent is a core branch or a branch of the native couple of a cap pair.** (The proof of
`IntGeo.capParent_inCapNative`, keeping the native branch.) -/
theorem capParent_core_or_native (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (B : GBranch (D.forest hS)) (hB : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J B) :
    (∃ b, B = D.coreBranch hS b) ∨
      ∃ (q : SourcePair S) (c : GBranch (nativeCoupleForest D hS q).shape), IsCapPair S hS J q ∧
        B = subforestBranchEmbedding (nativeCoupleForest D hS q) c := by
  by_cases hnc : ∃ b, B = D.coreBranch hS b
  · exact Or.inl hnc
  right
  have hnc' : ∀ b, B ≠ D.coreBranch hS b := fun b h => hnc ⟨b, h⟩
  obtain ⟨ℓ, ⟨-, hpJ⟩, hℓt, i0, hℓp⟩ := hB
  obtain ⟨q, hq, hcq⟩ := leaf_inCapNative D hS J hcap ℓ (Or.inr hpJ)
  obtain ⟨a, ha⟩ := exists_nativeNodeAt_of_slotOf D hS hq
  by_cases h0 : a.1.2 = []
  · exfalso
    have hr : nativeNodeAt D hS (.inl q) a = (nativeCoupleForest D hS q).root a.1.1 := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      show ((nativeCoupleForest D hS q).root a.1.1).1.2 ++ a.1.2 = _
      rw [h0, List.append_nil]
    obtain ⟨σ, hσ⟩ := nativeRoot_attached D hS q a.1.1
    have hℓσ : ℓ.toNode = attachedNode D hS σ.toNode := ha.symm.trans (hr.trans hσ)
    by_cases hσr : σ.toNode.1.2 = []
    · have he : σ.toNode = GNode.root S.tree σ.1.1 := Subtype.ext (Prod.ext rfl hσr)
      have hroot : attachedNode D hS σ.toNode = GNode.root (D.forest hS) σ.1.1 := by
        rw [he]
        exact attachedNode_root D hS _
      have hp : ℓ.1.2 = [] := congrArg (fun z : GNode (D.forest hS) => z.1.2) (hℓσ.trans hroot)
      rw [hℓp] at hp
      simp at hp
    · exact hnc' _ (branch_eq_of_isParentOf ⟨hℓt, i0, hℓp⟩ _
        (hℓσ.trans (attachedNode_nonroot D hS σ.toNode hσr)))
  · let E := nativeCoupleForest D hS q
    let c : GBranch E.shape := GNode.parent (tree := E.shape) a h0
    have hv := congrArg Subtype.val ha
    have hv1 : (E.root a.1.1).1.1 = ℓ.1.1 := by have h := congrArg Prod.fst hv; exact h
    have hv2 : (E.root a.1.1).1.2 ++ a.1.2 = ℓ.1.2 := by have h := congrArg Prod.snd hv; exact h
    refine ⟨q, c, hcq, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hℓt.symm.trans hv1.symm
    · show B.1.2 = (E.root a.1.1).1.2 ++ a.1.2.dropLast
      rw [← List.dropLast_append_of_ne_nil h0, hv2, hℓp, List.dropLast_concat]

/-- The node of a native couple branch lies in that slot. -/
theorem slotOf_subforestBranch (q : SourcePair S) (c : GBranch (nativeCoupleForest D hS q).shape) :
    slotOf D hS (subforestBranchEmbedding (nativeCoupleForest D hS q) c).toNode = .inl q := by
  rw [← subforest_branch_node]
  exact slotOf_nativeNodeAt D hS (.inl q) c.toNode

/-- The children of a native couple branch lie in that slot. -/
theorem slotOf_subforestBranch_child (q : SourcePair S) (c : GBranch (nativeCoupleForest D hS q).shape)
    (i : Fin 3) : slotOf D hS ((subforestBranchEmbedding (nativeCoupleForest D hS q) c).child i) = .inl q := by
  rw [← subforest_node_child]
  exact slotOf_nativeNodeAt D hS (.inl q) (c.child i)

/-! ## Parents and children -/

/-- The address of the parent of a child branch. -/
theorem parent_addr {T : Fin w → TTree} {B C : GBranch T} (h : C.IsChildOf B) :
    B.1 = (C.1.1, C.1.2.dropLast) := by
  obtain ⟨h1, i, h2⟩ := h
  rw [h2, List.dropLast_concat, h1]

/-- A child branch of a core branch is attached at a skeleton child. -/
theorem child_of_core {b : GBranch S.tree} {C : GBranch (D.forest hS)} (h : C.IsChildOf (D.coreBranch hS b)) :
    ∃ i : Fin 3, C.toNode = attachedNode D hS (b.child i) := by
  obtain ⟨h1, i, h2⟩ := h
  refine ⟨i, ?_⟩
  rw [attachedNode_child]
  exact Subtype.ext (Prod.ext h1 h2)

/-! ## The classification -/

variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)

/-- The terminal node of a non-trivial chain is a native branch of the chain slot. -/
theorem slotOf_chainTerminal (π : GBranch S.tree) (h0 : (D.tree π).lonePath ≠ []) (B : GBranch (D.forest hS))
    (hB : B.1 = addrExt (inflatedPosition S D.tree π.toNode) (D.tree π).lonePath.dropLast) :
    slotOf D hS B.toNode = .inr π := by
  let z : NativeNode D (.inr π) := ⟨((0 : Fin 1), (D.tree π).lonePath),
    Links.lonePath_mem_plug (D.tree π) (nodeSign S.sig π.1) TTree.leaf⟩
  let a : NativeNode D (.inr π) := (GNode.parent (tree := (decodedTree (D.tree π) (nodeSign S.sig π.1)).tree) z h0).toNode
  have he : nativeNodeAt D hS (.inr π) a = B.toNode := by
    apply Subtype.ext
    show addrExt (inflatedPosition S D.tree π.toNode) (D.tree π).lonePath.dropLast = B.1
    rw [hB]
  rw [← he]
  exact slotOf_nativeNodeAt D hS _ a

end WaveTurbulence.Flower.MkSlotsB
