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

/-- **The parent of a core branch**: inside its non-trivial chain (the terminal node), or the core branch of the
skeleton parent (trivial chain). -/
theorem parent_of_core {π : GBranch S.tree} {B : GBranch (D.forest hS)} (h : (D.coreBranch hS π).IsChildOf B) :
    ((D.tree π).lonePath ≠ [] ∧
        B.1 = addrExt (inflatedPosition S D.tree π.toNode) (D.tree π).lonePath.dropLast) ∨
      ∃ b : GBranch S.tree, π.IsChildOf b ∧ B = D.coreBranch hS b := by
  have hB := parent_addr h
  have hC1 : (D.coreBranch hS π).1.1 = (inflatedPosition S D.tree π.toNode).1 := rfl
  have hC2 : (D.coreBranch hS π).1.2 = (inflatedPosition S D.tree π.toNode).2 ++ (D.tree π).lonePath := rfl
  by_cases h0 : (D.tree π).lonePath = []
  · right
    have hnr : π.toNode.1.2 ≠ [] := by
      intro hr
      have hip : inflatedPosition S D.tree π.toNode = π.toNode.1 := by
        rw [inflatedPosition]
        simp only [hr, ↓reduceDIte]
      obtain ⟨-, i, hi⟩ := h
      rw [hC2, h0, hip, List.append_nil, hr] at hi
      simp at hi
    let b := π.toNode.parent hnr
    have hip : inflatedPosition S D.tree π.toNode =
        addrExt (inflatedPosition S D.tree b.toNode) ((D.tree b).lonePath ++ [π.1.2.getLast hnr]) := by
      rw [inflatedPosition]
      simp only [hnr, ↓reduceDIte]
      rfl
    refine ⟨b, ⟨rfl, π.1.2.getLast hnr, (List.dropLast_append_getLast hnr).symm⟩, ?_⟩
    apply Subtype.ext
    rw [hB]
    show ((D.coreBranch hS π).1.1, (D.coreBranch hS π).1.2.dropLast) =
      addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath
    rw [hC1, hC2, h0, List.append_nil, hip]
    simp only [addrExt]
    rw [← List.append_assoc, List.dropLast_concat]
  · left
    refine ⟨h0, ?_⟩
    rw [hB, hC1, hC2, List.dropLast_append_of_ne_nil h0]
    rfl

/-- **The parent of a native couple branch**: in the same native couple, or (at a native root) the core branch whose
child is attached there. -/
theorem parent_of_native {q : SourcePair S} {c : GBranch (nativeCoupleForest D hS q).shape}
    {B : GBranch (D.forest hS)} (h : (subforestBranchEmbedding (nativeCoupleForest D hS q) c).IsChildOf B) :
    slotOf D hS B.toNode = .inl q ∨
      ∃ (b : GBranch S.tree) (i : Fin 3), B = D.coreBranch hS b ∧
        AttachedTop D hS (b.child i) (subforestBranchEmbedding (nativeCoupleForest D hS q) c) := by
  have hB := parent_addr h
  have hE1 : (subforestBranchEmbedding (nativeCoupleForest D hS q) c).1.1 =
      ((nativeCoupleForest D hS q).root c.1.1).1.1 := rfl
  have hE2 : (subforestBranchEmbedding (nativeCoupleForest D hS q) c).1.2 =
      ((nativeCoupleForest D hS q).root c.1.1).1.2 ++ c.1.2 := rfl
  by_cases h0 : c.1.2 = []
  · right
    have hroot : (subforestBranchEmbedding (nativeCoupleForest D hS q) c).toNode =
        (nativeCoupleForest D hS q).root c.1.1 := by
      apply Subtype.ext
      show ((subforestBranchEmbedding (nativeCoupleForest D hS q) c).1.1,
        (subforestBranchEmbedding (nativeCoupleForest D hS q) c).1.2) = ((nativeCoupleForest D hS q).root c.1.1).1
      rw [hE1, hE2, h0, List.append_nil]
    obtain ⟨σ, hσ⟩ := nativeRoot_attached D hS q c.1.1
    by_cases hσr : σ.toNode.1.2 = []
    · exfalso
      have he : σ.toNode = GNode.root S.tree σ.1.1 := Subtype.ext (Prod.ext rfl hσr)
      have hr : attachedNode D hS σ.toNode = GNode.root (D.forest hS) σ.1.1 := by
        rw [he]; exact attachedNode_root D hS _
      have hp := congrArg (fun z : GNode (D.forest hS) => z.1.2) (hroot.trans (hσ.trans hr))
      obtain ⟨-, i, hi⟩ := h
      have hp' : (subforestBranchEmbedding (nativeCoupleForest D hS q) c).1.2 = [] := hp
      rw [hp'] at hi
      simp at hi
    · let b := σ.toNode.parent hσr
      let i := σ.1.2.getLast hσr
      have hat : attachedNode D hS σ.toNode = (D.coreBranch hS b).child i :=
        attachedNode_nonroot D hS σ.toNode hσr
      have hCn : (subforestBranchEmbedding (nativeCoupleForest D hS q) c).toNode = (D.coreBranch hS b).child i :=
        hroot.trans (hσ.trans hat)
      refine ⟨b, i, ?_, attachedTop_of_eq D hS _ _ ?_⟩
      · apply Subtype.ext
        rw [hB]
        have hv := congrArg Subtype.val hCn
        have h1 : (subforestBranchEmbedding (nativeCoupleForest D hS q) c).1.1 = (D.coreBranch hS b).1.1 := by
          have h := congrArg Prod.fst hv; exact h
        have h2 : (subforestBranchEmbedding (nativeCoupleForest D hS q) c).1.2 = (D.coreBranch hS b).1.2 ++ [i] := by
          have h := congrArg Prod.snd hv; exact h
        rw [h1, h2, List.dropLast_concat]
      · rw [hCn, ← attachedNode_child]
  · left
    let c' : GBranch (nativeCoupleForest D hS q).shape :=
      GNode.parent (tree := (nativeCoupleForest D hS q).shape) c.toNode h0
    have he : B = subforestBranchEmbedding (nativeCoupleForest D hS q) c' := by
      apply Subtype.ext
      rw [hB, hE1, hE2, List.dropLast_append_of_ne_nil h0]
      rfl
    rw [he]
    exact slotOf_subforestBranch D hS q c'

/-! ## The classification -/

variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)

/-- Two capped flower parents in one tree coincide (`CapGeo.one_flower`). -/
theorem cfp_eq {p : ℕ} (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p)
    {b b' : GBranch (D.forest hS)} (hb : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b)
    (hb' : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b') (h : b.1.1 = b'.1.1) : b = b' :=
  capFlowerParent_eq hG hb hb' h

/-- Two pinned branches forming a parent/child pair: one of them is a capped flower parent. -/
theorem pinned_pair_cfp {p : ℕ} (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p)
    {B C : GBranch (D.forest hS)} (hBC : C.IsChildOf B)
    (hB : (fixCap (layeredReconstruction D hS layer hLayer) J pat t s B).isSome)
    (hC : (fixCap (layeredReconstruction D hS layer hLayer) J pat t s C).isSome) :
    IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J B ∨
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C := by
  by_cases hnB : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J B
  · exact Or.inl hnB
  by_cases hnC : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C
  · exact Or.inr hnC
  exfalso
  obtain ⟨vB, hvB⟩ := Option.isSome_iff_exists.mp hB
  obtain ⟨vC, hvC⟩ := Option.isSome_iff_exists.mp hC
  obtain ⟨htr, i, hi⟩ := hBC
  have hpat : pat C.1.1 = pat B.1.1 := by rw [htr]
  have hlen : C.1.2.length = B.1.2.length + 1 := by rw [hi]; simp
  rcases fixCap_cases hvC with ⟨h, -⟩ | ⟨-, -, h0, -⟩ | ⟨-, hpC, ⟨c2, hc2, hc2C⟩, -⟩ | ⟨i2, -, hpC, ⟨c2, hc2, h21, h22⟩, -⟩
  · exact hnC h
  · rw [hi] at h0; simp at h0
  · rcases fixCap_cases hvB with ⟨h, -⟩ | ⟨-, hpB, -, -⟩ | ⟨-, -, ⟨c1, hc1, hc1B⟩, -⟩ | ⟨i1, -, hpB, -, -⟩
    · exact hnB h
    · rw [hpat, hpB] at hpC; exact absurd hpC (by simp)
    · have he := cfp_eq D hS layer hLayer J hG hc1 hc2 (by rw [hc1B.1, hc2C.1, htr])
      subst he
      obtain ⟨-, j1, hj1⟩ := hc1B
      obtain ⟨-, j2, hj2⟩ := hc2C
      have := congrArg List.length (hj1.symm.trans hj2)
      simp at this
      omega
    · rw [hpat, hpB] at hpC; exact absurd hpC (by simp)
  · rcases fixCap_cases hvB with ⟨h, -⟩ | ⟨-, hpB, -, -⟩ | ⟨-, hpB, -, -⟩ | ⟨i1, -, hpB, ⟨c1, hc1, h11, h12⟩, -⟩
    · exact hnB h
    · rw [hpat, hpB] at hpC; exact absurd hpC (by simp)
    · rw [hpat, hpB] at hpC; exact absurd hpC (by simp)
    · have he := cfp_eq D hS layer hLayer J hG hc1 hc2 (by rw [← h11, ← h21, htr])
      subst he
      have e1 := congrArg List.length h12
      have e2 := congrArg List.length h22
      have e3 := congrArg List.length hi
      simp at e1 e2 e3
      omega

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

/-- **The classification of the relaxed edges** (pinned parent/child pairs) of the reconstruction of a member, for
every pattern. Case (e) is not in the B4 brief's list (see the module docstring). -/
theorem relaxedEdge_classification {p : ℕ} (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p)
    (B C : GBranch (D.forest hS)) (hBC : C.IsChildOf B)
    (hB : (fixCap (layeredReconstruction D hS layer hLayer) J pat t s B).isSome)
    (hC : (fixCap (layeredReconstruction D hS layer hLayer) J pat t s C).isSome) :
    -- (a) a core edge
    (∃ b b' : GBranch S.tree, b'.IsChildOf b ∧ B = D.coreBranch hS b ∧ C = D.coreBranch hS b') ∨
    -- (b) a slot top with its clock
    (∃ (b : GBranch S.tree) (i : Fin 3), B = D.coreBranch hS b ∧
      ((∃ b' : GBranch S.tree, b'.toNode = b.child i ∧ (D.tree b').lonePath ≠ [] ∧
          C.1 = inflatedPosition S D.tree b'.toNode ∧ slotOf D hS C.toNode = .inr b') ∨
        (∃ σ : GLeaf S.tree, σ.toNode = b.child i ∧ C.toNode = attachedNode D hS σ.toNode ∧
          slotOf D hS C.toNode = .inl (pairOfLeaf S hS σ)))) ∨
    -- (c) inside the native couple of a cap pair
    (∃ q : SourcePair S, IsCapPair S hS J q ∧ slotOf D hS B.toNode = .inl q ∧ slotOf D hS C.toNode = .inl q) ∨
    -- (e) a regular chain's terminal node above its core branch (pattern `dParent`)
    (∃ π : GBranch S.tree, C = D.coreBranch hS π ∧
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C ∧
      pat B.1.1 = FixPat.dParent ∧ 2 ≤ (D.tree π).lonePath.length ∧
      B.1 = addrExt (inflatedPosition S D.tree π.toNode) (D.tree π).lonePath.dropLast ∧
      slotOf D hS B.toNode = .inr π) := by
  have hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf := hG.cap_leaf
  -- (a)/(b) from an `AttachedTop` below a core branch
  have hab : ∀ (b : GBranch S.tree) (i : Fin 3), B = D.coreBranch hS b → AttachedTop D hS (b.child i) C →
      (∃ b b' : GBranch S.tree, b'.IsChildOf b ∧ B = D.coreBranch hS b ∧ C = D.coreBranch hS b') ∨
      (∃ (b : GBranch S.tree) (i : Fin 3), B = D.coreBranch hS b ∧
        ((∃ b' : GBranch S.tree, b'.toNode = b.child i ∧ (D.tree b').lonePath ≠ [] ∧
            C.1 = inflatedPosition S D.tree b'.toNode ∧ slotOf D hS C.toNode = .inr b') ∨
          (∃ σ : GLeaf S.tree, σ.toNode = b.child i ∧ C.toNode = attachedNode D hS σ.toNode ∧
            slotOf D hS C.toNode = .inl (pairOfLeaf S hS σ)))) := by
    intro b i hBb hT
    rcases hT with ⟨b', hb', -, hCb'⟩ | hT | hT
    · refine Or.inl ⟨b, b', ⟨?_, i, ?_⟩, hBb, hCb'⟩
      · exact congrArg (fun x : GNode S.tree => x.1.1) hb'
      · exact congrArg (fun x : GNode S.tree => x.1.2) hb'
    · exact Or.inr ⟨b, i, hBb, Or.inl hT⟩
    · exact Or.inr ⟨b, i, hBb, Or.inr hT⟩
  rcases pinned_pair_cfp D hS layer hLayer J pat t s hG hBC hB hC with hcB | hcC
  · -- `B` is the capped flower parent
    rcases capParent_core_or_native D hS layer hLayer J hcap B hcB with ⟨b, rfl⟩ | ⟨q, c, hq, rfl⟩
    · obtain ⟨i, hi⟩ := child_of_core D hS hBC
      rcases hab b i rfl (attachedTop_of_eq D hS _ C hi) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · obtain ⟨h1, i, hi⟩ := hBC
      have hCc : C.toNode = (subforestBranchEmbedding (nativeCoupleForest D hS q) c).child i :=
        Subtype.ext (Prod.ext h1 hi)
      refine Or.inr (Or.inr (Or.inl ⟨q, hq, slotOf_subforestBranch D hS q c, ?_⟩))
      rw [hCc]
      exact slotOf_subforestBranch_child D hS q c i
  · -- `C` is the capped flower parent
    rcases capParent_core_or_native D hS layer hLayer J hcap C hcC with ⟨π, rfl⟩ | ⟨q, c, hq, rfl⟩
    · rcases parent_of_core D hS hBC with ⟨h0, haddr⟩ | ⟨b, hπb, rfl⟩
      · -- case (e)
        refine Or.inr (Or.inr (Or.inr ⟨π, rfl, hcC, ?_, ?_, haddr, slotOf_chainTerminal D hS π h0 B haddr⟩))
        · obtain ⟨vB, hvB⟩ := Option.isSome_iff_exists.mp hB
          have hlen2 : 2 ≤ (D.tree π).lonePath.length := by
            have hl := chain_lonePath_length (D.tree π)
            have hne : (D.tree π).lonePath.length ≠ 0 := fun h => h0 (List.length_eq_zero_iff.mp h)
            omega
          rcases fixCap_cases hvB with ⟨h, -⟩ | ⟨-, -, hr, -⟩ | ⟨-, hp, -, -⟩ | ⟨i1, -, -, ⟨c1, hc1, h11, h12⟩, -⟩
          · exfalso
            have he := cfp_eq D hS layer hLayer J hG h hcC hBC.1.symm
            obtain ⟨-, i, hi⟩ := hBC
            rw [he] at hi
            have := congrArg List.length hi
            simp at this
          · exfalso
            rw [haddr] at hr
            simp only [addrExt] at hr
            have h2 := (List.append_eq_nil_iff.mp hr).2
            have h3 := congrArg List.length h2
            rw [List.length_dropLast] at h3
            simp at h3
            omega
          · exact hp
          · exfalso
            have he := cfp_eq D hS layer hLayer J hG hc1 hcC (by rw [← h11]; exact hBC.1.symm)
            obtain ⟨-, i, hi⟩ := hBC
            rw [← he, h12] at hi
            have := congrArg List.length hi
            simp at this
        · have hl := chain_lonePath_length (D.tree π)
          have hne : (D.tree π).lonePath.length ≠ 0 := fun h => h0 (List.length_eq_zero_iff.mp h)
          omega
      · exact Or.inl ⟨b, π, hπb, rfl, rfl⟩
    · rcases parent_of_native D hS hBC with hsl | ⟨b, i, hBb, hT⟩
      · exact Or.inr (Or.inr (Or.inl ⟨q, hq, hsl, slotOf_subforestBranch D hS q c⟩))
      · rcases hab b i hBb hT with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)

/-- **(d) Roots pinned at their upper time `t`** (`s ≠ t`): the pattern is `dRoot`, the root is not a capped flower
parent, and it is the top of the native object attached at the skeleton root (the core of a skeleton root with
trivial chain, the top of its non-trivial chain, or a root of a native couple). -/
theorem rootPin_classification (hst : s ≠ t) (r : GBranch (D.forest hS))
    (h : fixCap (layeredReconstruction D hS layer hLayer) J pat t s r = some t) :
    pat r.1.1 = FixPat.dRoot ∧ r.1.2 = [] ∧ ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J r ∧
      AttachedTop D hS (GNode.root S.tree r.1.1) r := by
  rcases fixCap_cases h with ⟨-, hv⟩ | ⟨hc, hp, h0, -⟩ | ⟨-, -, -, hv⟩ | ⟨i, -, -, -, hv⟩
  · exact absurd hv.symm hst
  · refine ⟨hp, h0, hc, attachedTop_of_eq D hS _ r ?_⟩
    rw [attachedNode_root]
    exact Subtype.ext (Prod.ext rfl h0)
  · exact absurd hv.symm hst
  · exact absurd hv.symm hst

end WaveTurbulence.Flower.MkSlotsB
