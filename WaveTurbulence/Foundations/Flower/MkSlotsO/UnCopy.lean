/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.Split
public import WaveTurbulence.Foundations.Flower.MkSlotsG.Weight
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapT
public import WaveTurbulence.Foundations.Flower.MkSlots.IntGeo
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainHoleReplacement
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementBranches
public import WaveTurbulence.Foundations.RegStruct.ChainSubtreeFrames
public import WaveTurbulence.Foundations.RegStruct.ChainNodeBounds

/-! # B3s-HELPER8 / UNPIN (part 0): small facts on the per-node factor of `genΘs` (copied by source)

Copied by source from HELPER7's `MkSlotsI/RSlotKer.lean` (`genNode`), `MkSlotsI/StemW1.lean` (`omegaAt_of_branch`,
`genNW_toNode`, `chain_branch_of_branch`) and `MkSlotsI/RSlotCpl.lean` (`cpl_not_core`, `onCapStem_emb_iff`), see
`COPIED-SHA256SUMS` (those modules are being reorganised; the copies keep this packet independent of them):

* `unNode`: the per-node factor of `genΘs` at a node of the reconstruction (`1` at a core node, `genNW` else);
* `un_omegaAt_of_branch`, `un_genNW_toNode`, `un_chain_branch_of_branch`, `un_cpl_not_core`,
  `un_onCapStem_emb_iff`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlotsI
open WaveTurbulence.Flower.MkSlots.IntCapT

namespace WaveTurbulence.Flower.MkSlotsO

variable {w d : ℕ}

/-- The resonance value at a branch. -/
theorem un_omegaAt_of_branch {w' : ℕ} {G : Garden w'} (k : GNode G.tree → Mom d) (z : GNode G.tree)
    (h : z.1.2 ∈ (G.tree z.1.1).branching) : MkSlotsS.omegaAt k z = omegaNode G k ⟨z.1, h⟩ := by
  unfold MkSlotsS.omegaAt
  rw [dite_eq_left h]

/-- The stem node weight at a branch (unfolded). -/
theorem un_genNW_toNode (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (b : GBranch LG.garden.tree) (x : ℝ) :
    genNW LG J L σ kSel Rs b.toNode x =
      if ∃ j, b ∈ stemSetCap LG J j then
        (MkSlotsT.radProd (MkSlotsG.radRaw LG J L σ kSel Rs b) x : ℂ) *
          (if b ∈ selSetCap LG J kSel then ((chiD (|x| / Rs b.1.1) : ℝ) : ℂ) else 1)
      else 1 := by
  have hb : (b.toNode).1.2 ∈ (LG.garden.tree (b.toNode).1.1).branching := b.2
  have he : (⟨(b.toNode).1, hb⟩ : GBranch LG.garden.tree) = b := rfl
  unfold genNW
  rw [dite_eq_left hb, he]
  split_ifs <;> first | rfl | contradiction

section Recon

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

/-- The per-node factor of `genΘs` at a node of the reconstruction: `1` at a core node, the stem node weight
elsewhere (HELPER7's `genNode`). -/
def unNode (z : GNode (D.forest hS)) (v : ℝ) : ℂ :=
  if ∃ β : GBranch S.tree, z = (D.coreBranch hS β).toNode then 1
  else genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs z v

/-- A non-lone native chain node whose context node is a branch is a native branch. -/
theorem un_chain_branch_of_branch (b : GBranch S.tree)
    (a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree)
    (h : (chainContextNode D hS b a).1.2 ∈ ((D.forest hS) (chainContextNode D hS b a).1.1).branching)
    (hnc : chainContextNode D hS b a ≠ (D.coreBranch hS b).toNode) :
    a.1.2 ∈ ((decodedTree (D.tree b) (nodeSign S.sig b.1)).tree a.1.1).branching := by
  have hs := (D.forest_subtree_position hS b.toNode).trans (congrArg some (D.inflateNode_branch hS b))
  have h1 := (Comb.subtree_branching_iff hs a.1.2).mpr h
  have he := branching_replaceAt_eq (plug_subtree_lonePath (D.tree b) (nodeSign S.sig b.1) .leaf)
    (node3 fun i => D.inflateNode hS (b.child i))
  rw [replaceAt_plug_lonePath] at he
  rw [he] at h1
  rcases Finset.mem_union.mp h1 with h2 | h2
  · exact (Finset.mem_filter.mp h2).1
  · exfalso
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp h2
    have hlp : (D.tree b).lonePath = a.1.2 :=
      leaf_prefix_node_eq (chain_lone_mem_leaves (D.tree b) (nodeSign S.sig b.1)) a.2 ⟨r, hr⟩
    apply hnc
    rw [← chainContextNode_lone D hS b]
    congr 1
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) hlp.symm

/-- A native couple node is never a core node. -/
theorem un_cpl_not_core (q : SourcePair S) (a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree)
    (β : GBranch S.tree) : (nativeCoupleForest D hS q).nodeEmbedding a ≠ (D.coreBranch hS β).toNode := by
  intro h
  have h2 : nativeNodeMap D hS ⟨.inl q, a⟩ =
      nativeNodeMap D hS ⟨.inr β, (chainLoneLeaf (D.tree β) (nodeSign S.sig β.1)).toNode⟩ :=
    h.trans (chainContextNode_lone D hS β).symm
  have h3 := congrArg Sigma.fst (nativeNodeMap_injective D hS h2)
  exact Sum.inl_ne_inr h3

end Recon

/-- A node of a rooted couple is on the capped stem iff a capped flower of the couple lies below it. -/
theorem un_onCapStem_emb_iff (LG : LayeredGarden w) (E : Comb.RootedSubforest LG.garden.tree 2)
    (hc : LG.garden.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (J : Finset (Fin w))
    (a : GNode (rootedLayeredGarden LG E hc).garden.tree) :
    OnCapStem LG J (capT_emb LG E hc a) →
      ∃ l : GLeaf (rootedLayeredGarden LG E hc).garden.tree,
        capT_IsFl (rootedLayeredGarden LG E hc) (fun c => (E.root c).1.1) J l ∧ l.1.1 = a.1.1 ∧
          a.1.2 <+: l.1.2 := by
  rintro ⟨ℓ, hℓ, h1, r, h2⟩
  have h1' : ℓ.1.1 = (E.root a.1.1).1.1 := h1.symm
  have h2' : ((E.root a.1.1).1.2 ++ a.1.2) ++ r = ℓ.1.2 := h2
  have hv : ℓ.1 = ((E.root a.1.1).1.1, (E.root a.1.1).1.2 ++ (a.1.2 ++ r)) := by
    refine Prod.ext h1' ?_
    rw [← h2']
    exact List.append_assoc _ _ _
  have hl : a.1.2 ++ r ∈ (E.shape a.1.1).leaves := by
    rw [Comb.subtree_leaves_iff (E.subtree_eq a.1.1)]
    have h := ℓ.2
    rw [hv] at h
    exact h
  have hle : capT_lemb LG E hc ⟨(a.1.1, a.1.2 ++ r), hl⟩ = ℓ := Subtype.ext hv.symm
  refine ⟨⟨(a.1.1, a.1.2 ++ r), hl⟩, ?_, rfl, List.prefix_append _ _⟩
  refine (capT_isCapFlower_iff LG E hc J _ (fun _ => rfl) _).mp ?_
  rw [hle]
  exact hℓ

end WaveTurbulence.Flower.MkSlotsO
