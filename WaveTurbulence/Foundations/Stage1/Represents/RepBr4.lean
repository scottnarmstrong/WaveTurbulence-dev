/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepBr3
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeChainLayering
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeKernelIntegrands
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CenteredDecorations
public import WaveTurbulence.Foundations.RegStruct.DecodedTreeProperties
import Mathlib.Tactic

/-!
# S2 REPRESENTS: native tree slots, basic bridging facts
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem tree_decodes (b : GBranch S.tree) :
    (D.tree b).DecodesTree (nativeChainLayered D hS layer hLayer b).garden :=
  decodedTree_decodes _ _

theorem tree_noFlower (b : GBranch S.tree) :
    ∀ b', ¬ (nativeChainLayered D hS layer hLayer b).garden.IsFlowerParent b' :=
  noFlowerParent_of_noFlower _ (decodedTree_noFlower _ _)

theorem tree_lone_card (b : GBranch S.tree) (j : Fin 1) :
    (Finset.univ.filter fun ℓ : GLeaf (nativeChainLayered D hS layer hLayer b).garden.tree =>
      ℓ.1.1 = j ∧ (nativeChainLayered D hS layer hLayer b).garden.IsLone ℓ).card ≤ 1 :=
  card_lone_le_one (fun _ _ h h' => (decodedTree_isPairedTree _ _).eq_of_isLone h h') j

theorem tree_root_node (b : GBranch S.tree) :
    (chainContextNode D hS b (GNode.root (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree 0)).1 =
      inflatedPosition S D.tree b.toNode := by
  show addrExt (inflatedPosition S D.tree b.toNode) [] = _
  simp [addrExt]

theorem tree_root_layer_le (p : ℕ) (hp : ∀ ν, layer ν ≤ p) (b : GBranch S.tree) :
    (nativeChainLayered D hS layer hLayer b).layer
        (GNode.root (nativeChainLayered D hS layer hLayer b).garden.tree 0) ≤
      clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr b) 0) := by
  have hcl : argSrc hS (.inr b) 0 = clkOfNode S b.toNode := by simp [argSrc]
  rw [hcl]
  let ν' : GNode (layeredReconstruction D hS layer hLayer).garden.tree :=
    chainContextNode D hS b (GNode.root (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree 0)
  have h1 : (nativeChainLayered D hS layer hLayer b).layer
      (GNode.root (nativeChainLayered D hS layer hLayer b).garden.tree 0) =
      (layeredReconstruction D hS layer hLayer).layer ν' := rfl
  rw [h1]
  refine le_trans (LFTwist.layer_le_parentLayer (layeredReconstruction D hS layer hLayer)
    (p := p) (fun n => hp _) ν') ?_
  exact le_of_eq (parentLayer_inflated D hS layer hLayer p b.toNode ν' (tree_root_node D hS b))

theorem tree_lone_layer (b : GBranch S.tree)
    (a : GNode (nativeChainLayered D hS layer hLayer b).garden.tree) (ha : a.1.2 = (D.tree b).lonePath) :
    (nativeChainLayered D hS layer hLayer b).layer a = layer (D.coreBranch hS b).toNode := by
  show layer (chainContextNode D hS b a) = layer (D.coreBranch hS b).toNode
  congr 1
  apply Subtype.ext
  show addrExt (inflatedPosition S D.tree b.toNode) a.1.2 = D.corePosition b
  rw [ha]
  rfl

end WaveTurbulence.Represents
