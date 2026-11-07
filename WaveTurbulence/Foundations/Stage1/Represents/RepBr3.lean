/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepBr2
public import WaveTurbulence.Foundations.Molecule.LFTwist.LeafLayers
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeCoupleBranches
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeCoupleLayering
public import WaveTurbulence.Foundations.RegStruct.DecodedCouple
import Mathlib.Tactic

/-!
# S2 REPRESENTS: native couple slots, basic bridging facts
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem couple_decodes (p' : SourcePair S) :
    (D.couple p').Decodes (nativeCoupleLayered D hS layer hLayer p').garden := by
  rw [nativeCoupleLayered_garden]
  exact decodedCouple_decodes _

theorem couple_layer_le (p : ℕ) (hp : ∀ ν, layer ν ≤ p) (p' : SourcePair S)
    (a : GNode (nativeCoupleLayered D hS layer hLayer p').garden.tree) :
    (nativeCoupleLayered D hS layer hLayer p').layer a ≤ p := hp _

theorem couple_root_node (p' : SourcePair S) (j : Fin 2) :
    ((nativeCoupleForest D hS p').nodeEmbedding
        (GNode.root (nativeCoupleForest D hS p').shape j)).1 =
      inflatedPosition S D.tree (if j = 0 then (p'.firstLeaf hS).toNode else (p'.secondLeaf hS).toNode) := by
  fin_cases j
  · show ((inflatedPosition S D.tree (p'.firstLeaf hS).toNode).1,
        (inflatedPosition S D.tree (p'.firstLeaf hS).toNode).2 ++ []) = _
    simp
  · show ((inflatedPosition S D.tree (p'.secondLeaf hS).toNode).1,
        (inflatedPosition S D.tree (p'.secondLeaf hS).toNode).2 ++ []) = _
    simp

theorem couple_root_layer_le (p : ℕ) (hp : ∀ ν, layer ν ≤ p) (p' : SourcePair S) (j : Fin 2) :
    (nativeCoupleLayered D hS layer hLayer p').layer
        (GNode.root (nativeCoupleLayered D hS layer hLayer p').garden.tree j) ≤
      clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inl p') j) := by
  set ν : GNode S.tree := if j = 0 then (p'.firstLeaf hS).toNode else (p'.secondLeaf hS).toNode with hν
  have hcl : argSrc hS (.inl p') j = clkOfNode S ν := by
    fin_cases j <;> simp [argSrc, hν]
  rw [hcl]
  let E := nativeCoupleForest D hS p'
  let ν' : GNode (layeredReconstruction D hS layer hLayer).garden.tree :=
    E.nodeEmbedding (GNode.root E.shape j)
  have h1 : (nativeCoupleLayered D hS layer hLayer p').layer
      (GNode.root (nativeCoupleLayered D hS layer hLayer p').garden.tree j) =
      (layeredReconstruction D hS layer hLayer).layer ν' := rfl
  rw [h1]
  refine le_trans (LFTwist.layer_le_parentLayer (layeredReconstruction D hS layer hLayer)
    (p := p) (fun n => hp _) ν') ?_
  exact le_of_eq (parentLayer_inflated D hS layer hLayer p ν ν' (couple_root_node D hS p' j))

end WaveTurbulence.Represents
