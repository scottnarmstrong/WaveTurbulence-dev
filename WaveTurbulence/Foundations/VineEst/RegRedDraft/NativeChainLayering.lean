/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeChainNodes
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionChainBlocks

/-! # Inherited layerings of the actual regular paired-tree replacements -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem chainContext_pair_layers {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (b : GBranch S.tree)
    (x y : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree)
    (hp : (x.1,y.1) ∈ (D.tree b).pairsAt (nodeSign S.sig b.1) ((0 : Fin 1),[])) :
    layer (chainContextNode D hS b x) = layer (chainContextNode D hS b y) := by
  let a := inflatedPosition S D.tree b.toNode
  let f : (Fin 1 × Path) → (Fin w × Path) := fun z => addrExt a z.2
  have hf : RespectsAt f (0,[]) := by
    intro q
    simp only [f,addrExt,List.nil_append,List.append_nil]
  have hm := chain_pairsAt_map_local (D.tree b) f (0,[]) hf (nodeSign S.sig b.1)
  have he : f (0,[]) = a := by simp only [f,addrExt,List.append_nil]
  rw [he] at hm
  have hq : (f x.1,f y.1) ∈ (D.tree b).pairsAt (nodeSign S.sig b.1) a := by
    rw [hm]
    exact List.mem_map.mpr ⟨(x.1,y.1),hp,rfl⟩
  exact layer_eq_of_sourcePair (layeredReconstruction D hS layer hLayer)
    (chainContextNode D hS b x) (chainContextNode D hS b y)
    (D.chain_pair_mem hS (D.garden_decodes hS) b _ hq)

theorem nativeChain_isLayering {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (b : GBranch S.tree) :
    IsLayering (decodedTree (D.tree b) (nodeSign S.sig b.1))
      (fun a => layer (chainContextNode D hS b a)) := by
  constructor
  · intro q i
    have hh := hLayer.1 (chainContextBranch D hS b ⟨q.1.2,q.2⟩) i
    exact (congrArg layer (chainContextNode_child D hS b q i)).trans_le hh
  · intro ℓ
    let T := decodedTree (D.tree b) (nodeSign S.sig b.1)
    have hd := decodedTree_decodes (D.tree b) (nodeSign S.sig b.1)
    by_cases hl : ℓ.1.2 = (D.tree b).lonePath
    · have hm : T.mark ℓ ≠ none := by
        change (decodedTree (D.tree b) (nodeSign S.sig b.1)).mark ℓ ≠ none
        rw [hd.2.1 ℓ,ite_eq_left hl]
        decide
      have hp := T.pair_eq_iff ℓ |>.mpr hm
      exact congrArg (fun q : GLeaf T.tree => layer (chainContextNode D hS b q.toNode)) hp.symm
    · have hp := hd.2.2 ℓ hl
      rcases (mem_symmPairs_iff _ _).mp hp with hp | hp
      · exact chainContext_pair_layers D hS layer hLayer b ℓ.toNode (T.pair ℓ).toNode hp
      · exact (chainContext_pair_layers D hS layer hLayer b (T.pair ℓ).toNode ℓ.toNode hp).symm

/-- TARGET regred L1724: each actual regular paired-tree replacement inherits its
layering from the reconstructed garden, including its distinguished lower leaf. -/
noncomputable def nativeChainLayered {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (b : GBranch S.tree) : LayeredGarden 1 where
  garden := decodedTree (D.tree b) (nodeSign S.sig b.1)
  layer := fun a => layer (chainContextNode D hS b a)
  isLayering := nativeChain_isLayering D hS layer hLayer b

end WaveTurbulence.RegRed
