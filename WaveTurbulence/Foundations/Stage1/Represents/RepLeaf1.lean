/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepBr8
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.InputProductFactorization
public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.Leaves
import Mathlib.Tactic

/-!
# S2 REPRESENTS: leaf profiles and leaf bounds of the native slots
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed
  WaveTurbulence.RegRedLeaf

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The leaf bounds of a native couple: the original bounds at the embedded leaves. -/
noncomputable def nativeCoupleB (B : (Fin w × TTree.Path) → NNReal) (p' : SourcePair S) :
    (Fin 2 × TTree.Path) → NNReal :=
  fun a => if h : a.2 ∈ ((nativeCoupleGarden D hS p').tree a.1).nodes then
    B ((nativeCoupleForest D hS p').nodeEmbedding ⟨a, h⟩).1 else 0

/-- The leaf bounds of a native tree. -/
noncomputable def nativeChainB (B : (Fin w × TTree.Path) → NNReal) (b : GBranch S.tree) :
    (Fin 1 × TTree.Path) → NNReal :=
  fun a => if h : a.2 ∈ ((decodedTree (D.tree b) (nodeSign S.sig b.1)).tree a.1).nodes then
    B (chainContextNode D hS b ⟨a, h⟩).1 else 0

variable (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem couple_controlled (H : LeafProfiles w d) (B : (Fin w × TTree.Path) → NNReal)
    (hctrl : LeafwiseControlled (layeredReconstruction D hS layer hLayer) H B) (p' : SourcePair S) :
    LeafwiseControlled (nativeCoupleLayered D hS layer hLayer p') (nativeCoupleProfiles D hS H p')
      (nativeCoupleB D hS B p') := by
  intro ℓ hℓ
  have h1 := hctrl _ ((mem_inputLeaves_couple D hS p' ℓ).2 hℓ)
  have hn : ℓ.1.2 ∈ ((nativeCoupleGarden D hS p').tree ℓ.1.1).nodes := ℓ.toNode.2
  simp only [nativeCoupleProfiles, nativeCoupleB, hn, ↓reduceDIte]
  exact h1

theorem chain_controlled (H : LeafProfiles w d) (B : (Fin w × TTree.Path) → NNReal)
    (hctrl : LeafwiseControlled (layeredReconstruction D hS layer hLayer) H B) (b : GBranch S.tree) :
    LeafwiseControlled (nativeChainLayered D hS layer hLayer b) (nativeChainProfiles D hS H b)
      (nativeChainB D hS B b) := by
  classical
  intro ℓ hℓ
  have hne : ℓ.1.2 ≠ (D.tree b).lonePath := fun h => not_mem_inputLeaves_chain_lone D b ℓ h hℓ
  have h1 := hctrl _ ((mem_inputLeaves_chain D hS b ⟨ℓ, hne⟩).2 hℓ)
  have hn : ℓ.1.2 ∈ ((decodedTree (D.tree b) (nodeSign S.sig b.1)).tree ℓ.1.1).nodes := ℓ.toNode.2
  simp only [nativeChainProfiles, nativeChainB, hn, ↓reduceDIte]
  have e : (chainContextLeaf D hS b ⟨ℓ, hne⟩).1 = (chainContextNode D hS b ℓ.toNode).1 :=
    congrArg Subtype.val (chainContextLeaf_toNode D hS b ⟨ℓ, hne⟩)
  rw [e] at h1
  exact h1

/-- The leaf cost of each replacement slot. -/
noncomputable def slotLeaf (B : (Fin w × TTree.Path) → NNReal) : ReplacementSlot S → ℝ
  | .inl p' => leafSizeProduct (nativeCoupleLayered D hS layer hLayer p') (nativeCoupleB D hS B p')
  | .inr b => leafSizeProduct (nativeChainLayered D hS layer hLayer b) (nativeChainB D hS B b)

theorem prod_slotLeaf (B : (Fin w × TTree.Path) → NNReal) :
    ∏ s, slotLeaf D hS layer hLayer B s = leafSizeProduct (layeredReconstruction D hS layer hLayer) B := by
  classical
  have h := inputProduct_reconstruction D hS (M := ℝ) (fun ν => (B ν.1 : ℝ))
  rw [Fintype.prod_sum_type]
  unfold leafSizeProduct
  have e0 : ∏ ℓ ∈ inputLeaves (layeredReconstruction D hS layer hLayer).garden, (B ℓ.1 : ℝ) =
      ∏ ℓ ∈ inputLeaves (D.garden hS), (B ℓ.toNode.1 : ℝ) := rfl
  rw [e0, h]
  congr 1
  · refine Finset.prod_congr rfl fun p' _ => ?_
    unfold slotLeaf leafSizeProduct
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    have hn : ℓ.1.2 ∈ ((nativeCoupleGarden D hS p').tree ℓ.1.1).nodes := ℓ.toNode.2
    simp only [nativeCoupleB, hn, ↓reduceDIte]
    rfl
  · refine Finset.prod_congr rfl fun b _ => ?_
    unfold slotLeaf leafSizeProduct
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    have hn : ℓ.1.2 ∈ ((decodedTree (D.tree b) (nodeSign S.sig b.1)).tree ℓ.1.1).nodes := ℓ.toNode.2
    simp only [nativeChainB, hn, ↓reduceDIte]
    rfl

end WaveTurbulence.Represents
