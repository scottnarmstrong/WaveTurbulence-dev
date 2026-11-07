/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.NativeReduction
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentApp
public import WaveTurbulence.Foundations.Spine.Stage1Interface

/-! # Leafwise skeleton reduction (REGRED-LEAF, RULINGS R24 D4)

`KG_skeleton_reduction_leaves`: TARGET (redkg) (regred, L1724–1730) for the leaf-modified kernel
`kernelLeaves` (TARGET L2065–2067, RULINGS R9(a)).  The reconstructed garden `𝒢` is the skeleton `𝒢_sk`
with every leaf pair replaced by a regular couple and every branching node by a regular tree.  A leaf
profile `H` of `𝒢` (indexed by raw addresses) is pulled back along the native embeddings to leaf profiles
`nativeCoupleProfiles` / `nativeChainProfiles` of the regular parts; the native kernels of (redkg) are then
`coupleLeaves` (`K*_𝒬`) and `treeLeaves` (`K*_𝒯`) with those profiles.  The decoration restriction `selSk` is a
predicate on skeleton decorations (the SG/LG/ZG factor `Z`, TARGET L1950), pulled back to full decorations
along `collapseGenDecoration`. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.RegRedLeaf
open TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.LGSpine

/-- The leaf profile of the regular couple `𝒬_p`: `H` at the embedded address. -/
noncomputable def nativeCoupleProfiles {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (H : LeafProfiles w d) (p : SourcePair S) : LeafProfiles 2 d :=
  fun a => if h : a.2 ∈ ((nativeCoupleGarden D hS p).tree a.1).nodes then
    H ((nativeCoupleForest D hS p).nodeEmbedding ⟨a, h⟩).1 else 0

/-- The leaf profile of the regular tree `𝒯_b`: `H` at the embedded address. -/
noncomputable def nativeChainProfiles {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (H : LeafProfiles w d) (b : GBranch S.tree) : LeafProfiles 1 d :=
  fun a => if h : a.2 ∈ ((decodedTree (D.tree b) (nodeSign S.sig b.1)).tree a.1).nodes then
    H (chainContextNode D hS b ⟨a, h⟩).1 else 0

/-- The leafwise native starred kernel of one replacement slot: `K*_𝒬` (for a pair) or `K*_𝒯` (for a
branching node) with the pulled-back leaf profile. -/
noncomputable def slotLeaves {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    ReplacementSlot S → ℂ
  | .inl p => coupleLeaves L γ δ (nativeCoupleLayered D hS layer hLayer p) (nativeCoupleProfiles D hS H p)
      (parentClockWith tt τ (p.firstLeaf hS).toNode) (parentClockWith tt τ (p.secondLeaf hS).toNode)
      (cosetDecoration S L k₀ κ (p.firstLeaf hS).toNode)
  | .inr b => treeLeaves L γ δ (nativeChainLayered D hS layer hLayer b) (nativeChainProfiles D hS H b)
      (parentClockWith tt τ b.toNode) (τ b) (cosetDecoration S L k₀ κ b.toNode)

/-- Exactly the two native starred-kernel products of (redkg), leafwise. -/
noncomputable def reducedStarProductLeaves {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) : ℂ :=
  (∏ p : SourcePair S, coupleLeaves L γ δ (nativeCoupleLayered D hS layer hLayer p)
    (nativeCoupleProfiles D hS H p)
    (parentClockWith tt τ (p.firstLeaf hS).toNode) (parentClockWith tt τ (p.secondLeaf hS).toNode)
    (cosetDecoration S L k₀ κ (p.firstLeaf hS).toNode)) *
  (∏ b : GBranch S.tree, treeLeaves L γ δ (nativeChainLayered D hS layer hLayer b)
    (nativeChainProfiles D hS H b)
    (parentClockWith tt τ b.toNode) (τ b) (cosetDecoration S L k₀ κ b.toNode))

theorem coupleLeaves_nativeProfiles {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (p : SourcePair S) (t s : ℝ) (k : Mom d) :
    coupleLeaves L γ δ (nativeCoupleLayered D hS layer hLayer p) (nativeCoupleProfiles D hS H p) t s k =
      kernelNode L γ δ (nativeCoupleLayered D hS layer hLayer p)
        (fun a => (fun a' : GNode (D.forest hS) => H a'.1) ((nativeCoupleForest D hS p).nodeEmbedding a))
        (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0 := by
  unfold coupleLeaves kernelLeaves kernelNode
  congr 1
  apply tsum_congr
  intro κ
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ _
  have h : ℓ.1.2 ∈ ((nativeCoupleGarden D hS p).tree ℓ.1.1).nodes := ℓ.toNode.2
  simp only [nativeCoupleProfiles]
  simp only [h, ↓reduceDIte]
  rfl

theorem treeLeaves_nativeProfiles {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (b : GBranch S.tree) (t s : ℝ) (k : Mom d) :
    treeLeaves L γ δ (nativeChainLayered D hS layer hLayer b) (nativeChainProfiles D hS H b) t s k =
      kernelNode L γ δ (nativeChainLayered D hS layer hLayer b)
        (fun a => (fun a' : GNode (D.forest hS) => H a'.1) (chainContextNode D hS b a))
        (fun _ => t) s k (fun _ => 0) 0 := by
  unfold treeLeaves kernelLeaves kernelNode
  congr 1
  apply tsum_congr
  intro κ
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ _
  have h : ℓ.1.2 ∈ ((decodedTree (D.tree b) (nodeSign S.sig b.1)).tree ℓ.1.1).nodes :=
    ℓ.toNode.2
  simp only [nativeChainProfiles]
  simp only [h, ↓reduceDIte]
  rfl

theorem nativeKernelValueN_leaves {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (s : ReplacementSlot S) :
    nativeKernelValueN D hS L γ δ (fun a => H a.1) layer hLayer tt k₀ κ τ s =
      slotLeaves D hS L γ δ H layer hLayer tt k₀ κ τ s := by
  cases s with
  | inl p =>
    have hu : (fun q : GBranch (nativeCoupleGarden D hS p).tree => nativeCoupleUpperW D hS tt τ p q.1.1) =
        (fun q => if q.1.1 = 0 then parentClockWith tt τ (p.firstLeaf hS).toNode
          else parentClockWith tt τ (p.secondLeaf hS).toNode) := by
      have hv (j : Fin 2) : nativeCoupleUpperW D hS tt τ p j =
          if j = 0 then parentClockWith tt τ (p.firstLeaf hS).toNode
          else parentClockWith tt τ (p.secondLeaf hS).toNode := by fin_cases j <;> rfl
      exact funext (fun q => hv q.1.1)
    refine Eq.trans ?_ (coupleLeaves_nativeProfiles D hS L γ δ H layer hLayer p _ _ _).symm
    exact congrArg (fun up => kernelNode L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => (fun a' : GNode (D.forest hS) => H a'.1) ((nativeCoupleForest D hS p).nodeEmbedding a))
      up 0 (k₀+latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0) hu
  | inr b =>
    exact (treeLeaves_nativeProfiles D hS L γ δ H layer hLayer b _ _ _).symm

theorem prod_nativeKernelValueN_leaves {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    (∏ s : ReplacementSlot S, nativeKernelValueN D hS L γ δ (fun a => H a.1) layer hLayer tt k₀ κ τ s) =
      reducedStarProductLeaves D hS L γ δ H layer hLayer tt k₀ κ τ := by
  simp_rw [nativeKernelValueN_leaves]
  rw [Fintype.prod_sum_type]
  rfl

end WaveTurbulence.RegRedLeaf
