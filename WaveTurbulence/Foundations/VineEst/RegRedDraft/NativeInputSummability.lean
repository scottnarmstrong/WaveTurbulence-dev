/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeKernelFactors
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.AllTimeKernelNorm

/-! # Native lattice absolute convergence follows from the full source inputs -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

theorem summable_lattice_translate {d : ℕ} (L : ℝ) (k : Mom d) (v : Fin d → ℤ)
    (f : Mom d → ℝ) (hf : Summable (fun n : Fin d → ℤ => |f (k+latticePoint L n)|)) :
    Summable (fun n : Fin d → ℤ => |f ((k+latticePoint L v)+latticePoint L n)|) := by
  have hi : Function.Injective (fun n : Fin d → ℤ => v+n) := fun _ _ h => add_left_cancel h
  have hs := hf.comp_injective hi
  change Summable (fun n : Fin d → ℤ => |f (k+latticePoint L (v+n))|) at hs
  apply hs.congr
  intro n
  exact congrArg (fun z => |f z|) ((congrArg (fun z => k+z) (latticePoint_add L v n)).trans
    (add_assoc k (latticePoint L v) (latticePoint L n)).symm)

theorem nativeCouple_input_summable {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ))
    (hF : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |F (layer ℓ.toNode) (k₀+latticePoint L n)|)
    (p : SourcePair S) (ℓ : GLeaf (nativeCoupleLayered D hS layer hLayer p).garden.tree)
    (hℓ : ℓ ∈ inputLeaves (nativeCoupleLayered D hS layer hLayer p).garden) :
    Summable (fun n : Fin d → ℤ => |F ((nativeCoupleLayered D hS layer hLayer p).layer ℓ.toNode)
      ((k₀+latticePoint L (κ (p.firstLeaf hS).toNode))+latticePoint L n)|) := by
  let E := nativeCoupleForest D hS p
  have hs := hF (E.leafEmbedding ℓ) ((mem_inputLeaves_couple D hS p ℓ).mpr hℓ)
  have he := congrArg (fun a : GNode (D.forest hS) =>
    Summable (fun n : Fin d → ℤ => |F (layer a) (k₀+latticePoint L n)|)) (subforest_node_leaf E ℓ)
  exact summable_lattice_translate L k₀ (κ (p.firstLeaf hS).toNode) (F (layer (E.nodeEmbedding ℓ.toNode)))
    (he.mpr hs)

theorem nativeChain_input_summable {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ))
    (hF : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |F (layer ℓ.toNode) (k₀+latticePoint L n)|)
    (b : GBranch S.tree) (ℓ : GLeaf (nativeChainLayered D hS layer hLayer b).garden.tree)
    (hℓ : ℓ ∈ inputLeaves (nativeChainLayered D hS layer hLayer b).garden) :
    Summable (fun n : Fin d → ℤ => |F ((nativeChainLayered D hS layer hLayer b).layer ℓ.toNode)
      ((k₀+latticePoint L (κ b.toNode))+latticePoint L n)|) := by
  have hne : ℓ.1.2 ≠ (D.tree b).lonePath := fun he => not_mem_inputLeaves_chain_lone D b ℓ he hℓ
  let q : ChainInternalLeaf D b := ⟨ℓ,hne⟩
  have hs := hF (chainContextLeaf D hS b q) ((mem_inputLeaves_chain D hS b q).mpr hℓ)
  have he := congrArg (fun a : GNode (D.forest hS) =>
    Summable (fun n : Fin d → ℤ => |F (layer a) (k₀+latticePoint L n)|)) (chainContextLeaf_toNode D hS b q)
  exact summable_lattice_translate L k₀ (κ b.toNode) (F (layer (chainContextNode D hS b ℓ.toNode))) (he.mp hs)

theorem summable_integral_kernelAllIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀+latticePoint L n)|) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl => ∫ τ, kernelAllIntegrand L γ δ F LG up s k₀ κ τ) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun κ => norm_integral_le_integral_norm (kernelAllIntegrand L γ δ F LG up s k₀ κ))
    (summable_integral_norm_kernelAllIntegrand L γ δ F LG hG up s k₀ nroot nfl hlone hF)

/-- Every native starred-kernel sum converges from the actual full-garden
source input hypothesis, including the shifted attachment coset. -/
theorem summable_nativeKernelIntegral {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (hF : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |F (layer ℓ.toNode) (k₀+latticePoint L n)|)
    (s : ReplacementSlot S) :
    Summable (fun ρ : NativeRelativeDecoration D hS d s =>
      ∫ t, nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀ κ τ s ρ t) := by
  cases s with
  | inl p =>
    have hp : (nativeCoupleLayered D hS layer hLayer p).garden.IsPlain :=
      Comb.RootedSubforest.inducedGarden_plain (G := D.garden hS) (nativeCoupleForest D hS p)
        (nativeCoupleForest_closed D hS p)
    exact summable_integral_kernelAllIntegrand L γ δ F (nativeCoupleLayered D hS layer hLayer p)
      (noFlowerParent_of_noFlower _ (nativeCouple_noFlower D hS p)) _ _ _ _ _
      (lone_count_le_one_of_plain _ hp) (nativeCouple_input_summable D hS L F layer hLayer k₀ κ hF p)
  | inr b =>
    exact summable_integral_kernelAllIntegrand L γ δ F (nativeChainLayered D hS layer hLayer b)
      (noFlowerParent_of_noFlower _ (decodedTree_noFlower _ _)) _ _ _ _ _
      (card_lone_le_one (fun _ _ h h' => (decodedTree_isPairedTree _ _).eq_of_isLone h h'))
      (nativeChain_input_summable D hS L F layer hLayer k₀ κ hF b)

end WaveTurbulence.RegRed
