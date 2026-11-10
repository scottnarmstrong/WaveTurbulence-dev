/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeKernelFactors

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

end WaveTurbulence.RegRed
