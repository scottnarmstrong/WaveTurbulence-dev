/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.NativeNode

/-! # Native lattice absolute convergence for node profiles (REGRED-LEAF)

REGRED `NativeInputSummability` for a node profile `A`: summability of `|A ℓ (k₀ + n/L)|` at the input
leaves of the full garden gives summability of every native kernel sum, including the shifted
attachment coset. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRedLeaf
open TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed

theorem nativeCouple_input_summableN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ))
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀+latticePoint L n)|)
    (p : SourcePair S) (ℓ : GLeaf (nativeCoupleGarden D hS p).tree)
    (hℓ : ℓ ∈ inputLeaves (nativeCoupleGarden D hS p)) :
    Summable (fun n : Fin d → ℤ => |A ((nativeCoupleForest D hS p).nodeEmbedding ℓ.toNode)
      ((k₀+latticePoint L (κ (p.firstLeaf hS).toNode))+latticePoint L n)|) := by
  let E := nativeCoupleForest D hS p
  have hs := hA (E.leafEmbedding ℓ) ((mem_inputLeaves_couple D hS p ℓ).mpr hℓ)
  have he := congrArg (fun a : GNode (D.forest hS) =>
    Summable (fun n : Fin d → ℤ => |A a (k₀+latticePoint L n)|)) (subforest_node_leaf E ℓ)
  exact summable_lattice_translate L k₀ (κ (p.firstLeaf hS).toNode)
    (A (E.nodeEmbedding ℓ.toNode)) (he.mpr hs)

theorem nativeChain_input_summableN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ))
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀+latticePoint L n)|)
    (b : GBranch S.tree) (ℓ : GLeaf (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree)
    (hℓ : ℓ ∈ inputLeaves (decodedTree (D.tree b) (nodeSign S.sig b.1))) :
    Summable (fun n : Fin d → ℤ => |A (chainContextNode D hS b ℓ.toNode)
      ((k₀+latticePoint L (κ b.toNode))+latticePoint L n)|) := by
  have hne : ℓ.1.2 ≠ (D.tree b).lonePath := fun he => not_mem_inputLeaves_chain_lone D b ℓ he hℓ
  let q : ChainInternalLeaf D b := ⟨ℓ,hne⟩
  have hs := hA (chainContextLeaf D hS b q) ((mem_inputLeaves_chain D hS b q).mpr hℓ)
  have he := congrArg (fun a : GNode (D.forest hS) =>
    Summable (fun n : Fin d → ℤ => |A a (k₀+latticePoint L n)|)) (chainContextLeaf_toNode D hS b q)
  exact summable_lattice_translate L k₀ (κ b.toNode) (A (chainContextNode D hS b ℓ.toNode)) (he.mp hs)

/-- Every native starred-kernel sum converges from the full-garden source input hypothesis. -/
theorem summable_nativeKernelIntegralN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀+latticePoint L n)|)
    (s : ReplacementSlot S) :
    Summable (fun ρ : NativeRelativeDecoration D hS d s =>
      ∫ t, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀ κ τ s ρ t) := by
  cases s with
  | inl p =>
    have hp : (nativeCoupleLayered D hS layer hLayer p).garden.IsPlain :=
      Comb.RootedSubforest.inducedGarden_plain (G := D.garden hS) (nativeCoupleForest D hS p)
        (nativeCoupleForest_closed D hS p)
    exact summable_integral_kernelAllIntegrandN L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (noFlowerParent_of_noFlower _ (nativeCouple_noFlower D hS p))
      (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (k₀+latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0
      (lone_count_le_one_of_plain _ hp) (nativeCouple_input_summableN D hS L A k₀ κ hA p)
  | inr b =>
    exact summable_integral_kernelAllIntegrandN L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (noFlowerParent_of_noFlower _ (decodedTree_noFlower _ _))
      (fun _ => parentClockWith tt τ b.toNode) (τ b) (k₀+latticePoint L (κ b.toNode))
      (fun _ => 0) 0
      (card_lone_le_one (fun _ _ h h' => (decodedTree_isPairedTree _ _).eq_of_isLone h h'))
      (nativeChain_input_summableN D hS L A k₀ κ hA b)

end WaveTurbulence.RegRedLeaf
