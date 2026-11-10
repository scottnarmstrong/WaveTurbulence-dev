/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.NodeKernel
public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.ClockDomains

/-! # The native regular-part kernels with a node profile (REGRED-LEAF)

REGRED `NativeKernelIntegrands` / `NativeKernelFactors`, with the layer input `F (layer ·)` replaced by
a profile `A` of the reconstructed garden's nodes.  The native couple (resp. tree) receives the pulled-back
profile `A ∘ nodeEmbedding` (resp. `A ∘ chainContextNode`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRedLeaf
open TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed

noncomputable def nativeKernelIntegrandN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s → NativeTimeBlock D s → ℂ
  | .inl p,ρ => kernelAllIntegrandN L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (k₀+latticePoint L (κ (p.firstLeaf hS).toNode)) ρ
  | .inr b,ρ => kernelAllIntegrandN L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (fun _ => parentClockWith tt τ b.toNode) (τ b) (k₀+latticePoint L (κ b.toNode)) ρ

/-- The native regular-part kernels with the pulled-back node profile. -/
noncomputable def nativeKernelValueN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    ReplacementSlot S → ℂ
  | .inl p => kernelNode L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (k₀+latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0
  | .inr b => kernelNode L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (fun _ => parentClockWith tt τ b.toNode) (τ b) (k₀+latticePoint L (κ b.toNode))
      (fun _ => 0) 0

theorem nativeKernelValueN_eq_tsum_integral {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (s : ReplacementSlot S) :
    nativeKernelValueN D hS L γ δ A layer hLayer tt k₀ κ τ s =
      nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s *
        ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀ κ τ s ρ t := by
  cases s with
  | inl p =>
    exact kernelNode_eq_tsum_integral_all L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (noFlowerParent_of_noFlower _ (nativeCouple_noFlower D hS p))
      (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (k₀+latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0
  | inr b =>
    exact kernelNode_eq_tsum_integral_all L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (noFlowerParent_of_noFlower _ (decodedTree_noFlower _ _))
      (fun _ => parentClockWith tt τ b.toNode) (τ b) (k₀+latticePoint L (κ b.toNode))
      (fun _ => 0) 0

/-- The input factor of a native replacement slot. -/
noncomputable def nativeInputFactorN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) :
    (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s → ℂ
  | .inl p,ρ => ∏ ℓ ∈ inputLeaves (nativeCoupleGarden D hS p),
      (A ((nativeCoupleForest D hS p).nodeEmbedding ℓ.toNode)
        (cosetDecoration (nativeCoupleGarden D hS p) L
          (k₀+latticePoint L (κ (p.firstLeaf hS).toNode)) ρ.1 ℓ.toNode) : ℂ)
  | .inr b,ρ => ∏ ℓ ∈ inputLeaves (decodedTree (D.tree b) (nodeSign S.sig b.1)),
      (A (chainContextNode D hS b ℓ.toNode)
        (cosetDecoration (decodedTree (D.tree b) (nodeSign S.sig b.1)) L
          (k₀+latticePoint L (κ b.toNode)) ρ.1 ℓ.toNode) : ℂ)

theorem nativeKernelIntegrandN_eq_factors {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (s : ReplacementSlot S) (ρ : NativeRelativeDecoration D hS d s) (t : NativeTimeBlock D s) :
    nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀ κ τ s ρ t =
      nativeEpsilonFactor D hS s ρ * (nativeDomainW D hS layer hLayer tt τ s).indicator
        (nativePhaseFactor D hS L γ δ k₀ κ s ρ) t * nativeInputFactorN D hS L A k₀ κ s ρ := by
  cases s <;> rfl

theorem inputProduct_relative_reconstructionN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (∏ ℓ ∈ inputLeaves (D.garden hS),
      (A ℓ.toNode (cosetDecoration (D.garden hS) L k₀ κ.1 ℓ.toNode) : ℂ)) =
      ∏ s : ReplacementSlot S, nativeInputFactorN D hS L A k₀ (collapseGenDecoration D hS κ).1 s
        (restrictRelativeDecorations D hS κ s) := by
  apply (inputProduct_reconstruction D hS (fun a =>
    (A a (cosetDecoration (D.garden hS) L k₀ κ.1 a) : ℂ))).trans
  rw [Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro p _
    apply Finset.prod_congr rfl
    intro ℓ _
    exact congrArg (fun v => (A ((nativeCoupleForest D hS p).nodeEmbedding ℓ.toNode) v : ℂ))
      (nativeCouple_coset D hS L k₀ κ p ℓ.toNode).symm
  · apply Finset.prod_congr rfl
    intro b _
    apply Finset.prod_congr rfl
    intro ℓ _
    exact congrArg (fun v => (A (chainContextNode D hS b ℓ.toNode) v : ℂ))
      (nativeChain_coset D hS L k₀ κ b ℓ.toNode).symm

/-- TARGET redkg at the literal integrand level, with node profile `A`. -/
theorem kernelAllIntegrandN_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch (D.forest hS) → ℝ) :
    kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ τ =
      coreKernelIntegrandW D hS L γ δ layer tt k₀ (collapseGenDecoration D hS κ).1 (nativeCoreClock D hS τ) *
        ∏ s : ReplacementSlot S, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀
          (collapseGenDecoration D hS κ).1 (nativeCoreClock D hS τ) s
          (restrictRelativeDecorations D hS κ s) (nativeTimeRestriction D hS τ s) := by
  classical
  let κS := collapseGenDecoration D hS κ
  let ρ := restrictRelativeDecorations D hS κ
  let τS := nativeCoreClock D hS τ
  let τN := nativeTimeRestriction D hS τ
  let E := fun s => nativeEpsilonFactor D hS s (ρ s)
  let P := fun s => nativePhaseFactor D hS L γ δ k₀ κS.1 s (ρ s) (τN s)
  let I := fun s => nativeInputFactorN D hS L A k₀ κS.1 s (ρ s)
  let Ac := τS ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt
  let B := fun s => τN s ∈ nativeDomainW D hS layer hLayer tt τS s
  let Pc := phaseProd L γ δ S (cosetDecoration S L k₀ κS.1) τS
  have hd := nativeTimeDomain_reconstructionW D hS layer hLayer tt τ
  have hm : (if τ ∈ kDomain (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) 0
      then Pc * ∏ s, P s else 0) = (if Ac then Pc else 0) * ∏ s, if B s then P s else 0 :=
    (ite_congr (propext hd) (fun _ => rfl) (fun _ => rfl)).trans (mask_mul_prod Ac B Pc P)
  simp_rw [nativeKernelIntegrandN_eq_factors]
  unfold kernelAllIntegrandN coreKernelIntegrandW
  dsimp only [layeredReconstruction]
  simp only [Set.indicator_apply]
  change (epsDec (D.garden hS) κ.1 : ℂ) *
    (if τ ∈ kDomain (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) 0 then
      phaseProd L γ δ (D.garden hS) (cosetDecoration (D.garden hS) L k₀ κ.1) τ else 0) *
      (∏ ℓ ∈ inputLeaves (D.garden hS), (A ℓ.toNode
        (cosetDecoration (D.garden hS) L k₀ κ.1 ℓ.toNode) : ℂ)) = _
  rw [epsilon_relative_reconstruction D hS κ, phaseProd_relative_reconstruction D hS L γ δ k₀ κ τ,
    inputProduct_relative_reconstructionN D hS L A k₀ κ]
  change ((epsDec S κS.1 : ℂ) * ∏ s, E s) *
    (if τ ∈ kDomain (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) 0
      then Pc * ∏ s, P s else 0) * (∏ s, I s) =
      ((epsDec S κS.1 : ℂ) * (if Ac then Pc else 0)) *
        ∏ s, E s * (if B s then P s else 0) * I s
  rw [hm, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end WaveTurbulence.RegRedLeaf
