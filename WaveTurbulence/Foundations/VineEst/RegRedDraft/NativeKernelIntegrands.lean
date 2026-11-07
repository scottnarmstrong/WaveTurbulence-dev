/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeTimeCoordinates
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.AllTimeKernel
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CosetCentering

/-! # The actual native KQstar/KTstar integrands in skeleton coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

theorem noFlowerParent_of_noFlower {w : ℕ} (G : Garden w) (hf : ∀ ℓ, ¬ G.IsFlower ℓ)
    (b : GBranch G.tree) : ¬ G.IsFlowerParent b := by
  rintro ⟨ℓ,hℓ,_⟩
  exact hf ℓ hℓ

noncomputable def nativeKernelIntegrand {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s → NativeTimeBlock D s → ℂ
  | .inl p,ρ => kernelAllIntegrand L γ δ F (nativeCoupleLayered D hS layer hLayer p)
      (fun q => nativeCoupleUpper D hS top τ p q.1.1) 0
      (k₀+latticePoint L (κ (p.firstLeaf hS).toNode)) ρ
  | .inr b,ρ => kernelAllIntegrand L γ δ F (nativeChainLayered D hS layer hLayer b)
      (fun _ => parentClock top τ b.toNode) (τ b) (k₀+latticePoint L (κ b.toNode)) ρ

theorem integrable_nativeKernelIntegrand {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (s : ReplacementSlot S) (ρ : NativeRelativeDecoration D hS d s) :
    Integrable (nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀ κ τ s ρ) := by
  cases s with
  | inl p =>
    exact integrable_kernelAllIntegrand L γ δ F (nativeCoupleLayered D hS layer hLayer p)
      (noFlowerParent_of_noFlower _ (nativeCouple_noFlower D hS p)) _ _ _ ρ
  | inr b =>
    exact integrable_kernelAllIntegrand L γ δ F (nativeChainLayered D hS layer hLayer b)
      (noFlowerParent_of_noFlower _ (decodedTree_noFlower _ _)) _ _ _ ρ

noncomputable def nativeKernelPrefactor {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (c : ℂ) : ReplacementSlot S → ℂ
  | .inl p => c^(nativeCoupleLayered D hS layer hLayer p).garden.order *
      (nativeCoupleLayered D hS layer hLayer p).garden.zeta
  | .inr b => c^(nativeChainLayered D hS layer hLayer b).garden.order *
      (nativeChainLayered D hS layer hLayer b).garden.zeta

noncomputable def nativeKernelValue {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    ReplacementSlot S → ℂ
  | .inl p => kernelK L γ δ F (nativeCoupleLayered D hS layer hLayer p)
      (fun q => nativeCoupleUpper D hS top τ p q.1.1) 0
      (k₀+latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0
  | .inr b => KTstar L γ δ F (nativeChainLayered D hS layer hLayer b)
      (parentClock top τ b.toNode) (τ b) (k₀+latticePoint L (κ b.toNode))

theorem nativeKernelValue_eq_tsum_integral {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (s : ReplacementSlot S) :
    nativeKernelValue D hS L γ δ F layer hLayer top k₀ κ τ s =
      nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s *
        ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀ κ τ s ρ t := by
  cases s with
  | inl p =>
    exact kernelK_eq_tsum_integral_all L γ δ F (nativeCoupleLayered D hS layer hLayer p)
      (noFlowerParent_of_noFlower _ (nativeCouple_noFlower D hS p)) _ _ _ _ _
  | inr b =>
    exact kernelK_eq_tsum_integral_all L γ δ F (nativeChainLayered D hS layer hLayer b)
      (noFlowerParent_of_noFlower _ (decodedTree_noFlower _ _)) _ _ _ _ _

/-- The first branch is literally the source regular-couple starred kernel. -/
theorem nativeKernelValue_couple_eq_KQstar {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (p : SourcePair S) :
    nativeKernelValue D hS L γ δ F layer hLayer top k₀ κ τ (.inl p) =
      KQstar L γ δ F (nativeCoupleLayered D hS layer hLayer p)
        (parentClock top τ (p.firstLeaf hS).toNode) (parentClock top τ (p.secondLeaf hS).toNode)
        (k₀+latticePoint L (κ (p.firstLeaf hS).toNode)) := by
  have hu : (fun q : GBranch (nativeCoupleGarden D hS p).tree => nativeCoupleUpper D hS top τ p q.1.1) =
      (fun q => if q.1.1 = 0 then parentClock top τ (p.firstLeaf hS).toNode
        else parentClock top τ (p.secondLeaf hS).toNode) := by
    have hv (j : Fin 2) : nativeCoupleUpper D hS top τ p j =
        if j = 0 then parentClock top τ (p.firstLeaf hS).toNode
        else parentClock top τ (p.secondLeaf hS).toNode := by fin_cases j <;> rfl
    exact funext (fun q => hv q.1.1)
  exact congrArg (fun up => kernelK L γ δ F (nativeCoupleLayered D hS layer hLayer p) up 0
    (k₀+latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0) hu

end WaveTurbulence.RegRed
