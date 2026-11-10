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

noncomputable def nativeKernelPrefactor {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (c : ℂ) : ReplacementSlot S → ℂ
  | .inl p => c^(nativeCoupleLayered D hS layer hLayer p).garden.order *
      (nativeCoupleLayered D hS layer hLayer p).garden.zeta
  | .inr b => c^(nativeChainLayered D hS layer hLayer b).garden.order *
      (nativeChainLayered D hS layer hLayer b).garden.zeta

end WaveTurbulence.RegRed
