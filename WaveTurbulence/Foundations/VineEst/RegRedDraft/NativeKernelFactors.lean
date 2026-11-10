/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeKernelIntegrands
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.PhaseFactorization
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.InputProductFactorization
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.PhysicalDecorations

/-! # Literal factors of the actual native starred-kernel integrands -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def nativePhaseFactor {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) :
    (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s → NativeTimeBlock D s → ℂ
  | .inl p,ρ => phaseProd L γ δ (nativeCoupleGarden D hS p)
      (cosetDecoration (nativeCoupleGarden D hS p) L (k₀+latticePoint L (κ (p.firstLeaf hS).toNode)) ρ.1)
  | .inr b,ρ => phaseProd L γ δ (decodedTree (D.tree b) (nodeSign S.sig b.1))
      (cosetDecoration (decodedTree (D.tree b) (nodeSign S.sig b.1)) L (k₀+latticePoint L (κ b.toNode)) ρ.1)

noncomputable def nativeEpsilonFactor {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s → ℂ
  | .inl p,ρ => (epsDec (nativeCoupleGarden D hS p) ρ.1 : ℂ)
  | .inr b,ρ => (epsDec (decodedTree (D.tree b) (nodeSign S.sig b.1)) ρ.1 : ℂ)

noncomputable def nativeDomain {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (τ : GBranch S.tree → ℝ) : (s : ReplacementSlot S) → Set (NativeTimeBlock D s)
  | .inl p => kDomain (nativeCoupleLayered D hS layer hLayer p)
      (fun q => nativeCoupleUpper D hS top τ p q.1.1) 0
  | .inr b => kDomain (nativeChainLayered D hS layer hLayer b)
      (fun _ => parentClock top τ b.toNode) (τ b)

end WaveTurbulence.RegRed
