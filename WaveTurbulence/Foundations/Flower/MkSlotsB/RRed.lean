/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RNode
public import WaveTurbulence.Foundations.Flower.MkSlots.PRedRed

/-! # B3s-HELPER3: the relaxed pinned reconstruction identity (relaxed PRED, part 2)

The twin of `MkSlots.PRedRed` on RELAXED domains: the garden integrand lives on main's `kDomainFix` of the
reconstruction, the core integrand on `coreTimeDomainWR`, the native integrands on `nativeDomainWR`.

* `nativeKernelIntegrandNR` (relaxed native integrand), `coreKernelIntegrandWR`;
* **`kernelAllIntegrandD_reconstruction`**: main's `kernelAllIntegrandN_reconstruction` with the relaxed domains, for
  every `τ` on the pinned slice with free times distinct from the pins (`PinnedAt`), under `RelaxPins`; its proof is
  main's with the set identity `mem_kDomainFix_reconstruction_iff`;
* `splitIntegrandR`, **`integral_kernelAllIntegrandD_reconstruction_fix`**: the pinned time factorization (the
  pointwise identity holds `fixMeasure`-a.e., which is all the measure-preserving split needs), integrability and the
  L¹ bound of the reduced integrand. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlotsB
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.MkSlots

/-! ### The relaxed native and core integrands -/

section Native

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (fixG : GBranch (D.forest hS) → Option ℝ)

/-- The relaxed native integrand of a replacement slot (main's `nativeKernelIntegrandN` on `nativeDomainWR`). -/
def nativeKernelIntegrandNR :
    (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s → NativeTimeBlock D s → ℂ
  | .inl p, ρ => kernelAllIntegrandD L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (nativeDomainWR D hS layer hLayer tt τ fixG (.inl p)) (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) ρ
  | .inr b, ρ => kernelAllIntegrandD L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (nativeDomainWR D hS layer hLayer tt τ fixG (.inr b)) (k₀ + latticePoint L (κ b.toNode)) ρ

/-- The relaxed core integrand. -/
def coreKernelIntegrandWR (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) : ℂ :=
  (epsDec S κ : ℂ) *
    (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt (fixCore D hS fixG)).indicator
      (phaseProd L γ δ S (cosetDecoration S L k₀ κ)) τ

end Native

/-! ### The relaxed literal integrand identity -/

section Identity

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (fixG : GBranch (D.forest hS) → Option ℝ)

/-- The garden integrand on the relaxed domain of the reconstruction. -/
abbrev gardenIntegrandR {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) :
    (GBranch (D.forest hS) → ℝ) → ℂ :=
  kernelAllIntegrandD L γ δ (layeredReconstruction D hS layer hLayer) A
    (kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG) k₀ κ

/-! ### The pinned time factorization -/

/-- The reduced integrand: the core integrand times the pinned native integrals. -/
def reducedDecorationIntegrandNFR {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) : ℂ :=
  coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG (collapseGenDecoration D hS κ).1 τ *
    ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrandNR D hS L γ δ A layer hLayer tt k₀
      (collapseGenDecoration D hS κ).1 τ fixG s (restrictRelativeDecorations D hS κ s) t
        ∂(fixMeasure (fixNative D hS fixG s))

/-- The split measure of the time coordinates. -/
abbrev splitMeasure : Measure ((GBranch S.tree → ℝ) × ((s : ReplacementSlot S) → NativeTimeBlock D s)) :=
  (fixMeasure (fixCore D hS fixG)).prod (Measure.pi fun s => fixMeasure (fixNative D hS fixG s))

theorem integrable_gardenIntegrandR {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    Integrable (gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ) (fixMeasure fixG) :=
  integrable_kernelAllIntegrandD_fix L γ δ (layeredReconstruction D hS layer hLayer) A k₀
    (measurableSet_kDomainFix _ _ _) (kDomainFix_subset_unitBoxR _ _ _) κ

end Identity

end WaveTurbulence.Flower.MkSlotsB
