/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RRed

/-! # B3s-HELPER3: the relaxed weighted reduction with skeleton and slot multipliers (relaxed PRED, part 3)

The twin of the weighted part of `MkSlots.PRedRed` and of `MkSlotsW.PRedM` on relaxed domains, with the decoration
weight `(∏ z, W z (k z)) · Θ (collapse κ) · ∏ s, Θs s (k_s) (κ restricted to the native object of s)`: the node weight
`W` and the per-slot weights `Θs` split over the slots (`weight_relative_reconstruction`, `restrictRelativeDecorations`),
`Θ` is constant on the fibres of the collapse.

* `slotMom`, `nativeKernelIntegrandNWR`, `nativeKernelValueNWR` (the relaxed weighted native kernels, `Θs` inside),
  `nativeKernelValueNWR_eq_tsum_integral`, `summable_nativeKernelIntegralNWR`;
* `ΘSlots`, `reducedDecorationIntegrandNWFR`, `reducedDecorationIntegrandNWFR_glue`;
* `tsum_integral_sel_reductionNWFMR`, **`kernelNodeWR_native_reduction_selNWFMR`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlotsB
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.MkSlots

/-- The momentum of a replacement slot (the base plus the skeleton label of its slot node). -/
def slotMom {w d : ℕ} {S : Garden w} (hS : S.IsPlain) (L : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) :
    ReplacementSlot S → Mom d
  | .inl p => k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)
  | .inr b => k₀ + latticePoint L (κ b.toNode)

/-! ### The relaxed weighted native kernels -/

section Native

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Θs : (s : ReplacementSlot S) → Mom d → NativeRelativeDecoration D hS d s → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (fixG : GBranch (D.forest hS) → Option ℝ)

end Native

/-! ### The relaxed weighted reductions -/

section Reduction

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Θs : (s : ReplacementSlot S) → Mom d → NativeRelativeDecoration D hS d s → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (fixG : GBranch (D.forest hS) → Option ℝ)

/-- The product of the slot weights of a garden decoration. -/
def ΘSlots {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) : ℂ :=
  ∏ s : ReplacementSlot S, Θs s (slotMom hS L k₀ (collapseGenDecoration D hS κ).1 s)
    (restrictRelativeDecorations D hS κ s)

theorem norm_ΘSlots_le (CΘs : ℝ) (hΘs : ∀ s k ρ, ‖Θs s k ρ‖ ≤ CΘs) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    ‖ΘSlots D hS L Θs k₀ κ‖ ≤ CΘs ^ Fintype.card (ReplacementSlot S) :=
  norm_prod_le_pow_card _ CΘs fun _ => hΘs _ _ _

/-- The weighted garden integrand on the relaxed domain. -/
abbrev gardenIntegrandNWR {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) :
    (GBranch (D.forest hS) → ℝ) → ℂ :=
  kernelAllIntegrandNWD L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
    (kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG) k₀ (ΘSlots D hS L Θs k₀) κ

variable (hP : RelaxPins layer tt fixG)
include hP

omit hP in
theorem summable_integral_norm_gardenIntegrandR (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration (D.garden hS) d n nfl =>
      ∫ τ, ‖gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ τ‖ ∂(fixMeasure fixG)) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun κ => integral_norm_kernelAllIntegrandD_fix_le L γ δ (layeredReconstruction D hS layer hLayer) A k₀
      (kDomainFix_subset_unitBoxR _ _ _) κ)
    (summable_inputNodeMajorant L (layeredReconstruction D hS layer hLayer) A k₀ n nfl
      (lone_count_le_one_of_plain _ (D.garden_plain hS)) hA)

end Reduction

end WaveTurbulence.Flower.MkSlotsB
