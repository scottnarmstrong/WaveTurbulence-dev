/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.RawReduction

/-! # Skeleton reduction with the native kernels (node profiles, skeleton-level restriction)

REGRED `KernelNativeReduction` for a node profile `A`, with the skeleton-level decoration restriction
`selSk`.  The coupling power and `ζ` of the reconstructed garden split exactly into the skeleton's and the
native parts (`kernelPrefactor_reconstruction`), and each native `∑' ρ ∫` becomes the native kernel. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRedLeaf
open TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed

open scoped Classical in
/-- The decoration-restricted sum of the reconstructed garden, with the native kernels. -/
theorem kernelNode_native_reduction_sel {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀+latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) :
    (coupling d L γ δ : ℂ)^(D.garden hS).order * (D.garden hS).zeta *
      (∑' κ : GenDecoration (D.garden hS) d n nfl,
        if selSk (collapseGenDecoration D hS κ) then
          ∫ τ, kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ τ
        else 0) =
      (coupling d L γ δ : ℂ)^S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then
          ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
            ∏ s : ReplacementSlot S, nativeKernelValueN D hS L γ δ A layer hLayer tt k₀ κ.1 τ s
        else 0 := by
  let P := ∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s
  have hp : (coupling d L γ δ : ℂ)^(D.garden hS).order * (D.garden hS).zeta =
      ((coupling d L γ δ : ℂ)^S.order * S.zeta) * P := by
    change _ = ((coupling d L γ δ : ℂ)^S.order * S.zeta) *
      (∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s)
    rw [Fintype.prod_sum_type]
    exact (kernelPrefactor_reconstruction D hS layer hLayer (coupling d L γ δ)).trans (mul_assoc _ _ _)
  rw [tsum_integral_sel_reduction D hS L γ δ A layer hLayer tt k₀ n nfl hA selSk, hp, mul_assoc]
  apply congrArg (fun z => ((coupling d L γ δ : ℂ)^S.order * S.zeta) * z)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro κ
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro τ
    have hv := nativeKernelValue_prod_eqN D hS L γ δ A layer hLayer tt k₀ κ.1 τ
    exact (mul_left_comm P (coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ) _).trans
      (congrArg (fun z => coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ * z) hv).symm
  · simp only [hκ, ite_false, mul_zero]

end WaveTurbulence.RegRedLeaf
