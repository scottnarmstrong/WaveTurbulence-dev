/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.ReducedLatticeFubini
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.FiniteIndependentSums

/-! # Native decoration sums become the products of actual starred-kernel sums -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

theorem tsum_reduced_fixed_skeleton {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl) (τ : GBranch S.tree → ℝ)
    (hF : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |F (layer ℓ.toNode) (k₀+latticePoint L n)|) :
    (∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ (glueGenDecoration D hS κ ρ) τ) =
      coreKernelIntegrand D hS L γ δ layer top k₀ κ.1 τ *
        ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀ κ.1 τ s ρ t := by
  have (s : ReplacementSlot S) : Countable (NativeRelativeDecoration D hS d s) := by
    cases s <;> dsimp only [NativeRelativeDecoration] <;> unfold GenDecoration <;> infer_instance
  let f := fun s (ρ : NativeRelativeDecoration D hS d s) =>
    ∫ t, nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀ κ.1 τ s ρ t
  have hf (s : ReplacementSlot S) : Summable (f s) :=
    summable_nativeKernelIntegral D hS L γ δ F layer hLayer top k₀ κ.1 τ hF s
  apply (tsum_congr (fun ρ => reducedDecorationIntegrand_glue D hS L γ δ F layer hLayer top k₀ κ ρ τ)).trans
  rw [tsum_mul_left]
  exact congrArg (fun z => coreKernelIntegrand D hS L γ δ layer top k₀ κ.1 τ * z)
    (tsum_pi_prod_complex f hf)

theorem nativeKernelValue_prod_eq {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    (∏ s : ReplacementSlot S, nativeKernelValue D hS L γ δ F layer hLayer top k₀ κ τ s) =
      (∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s) *
        ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀ κ τ s ρ t := by
  simp_rw [nativeKernelValue_eq_tsum_integral]
  exact Finset.prod_mul_distrib

end WaveTurbulence.RegRed
