/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeSumFactorization

/-! # Analytic skeleton reduction before distributing the native kernel prefactors -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

/-- TARGET redkg, with native starred-kernel summands written as their actual
absolutely convergent lattice sums and time integrals. Every rearrangement is
derived from source input summability and the actual reconstruction maps. -/
theorem kernelK_raw_reduction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hF : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |F (layer ℓ.toNode) (k₀+latticePoint L n)|) :
    kernelK L γ δ F (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 k₀ n nfl =
      (coupling d L γ δ : ℂ)^(D.garden hS).order * (D.garden hS).zeta *
        ∑' κ : GenDecoration S d n nfl, ∫ τ : GBranch S.tree → ℝ,
          coreKernelIntegrand D hS L γ δ layer top k₀ κ.1 τ *
            ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
              ∫ t, nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀ κ.1 τ s ρ t := by
  let f : GenDecoration (D.garden hS) d n nfl → ℂ := fun κ =>
    ∫ τ, kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 k₀ κ τ
  have hs : Summable f := summable_integral_kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer)
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) _ _ _ n nfl
    (lone_count_le_one_of_plain _ (D.garden_plain hS)) hF
  have hp : Summable (fun p : GenDecoration S d n nfl ×
      ((s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) => f (glueGenDecoration D hS p.1 p.2)) :=
    hs.comp_injective (decorationFiberEquiv D hS n nfl).symm.injective
  have hsplit : (∑' κ, f κ) = ∑' κ : GenDecoration S d n nfl,
      ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s, f (glueGenDecoration D hS κ ρ) :=
    (tsum_decorationFiberEquiv D hS n nfl f).trans hp.tsum_prod
  rw [kernelK_eq_tsum_integral_all L γ δ F (layeredReconstruction D hS layer hLayer)
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS))]
  apply congrArg (fun z => (coupling d L γ δ : ℂ)^(D.garden hS).order * (D.garden hS).zeta * z)
  apply hsplit.trans
  apply tsum_congr
  intro κ
  apply Eq.trans (b := ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
    ∫ τ, reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ (glueGenDecoration D hS κ ρ) τ)
  · exact tsum_congr (fun ρ => integral_kernelAllIntegrand_reconstruction D hS L γ δ F layer hLayer top k₀
      (glueGenDecoration D hS κ ρ))
  · apply (tsum_integral_reduced_fixed_skeleton D hS L γ δ F layer hLayer top k₀ κ hF).trans
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun τ => tsum_reduced_fixed_skeleton D hS L γ δ F layer hLayer top k₀ κ τ hF))

end WaveTurbulence.RegRed
