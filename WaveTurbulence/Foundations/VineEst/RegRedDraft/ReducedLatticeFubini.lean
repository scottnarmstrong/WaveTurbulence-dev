/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.ReducedDecorationIntegrand
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeInputSummability

/-! # Absolute Fubini for the independent native decoration fibers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

theorem summable_integral_norm_reducedDecorationIntegrand {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hF : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |F (layer ℓ.toNode) (k₀+latticePoint L n)|) :
    Summable (fun κ : GenDecoration (D.garden hS) d n nfl =>
      ∫ τ, ‖reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ κ τ‖) := by
  have hs := summable_integral_norm_kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer)
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) (fun _ => top) 0 k₀ n nfl
    (lone_count_le_one_of_plain _ (D.garden_plain hS)) hF
  exact Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (integral_norm_reducedDecorationIntegrand_le D hS L γ δ F layer hLayer top k₀) hs

theorem glueGenDecoration_injective {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl) : Function.Injective (glueGenDecoration D hS κ) := by
  intro ρ η he
  have h := congrArg (fun k : GenDecoration (D.garden hS) d n nfl => restrictRelativeDecorations D hS k) he
  exact (restrictRelativeDecorations_glue D hS κ ρ).symm.trans
    (h.trans (restrictRelativeDecorations_glue D hS κ η))

theorem reducedDecorationIntegrand_glue {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (τ : GBranch S.tree → ℝ) :
    reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ (glueGenDecoration D hS κ ρ) τ =
      coreKernelIntegrand D hS L γ δ layer top k₀ κ.1 τ *
        ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀ κ.1 τ s (ρ s) t := by
  unfold reducedDecorationIntegrand
  rw [collapseGenDecoration_glue,restrictRelativeDecorations_glue]

/-- TARGET redkg: for every genuine skeleton decoration the independent native
lattice sum may be moved through the core time integral. Its summed L1 bound is
inherited from the full source kernel by the proved coordinate equivalences. -/
theorem tsum_integral_reduced_fixed_skeleton {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl)
    (hF : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |F (layer ℓ.toNode) (k₀+latticePoint L n)|) :
    (∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      ∫ τ, reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ (glueGenDecoration D hS κ ρ) τ) =
      ∫ τ, ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ (glueGenDecoration D hS κ ρ) τ := by
  have (s : ReplacementSlot S) : Countable (NativeRelativeDecoration D hS d s) := by
    cases s <;> dsimp only [NativeRelativeDecoration] <;> unfold GenDecoration <;> infer_instance
  have hs := (summable_integral_norm_reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ n nfl hF).comp_injective
    (glueGenDecoration_injective D hS κ)
  exact (integral_tsum_of_summable_integral_norm
    (fun ρ => integrable_reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ (glueGenDecoration D hS κ ρ)) hs)

end WaveTurbulence.RegRed
