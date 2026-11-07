/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.TimeIntegral
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.FiniteIndependentSums

/-! # Reduced fixed-decoration decomposition with a node profile (REGRED-LEAF)

REGRED `ReducedDecorationIntegrand`, `ReducedLatticeFubini` and `NativeSumFactorization` for a node profile `A`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRedLeaf
open TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed


noncomputable def reducedDecorationIntegrandN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) : ℂ :=
  coreKernelIntegrandW D hS L γ δ layer tt k₀ (collapseGenDecoration D hS κ).1 τ *
    ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀
      (collapseGenDecoration D hS κ).1 τ s (restrictRelativeDecorations D hS κ s) t

theorem integral_native_section_eq_reducedN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) :
    (∫ t : (s : ReplacementSlot S) → NativeTimeBlock D s,
      kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ
        ((sourceNativeTimeSplit D hS).symm (τ,t))) =
      reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ κ τ := by
  have he : (fun t => kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A
      (fun b => tt b.1.1) 0 k₀ κ ((sourceNativeTimeSplit D hS).symm (τ,t))) =
      (fun t : (s : ReplacementSlot S) → NativeTimeBlock D s =>
        coreKernelIntegrandW D hS L γ δ layer tt k₀ (collapseGenDecoration D hS κ).1 τ *
          ∏ s, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀
            (collapseGenDecoration D hS κ).1 τ s (restrictRelativeDecorations D hS κ s) (t s)) := by
    funext t
    have h := kernelAllIntegrandN_reconstruction D hS L γ δ A layer hLayer tt k₀ κ
      ((sourceNativeTimeSplit D hS).symm (τ,t))
    have hc := congrArg Prod.fst (sourceNativeTimeSplit_symm_clocks D hS τ t)
    have hn := congrArg Prod.snd (sourceNativeTimeSplit_symm_clocks D hS τ t)
    change nativeCoreClock D hS ((sourceNativeTimeSplit D hS).symm (τ,t)) = τ at hc
    change nativeTimeRestriction D hS ((sourceNativeTimeSplit D hS).symm (τ,t)) = t at hn
    rw [hc,hn] at h
    exact h
  apply (congrArg (fun g : (((s : ReplacementSlot S) → NativeTimeBlock D s) → ℂ) => ∫ t, g t) he).trans
  exact (integral_const_mul _ _).trans (congrArg
    (fun z => coreKernelIntegrandW D hS L γ δ layer tt k₀ (collapseGenDecoration D hS κ).1 τ * z)
      (integral_fintype_prod_volume_eq_prod _))

theorem integrable_reducedDecorationIntegrandN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    Integrable (reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ κ) := by
  have hf := integrable_kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) (fun b => tt b.1.1) 0 k₀ κ
  have hi := (measurePreserving_sourceNativeTimeSplit D hS).symm.integrable_comp_of_integrable hf
  exact hi.integral_prod_left.congr (Filter.Eventually.of_forall
    (integral_native_section_eq_reducedN D hS L γ δ A layer hLayer tt k₀ κ))

theorem integral_norm_reducedDecorationIntegrand_leN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (∫ τ, ‖reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ κ τ‖) ≤
      ∫ τ, ‖kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ τ‖ := by
  let f : (GBranch (D.forest hS) → ℝ) → ℂ :=
    kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ
  have hf : Integrable f := integrable_kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) _ _ _ κ
  have hmp := measurePreserving_sourceNativeTimeSplit D hS
  have hi := hmp.symm.integrable_comp_of_integrable hf
  have hr := integrable_reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ κ
  have hm : (∫ τ, ‖reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ κ τ‖) ≤
      ∫ τ, ∫ t, ‖f ((sourceNativeTimeSplit D hS).symm (τ,t))‖ := by
    apply integral_mono_ae hr.norm hi.norm.integral_prod_left
    apply Filter.Eventually.of_forall
    intro τ
    exact (congrArg norm (integral_native_section_eq_reducedN D hS L γ δ A layer hLayer tt k₀ κ τ)).symm.trans_le
      (norm_integral_le_integral_norm _)
  have ht : (∫ τ, ∫ t, ‖f ((sourceNativeTimeSplit D hS).symm (τ,t))‖) = ∫ τ, ‖f τ‖ :=
    (integral_prod _ hi.norm).symm.trans (hmp.symm.integral_comp' (fun τ => ‖f τ‖))
  exact hm.trans_eq ht




theorem summable_integral_norm_reducedDecorationIntegrandN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀+latticePoint L n)|) :
    Summable (fun κ : GenDecoration (D.garden hS) d n nfl =>
      ∫ τ, ‖reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ κ τ‖) := by
  have hs := summable_integral_norm_kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) (fun b => tt b.1.1) 0 k₀ n nfl
    (lone_count_le_one_of_plain _ (D.garden_plain hS)) hA
  exact Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (integral_norm_reducedDecorationIntegrand_leN D hS L γ δ A layer hLayer tt k₀) hs

theorem reducedDecorationIntegrand_glueN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (τ : GBranch S.tree → ℝ) :
    reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ (glueGenDecoration D hS κ ρ) τ =
      coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
        ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀ κ.1 τ s (ρ s) t := by
  unfold reducedDecorationIntegrandN
  rw [collapseGenDecoration_glue,restrictRelativeDecorations_glue]

/-- TARGET redkg: for every genuine skeleton decoration the independent native
lattice sum may be moved through the core time integral. Its summed L1 bound is
inherited from the full source kernel by the proved coordinate equivalences. -/
theorem tsum_integral_reduced_fixed_skeletonN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀+latticePoint L n)|) :
    (∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      ∫ τ, reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ (glueGenDecoration D hS κ ρ) τ) =
      ∫ τ, ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ (glueGenDecoration D hS κ ρ) τ := by
  have (s : ReplacementSlot S) : Countable (NativeRelativeDecoration D hS d s) := by
    cases s <;> dsimp only [NativeRelativeDecoration] <;> unfold GenDecoration <;> infer_instance
  have hs := (summable_integral_norm_reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ n nfl hA).comp_injective
    (glueGenDecoration_injective D hS κ)
  exact (integral_tsum_of_summable_integral_norm
    (fun ρ => integrable_reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ (glueGenDecoration D hS κ ρ)) hs)




theorem tsum_reduced_fixed_skeletonN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl) (τ : GBranch S.tree → ℝ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀+latticePoint L n)|) :
    (∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ (glueGenDecoration D hS κ ρ) τ) =
      coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
        ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀ κ.1 τ s ρ t := by
  have (s : ReplacementSlot S) : Countable (NativeRelativeDecoration D hS d s) := by
    cases s <;> dsimp only [NativeRelativeDecoration] <;> unfold GenDecoration <;> infer_instance
  let f := fun s (ρ : NativeRelativeDecoration D hS d s) =>
    ∫ t, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀ κ.1 τ s ρ t
  have hf (s : ReplacementSlot S) : Summable (f s) :=
    summable_nativeKernelIntegralN D hS L γ δ A layer hLayer tt k₀ κ.1 τ hA s
  apply (tsum_congr (fun ρ => reducedDecorationIntegrand_glueN D hS L γ δ A layer hLayer tt k₀ κ ρ τ)).trans
  rw [tsum_mul_left]
  exact congrArg (fun z => coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ * z)
    (tsum_pi_prod_complex f hf)

theorem nativeKernelValue_prod_eqN {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    (∏ s : ReplacementSlot S, nativeKernelValueN D hS L γ δ A layer hLayer tt k₀ κ τ s) =
      (∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s) *
        ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀ κ τ s ρ t := by
  simp_rw [nativeKernelValueN_eq_tsum_integral]
  exact Finset.prod_mul_distrib



end WaveTurbulence.RegRedLeaf
