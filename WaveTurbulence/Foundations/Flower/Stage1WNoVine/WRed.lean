/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.WNode

/-! # STAGE1W-O4: the node-weighted skeleton reduction (row T2, part 2)

The weighted analogue of REGRED-LEAF's `tsum_integral_sel_reduction` and `kernelNode_native_reduction_sel`:
for a node weight `W` bounded by `Cw`, the decoration-restricted weighted sum of the reconstructed garden is the
skeleton sum of the core integral against the product of the weighted native kernels
(`kernelNodeW_native_reduction_sel`).  Since the weight depends only on the decoration, every step is main's step
multiplied by the (bounded) decoration weight. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf

section Reduction

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d)

/-- The weighted reduced decoration integrand: main's times the decoration weight. -/
def reducedDecorationIntegrandNW {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) : ℂ :=
  (∏ z, W z (cosetDecoration (D.garden hS) L k₀ κ.1 z)) *
    reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ κ τ

theorem norm_fullWeight_le (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (k : GNode (D.forest hS) → Mom d) :
    ‖∏ z, W z (k z)‖ ≤ Cw ^ Fintype.card (GNode (D.forest hS)) := by
  refine (Finset.norm_prod_le _ _).trans ?_
  exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => hW _ _)).trans_eq
    (by rw [Finset.prod_const, Finset.card_univ])

theorem integral_kernelAllIntegrandNW_reconstruction {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
        (fun b => tt b.1.1) 0 k₀ κ τ) =
      ∫ τ, reducedDecorationIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ τ := by
  unfold kernelAllIntegrandNW reducedDecorationIntegrandNW
  rw [integral_const_mul, integral_const_mul,
    integral_kernelAllIntegrandN_reconstruction D hS L γ δ A layer hLayer tt k₀ κ]
  rfl

theorem integrable_reducedDecorationIntegrandNW {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    Integrable (reducedDecorationIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ) :=
  (integrable_reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ κ).const_mul _

theorem summable_integral_norm_reducedDecorationIntegrandNW (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hW : ∀ z x, ‖W z x‖ ≤ Cw) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration (D.garden hS) d n nfl =>
      ∫ τ, ‖reducedDecorationIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ τ‖) := by
  have hs := (summable_integral_norm_reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ n nfl hA).mul_left
    (Cw ^ Fintype.card (GNode (D.forest hS)))
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun κ => ?_) hs
  unfold reducedDecorationIntegrandNW
  simp_rw [norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_right (norm_fullWeight_le D hS W Cw hCw hW _)
    (integral_nonneg fun _ => norm_nonneg _)

theorem reducedDecorationIntegrandNW_glue {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (τ : GBranch S.tree → ℝ) :
    reducedDecorationIntegrandNW D hS L γ δ A W layer hLayer tt k₀ (glueGenDecoration D hS κ ρ) τ =
      coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
        ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s (ρ s) t := by
  unfold reducedDecorationIntegrandNW
  rw [reducedDecorationIntegrand_glueN D hS L γ δ A layer hLayer tt k₀ κ ρ τ,
    weight_relative_reconstruction D hS L W k₀ (glueGenDecoration D hS κ ρ),
    collapseGenDecoration_glue, restrictRelativeDecorations_glue]
  unfold nativeKernelIntegrandNW
  simp_rw [integral_const_mul]
  rw [Finset.prod_mul_distrib]
  ring

theorem tsum_integral_reduced_fixed_skeletonNW (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration S d n nfl)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    (∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      ∫ τ, reducedDecorationIntegrandNW D hS L γ δ A W layer hLayer tt k₀ (glueGenDecoration D hS κ ρ) τ) =
      ∫ τ, ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        reducedDecorationIntegrandNW D hS L γ δ A W layer hLayer tt k₀ (glueGenDecoration D hS κ ρ) τ := by
  have (s : ReplacementSlot S) : Countable (NativeRelativeDecoration D hS d s) := by
    cases s <;> dsimp only [NativeRelativeDecoration] <;> unfold GenDecoration <;> infer_instance
  have hs := (summable_integral_norm_reducedDecorationIntegrandNW D hS L γ δ A W layer hLayer tt k₀ Cw hCw hW
    n nfl hA).comp_injective (glueGenDecoration_injective D hS κ)
  exact integral_tsum_of_summable_integral_norm
    (fun ρ => integrable_reducedDecorationIntegrandNW D hS L γ δ A W layer hLayer tt k₀ (glueGenDecoration D hS κ ρ)) hs

theorem tsum_reduced_fixed_skeletonNW (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl) (τ : GBranch S.tree → ℝ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    (∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      reducedDecorationIntegrandNW D hS L γ δ A W layer hLayer tt k₀ (glueGenDecoration D hS κ ρ) τ) =
      coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
        ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s ρ t := by
  have (s : ReplacementSlot S) : Countable (NativeRelativeDecoration D hS d s) := by
    cases s <;> dsimp only [NativeRelativeDecoration] <;> unfold GenDecoration <;> infer_instance
  let f := fun s (ρ : NativeRelativeDecoration D hS d s) =>
    ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s ρ t
  have hf (s : ReplacementSlot S) : Summable (f s) :=
    summable_nativeKernelIntegralNW D hS L γ δ A W Cw hCw hW layer hLayer tt k₀ κ.1 τ hA s
  apply (tsum_congr (fun ρ => reducedDecorationIntegrandNW_glue D hS L γ δ A W layer hLayer tt k₀ κ ρ τ)).trans
  rw [tsum_mul_left]
  exact congrArg (fun z => coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ * z) (tsum_pi_prod_complex f hf)

/-- The weighted raw reduction (main's `tsum_integral_sel_reduction` with a node weight). -/
theorem tsum_integral_sel_reductionNW (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) :
    (∑' κ : GenDecoration (D.garden hS) d n nfl,
      if selSk (collapseGenDecoration D hS κ) then
        ∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
          (fun b => tt b.1.1) 0 k₀ κ τ
      else 0) =
      ∑' κ : GenDecoration S d n nfl, if selSk κ then
        ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
          ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
            ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s ρ t
      else 0 := by
  let f : GenDecoration (D.garden hS) d n nfl → ℂ := fun κ =>
    ∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
      (fun b => tt b.1.1) 0 k₀ κ τ
  have hs : Summable f := summable_integral_kernelAllIntegrandNW L γ δ
    (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z)) _ _ _
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS))
    (Cw ^ Fintype.card (GNode (D.forest hS))) (norm_fullWeight_le D hS W Cw hCw hW) n nfl
    (lone_count_le_one_of_plain _ (D.garden_plain hS)) hA
  let g : GenDecoration (D.garden hS) d n nfl → ℂ := fun κ =>
    if selSk (collapseGenDecoration D hS κ) then f κ else 0
  have hgs : Summable g := by
    apply Summable.of_norm_bounded hs.norm
    intro κ
    by_cases h : selSk (collapseGenDecoration D hS κ)
    · simp only [g, h, ite_true, le_refl]
    · simp only [g, h, ite_false, norm_zero, norm_nonneg]
  have hp : Summable (fun p : GenDecoration S d n nfl ×
      ((s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) =>
        g (glueGenDecoration D hS p.1 p.2)) :=
    hgs.comp_injective (decorationFiberEquiv D hS n nfl).symm.injective
  have hsplit : (∑' κ, g κ) = ∑' κ : GenDecoration S d n nfl,
      ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        g (glueGenDecoration D hS κ ρ) :=
    (tsum_decorationFiberEquiv D hS n nfl g).trans hp.tsum_prod
  change (∑' κ, g κ) = _
  rw [hsplit]
  apply tsum_congr
  intro κ
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    have hg : ∀ ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        g (glueGenDecoration D hS κ ρ) = f (glueGenDecoration D hS κ ρ) := by
      intro ρ
      simp only [g, collapseGenDecoration_glue, hκ, ite_true]
    rw [tsum_congr hg]
    apply Eq.trans (b := ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      ∫ τ, reducedDecorationIntegrandNW D hS L γ δ A W layer hLayer tt k₀ (glueGenDecoration D hS κ ρ) τ)
    · exact tsum_congr (fun ρ => integral_kernelAllIntegrandNW_reconstruction D hS L γ δ A W layer hLayer
        tt k₀ (glueGenDecoration D hS κ ρ))
    · apply (tsum_integral_reduced_fixed_skeletonNW D hS L γ δ A W layer hLayer tt k₀ Cw hCw hW κ hA).trans
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun τ => tsum_reduced_fixed_skeletonNW D hS L γ δ A W layer hLayer tt k₀ Cw hCw hW κ τ hA))
  · simp only [hκ, ite_false]
    have hg : ∀ ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        g (glueGenDecoration D hS κ ρ) = 0 := by
      intro ρ
      simp only [g, collapseGenDecoration_glue, hκ, ite_false]
    rw [tsum_congr hg, tsum_zero]

theorem nativeKernelValueNW_prod_eq (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    (∏ s : ReplacementSlot S, nativeKernelValueNW D hS L γ δ A W layer hLayer tt k₀ κ τ s) =
      (∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s) *
        ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ τ s ρ t := by
  simp_rw [nativeKernelValueNW_eq_tsum_integral]
  exact Finset.prod_mul_distrib

/-- **The weighted native reduction** (main's `kernelNode_native_reduction_sel` with a node weight). -/
theorem kernelNodeW_native_reduction_sel (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) :
    (coupling d L γ δ : ℂ) ^ (D.garden hS).order * (D.garden hS).zeta *
      (∑' κ : GenDecoration (D.garden hS) d n nfl,
        if selSk (collapseGenDecoration D hS κ) then
          ∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
            (fun b => tt b.1.1) 0 k₀ κ τ
        else 0) =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then
          ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
            ∏ s : ReplacementSlot S, nativeKernelValueNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s
        else 0 := by
  let P := ∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s
  have hp : (coupling d L γ δ : ℂ) ^ (D.garden hS).order * (D.garden hS).zeta =
      ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * P := by
    change _ = ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) *
      (∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s)
    rw [Fintype.prod_sum_type]
    exact (kernelPrefactor_reconstruction D hS layer hLayer (coupling d L γ δ)).trans (mul_assoc _ _ _)
  rw [tsum_integral_sel_reductionNW D hS L γ δ A W layer hLayer tt k₀ Cw hCw hW n nfl hA selSk, hp, mul_assoc]
  apply congrArg (fun z => ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * z)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro κ
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro τ
    have hv := nativeKernelValueNW_prod_eq D hS L γ δ A W layer hLayer tt k₀ κ.1 τ
    exact (mul_left_comm P (coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ) _).trans
      (congrArg (fun z => coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ * z) hv).symm
  · simp only [hκ, ite_false, mul_zero]

end Reduction

end WaveTurbulence.Flower.Stage1WNoVine
