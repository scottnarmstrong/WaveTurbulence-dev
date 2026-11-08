/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PRedNode
public import WaveTurbulence.Foundations.Flower.MkSlots.RedFix
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.WRed

/-! # B3s MK-SLOTS: the pinned node-weighted skeleton reduction (PRED, part 2)

The pinned twin of `Stage1WNoVine.WNode` (native part) and `Stage1WNoVine.WRed`.  For pins
`fixG : GBranch (D.forest hS) → Option ℝ` on the reconstructed garden, the decoration-restricted weighted sum of the
`fixMeasure fixG` integrals of the literal summand is the skeleton sum of the core integral against
`fixMeasure (fixCore D hS fixG)` of the core integrand times the pinned weighted native kernels, each native time
integral being against `fixMeasure (fixNative D hS fixG s)` (`kernelNodeWF_native_reduction_selNWF`).

The steps are those of `WRed` with `∂(fixMeasure …)` inserted: the time factorization is
`RedFix.integral_kernelAllIntegrandN_reconstruction_fix`, integrability and the L¹ bounds come from
`PRedNode` (support in the unit layer box) through the pinned split `measurePreserving_sourceNativeTimeSplit_fix`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlots
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine

theorem norm_prod_le_pow_card {ι : Type*} [Fintype ι] (f : ι → ℂ) (Cw : ℝ) (hf : ∀ i, ‖f i‖ ≤ Cw) :
    ‖∏ i, f i‖ ≤ Cw ^ Fintype.card ι := by
  refine (Finset.norm_prod_le _ _).trans ?_
  exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => hf a)).trans_eq
    (by rw [Finset.prod_const, Finset.card_univ])

/-! ### The pinned weighted native kernels -/

section Native

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (fixG : GBranch (D.forest hS) → Option ℝ)

/-- The pinned weighted native kernel of a replacement slot (`WNode.nativeKernelValueNW` with the native pins
`fixNative D hS fixG s`). -/
def nativeKernelValueNWF : ReplacementSlot S → ℂ
  | .inl p => kernelNodeWF L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun k => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k a))
      (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0 (fixNative D hS fixG (.inl p))
  | .inr b => kernelNodeWF L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (fun k => ∏ a, W (chainContextNode D hS b a) (k a))
      (fun _ => parentClockWith tt τ b.toNode) (τ b) (k₀ + latticePoint L (κ b.toNode))
      (fun _ => 0) 0 (fixNative D hS fixG (.inr b))

theorem nativeKernelValueNWF_eq_tsum_integral (s : ReplacementSlot S) :
    nativeKernelValueNWF D hS L γ δ A W layer hLayer tt k₀ κ τ fixG s =
      nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s *
        ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ τ s ρ t
            ∂(fixMeasure (fixNative D hS fixG s)) := by
  cases s with
  | inl p =>
    exact kernelNodeWF_eq_tsum_integral_all L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun k => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k a))
      (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0 (fixNative D hS fixG (.inl p))
  | inr b =>
    exact kernelNodeWF_eq_tsum_integral_all L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (fun k => ∏ a, W (chainContextNode D hS b a) (k a))
      (fun _ => parentClockWith tt τ b.toNode) (τ b) (k₀ + latticePoint L (κ b.toNode))
      (fun _ => 0) 0 (fixNative D hS fixG (.inr b))

/-- No pins: the pinned weighted native kernel is `WNode.nativeKernelValueNW`. -/
theorem nativeKernelValueNWF_none (s : ReplacementSlot S) :
    nativeKernelValueNWF D hS L γ δ A W layer hLayer tt k₀ κ τ (fun _ => none) s =
      nativeKernelValueNW D hS L γ δ A W layer hLayer tt k₀ κ τ s := by
  cases s with
  | inl p =>
    exact kernelNodeWF_none L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun k => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k a))
      (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode))
      (noFlowerParent_of_noFlower _ (nativeCouple_noFlower D hS p)) (fun _ => 0) 0
  | inr b =>
    exact kernelNodeWF_none L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (fun k => ∏ a, W (chainContextNode D hS b a) (k a))
      (fun _ => parentClockWith tt τ b.toNode) (τ b) (k₀ + latticePoint L (κ b.toNode))
      (noFlowerParent_of_noFlower _ (decodedTree_noFlower _ _)) (fun _ => 0) 0

theorem summable_nativeKernelIntegralNWF (Cw : ℝ) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (s : ReplacementSlot S) :
    Summable (fun ρ : NativeRelativeDecoration D hS d s =>
      ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ τ s ρ t
        ∂(fixMeasure (fixNative D hS fixG s))) := by
  cases s with
  | inl p =>
    have hp : (nativeCoupleLayered D hS layer hLayer p).garden.IsPlain :=
      Comb.RootedSubforest.inducedGarden_plain (G := D.garden hS) (nativeCoupleForest D hS p)
        (nativeCoupleForest_closed D hS p)
    exact summable_integral_kernelAllIntegrandNW_fix L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun k => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k a))
      (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) _
      (fun k => norm_prod_le_pow_card _ Cw fun a => hW _ _) (fun _ => 0) 0
      (lone_count_le_one_of_plain _ hp) (nativeCouple_input_summableN D hS L A k₀ κ hA p)
      (fixNative D hS fixG (.inl p))
  | inr b =>
    exact summable_integral_kernelAllIntegrandNW_fix L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (fun k => ∏ a, W (chainContextNode D hS b a) (k a))
      (fun _ => parentClockWith tt τ b.toNode) (τ b) (k₀ + latticePoint L (κ b.toNode)) _
      (fun k => norm_prod_le_pow_card _ Cw fun a => hW _ _) (fun _ => 0) 0
      (card_lone_le_one (fun _ _ h h' => (decodedTree_isPairedTree _ _).eq_of_isLone h h'))
      (nativeChain_input_summableN D hS L A k₀ κ hA b) (fixNative D hS fixG (.inr b))

end Native

/-! ### The pinned reduced decoration integrand -/

section Reduction

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (fixG : GBranch (D.forest hS) → Option ℝ)

/-- The reduced decoration integrand with pinned native integrals (main's `reducedDecorationIntegrandN`). -/
def reducedDecorationIntegrandNF {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) : ℂ :=
  coreKernelIntegrandW D hS L γ δ layer tt k₀ (collapseGenDecoration D hS κ).1 τ *
    ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀
      (collapseGenDecoration D hS κ).1 τ s (restrictRelativeDecorations D hS κ s) t
        ∂(fixMeasure (fixNative D hS fixG s))

theorem integral_native_section_eq_reducedNF {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) :
    (∫ t, kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ
        ((sourceNativeTimeSplit D hS).symm (τ, t)) ∂(Measure.pi fun s => fixMeasure (fixNative D hS fixG s))) =
      reducedDecorationIntegrandNF D hS L γ δ A layer hLayer tt k₀ fixG κ τ := by
  have he : (fun t => kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A
      (fun b => tt b.1.1) 0 k₀ κ ((sourceNativeTimeSplit D hS).symm (τ, t))) =
      (fun t : (s : ReplacementSlot S) → NativeTimeBlock D s =>
        coreKernelIntegrandW D hS L γ δ layer tt k₀ (collapseGenDecoration D hS κ).1 τ *
          ∏ s, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀
            (collapseGenDecoration D hS κ).1 τ s (restrictRelativeDecorations D hS κ s) (t s)) := by
    funext t
    have h := kernelAllIntegrandN_reconstruction D hS L γ δ A layer hLayer tt k₀ κ
      ((sourceNativeTimeSplit D hS).symm (τ, t))
    have hc := congrArg Prod.fst (sourceNativeTimeSplit_symm_clocks D hS τ t)
    have hn := congrArg Prod.snd (sourceNativeTimeSplit_symm_clocks D hS τ t)
    change nativeCoreClock D hS ((sourceNativeTimeSplit D hS).symm (τ, t)) = τ at hc
    change nativeTimeRestriction D hS ((sourceNativeTimeSplit D hS).symm (τ, t)) = t at hn
    rw [hc, hn] at h
    exact h
  rw [he, integral_const_mul, integral_fintype_prod_eq_prod]
  rfl

theorem integrable_reducedDecorationIntegrandNF {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    Integrable (reducedDecorationIntegrandNF D hS L γ δ A layer hLayer tt k₀ fixG κ)
      (fixMeasure (fixCore D hS fixG)) := by
  have hf := integrable_kernelAllIntegrandN_fix L γ δ (layeredReconstruction D hS layer hLayer) A
    (fun b => tt b.1.1) 0 k₀ κ fixG
  have hi := (measurePreserving_sourceNativeTimeSplit_fix D hS fixG).symm.integrable_comp_of_integrable hf
  exact hi.integral_prod_left.congr (Filter.Eventually.of_forall
    (integral_native_section_eq_reducedNF D hS L γ δ A layer hLayer tt k₀ fixG κ))

theorem integral_norm_reducedDecorationIntegrand_leNF {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (∫ τ, ‖reducedDecorationIntegrandNF D hS L γ δ A layer hLayer tt k₀ fixG κ τ‖ ∂(fixMeasure (fixCore D hS fixG))) ≤
      ∫ τ, ‖kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ τ‖
        ∂(fixMeasure fixG) := by
  let f : (GBranch (D.forest hS) → ℝ) → ℂ :=
    kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ
  have hf : Integrable f (fixMeasure fixG) :=
    integrable_kernelAllIntegrandN_fix L γ δ (layeredReconstruction D hS layer hLayer) A _ _ _ κ fixG
  have hmp := measurePreserving_sourceNativeTimeSplit_fix D hS fixG
  have hi := hmp.symm.integrable_comp_of_integrable hf
  have hr := integrable_reducedDecorationIntegrandNF D hS L γ δ A layer hLayer tt k₀ fixG κ
  have hm : (∫ τ, ‖reducedDecorationIntegrandNF D hS L γ δ A layer hLayer tt k₀ fixG κ τ‖
      ∂(fixMeasure (fixCore D hS fixG))) ≤
      ∫ τ, ∫ t, ‖f ((sourceNativeTimeSplit D hS).symm (τ, t))‖
        ∂(Measure.pi fun s => fixMeasure (fixNative D hS fixG s)) ∂(fixMeasure (fixCore D hS fixG)) := by
    apply integral_mono_ae hr.norm hi.norm.integral_prod_left
    apply Filter.Eventually.of_forall
    intro τ
    exact (congrArg norm
      (integral_native_section_eq_reducedNF D hS L γ δ A layer hLayer tt k₀ fixG κ τ)).symm.trans_le
      (norm_integral_le_integral_norm _)
  have ht : (∫ τ, ∫ t, ‖f ((sourceNativeTimeSplit D hS).symm (τ, t))‖
        ∂(Measure.pi fun s => fixMeasure (fixNative D hS fixG s)) ∂(fixMeasure (fixCore D hS fixG))) =
      ∫ τ, ‖f τ‖ ∂(fixMeasure fixG) :=
    (integral_prod _ hi.norm).symm.trans (hmp.symm.integral_comp' (fun τ => ‖f τ‖))
  exact hm.trans_eq ht

/-- The pinned weighted reduced decoration integrand: the pinned reduced integrand times the decoration weight. -/
def reducedDecorationIntegrandNWF {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) : ℂ :=
  (∏ z, W z (cosetDecoration (D.garden hS) L k₀ κ.1 z)) *
    reducedDecorationIntegrandNF D hS L γ δ A layer hLayer tt k₀ fixG κ τ

theorem integral_kernelAllIntegrandNW_reconstruction_fix {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
        (fun b => tt b.1.1) 0 k₀ κ τ ∂(fixMeasure fixG)) =
      ∫ τ, reducedDecorationIntegrandNWF D hS L γ δ A W layer hLayer tt k₀ fixG κ τ
        ∂(fixMeasure (fixCore D hS fixG)) := by
  unfold kernelAllIntegrandNW reducedDecorationIntegrandNWF
  rw [integral_const_mul (μ := fixMeasure (fixCore D hS fixG))]
  refine (integral_const_mul (μ := fixMeasure fixG) _ _).trans ?_
  exact congrArg₂ (· * ·) rfl (integral_kernelAllIntegrandN_reconstruction_fix D hS L γ δ A layer hLayer tt k₀ κ fixG
    (integrable_kernelAllIntegrandN_fix L γ δ (layeredReconstruction D hS layer hLayer) A _ _ _ κ fixG))

theorem integrable_reducedDecorationIntegrandNWF {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    Integrable (reducedDecorationIntegrandNWF D hS L γ δ A W layer hLayer tt k₀ fixG κ)
      (fixMeasure (fixCore D hS fixG)) :=
  (integrable_reducedDecorationIntegrandNF D hS L γ δ A layer hLayer tt k₀ fixG κ).const_mul _

theorem summable_integral_norm_reducedDecorationIntegrandNWF (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hW : ∀ z x, ‖W z x‖ ≤ Cw) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration (D.garden hS) d n nfl =>
      ∫ τ, ‖reducedDecorationIntegrandNWF D hS L γ δ A W layer hLayer tt k₀ fixG κ τ‖
        ∂(fixMeasure (fixCore D hS fixG))) := by
  have hs0 : Summable (fun κ : GenDecoration (D.garden hS) d n nfl =>
      ∫ τ, ‖reducedDecorationIntegrandNF D hS L γ δ A layer hLayer tt k₀ fixG κ τ‖
        ∂(fixMeasure (fixCore D hS fixG))) := by
    have hk := summable_integral_norm_kernelAllIntegrandNW_fix L γ δ (layeredReconstruction D hS layer hLayer) A
      (fun _ => 1) (fun b => tt b.1.1) 0 k₀ 1 (fun _ => by simp) n nfl
      (lone_count_le_one_of_plain _ (D.garden_plain hS)) hA fixG
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun κ => ?_) hk
    refine (integral_norm_reducedDecorationIntegrand_leNF D hS L γ δ A layer hLayer tt k₀ fixG κ).trans_eq ?_
    unfold kernelAllIntegrandNW
    simp only [one_mul]
    rfl
  have hs := hs0.mul_left (Cw ^ Fintype.card (GNode (D.forest hS)))
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun κ => ?_) hs
  unfold reducedDecorationIntegrandNWF
  simp_rw [norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_right (norm_fullWeight_le D hS W Cw hCw hW _)
    (integral_nonneg fun _ => norm_nonneg _)

theorem reducedDecorationIntegrandNWF_glue {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (τ : GBranch S.tree → ℝ) :
    reducedDecorationIntegrandNWF D hS L γ δ A W layer hLayer tt k₀ fixG (glueGenDecoration D hS κ ρ) τ =
      coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
        ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s (ρ s) t
          ∂(fixMeasure (fixNative D hS fixG s)) := by
  unfold reducedDecorationIntegrandNWF reducedDecorationIntegrandNF
  rw [weight_relative_reconstruction D hS L W k₀ (glueGenDecoration D hS κ ρ),
    collapseGenDecoration_glue, restrictRelativeDecorations_glue]
  unfold nativeKernelIntegrandNW
  simp_rw [integral_const_mul]
  rw [Finset.prod_mul_distrib]
  ring

theorem tsum_integral_reduced_fixed_skeletonNWF (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration S d n nfl)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    (∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      ∫ τ, reducedDecorationIntegrandNWF D hS L γ δ A W layer hLayer tt k₀ fixG (glueGenDecoration D hS κ ρ) τ
        ∂(fixMeasure (fixCore D hS fixG))) =
      ∫ τ, ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        reducedDecorationIntegrandNWF D hS L γ δ A W layer hLayer tt k₀ fixG (glueGenDecoration D hS κ ρ) τ
          ∂(fixMeasure (fixCore D hS fixG)) := by
  have (s : ReplacementSlot S) : Countable (NativeRelativeDecoration D hS d s) := by
    cases s <;> dsimp only [NativeRelativeDecoration] <;> unfold GenDecoration <;> infer_instance
  have hs := (summable_integral_norm_reducedDecorationIntegrandNWF D hS L γ δ A W layer hLayer tt k₀ fixG Cw hCw hW
    n nfl hA).comp_injective (glueGenDecoration_injective D hS κ)
  exact integral_tsum_of_summable_integral_norm
    (fun ρ => integrable_reducedDecorationIntegrandNWF D hS L γ δ A W layer hLayer tt k₀ fixG
      (glueGenDecoration D hS κ ρ)) hs

theorem tsum_reduced_fixed_skeletonNWF (Cw : ℝ) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl) (τ : GBranch S.tree → ℝ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    (∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      reducedDecorationIntegrandNWF D hS L γ δ A W layer hLayer tt k₀ fixG (glueGenDecoration D hS κ ρ) τ) =
      coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
        ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s ρ t
            ∂(fixMeasure (fixNative D hS fixG s)) := by
  have (s : ReplacementSlot S) : Countable (NativeRelativeDecoration D hS d s) := by
    cases s <;> dsimp only [NativeRelativeDecoration] <;> unfold GenDecoration <;> infer_instance
  let f := fun s (ρ : NativeRelativeDecoration D hS d s) =>
    ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s ρ t ∂(fixMeasure (fixNative D hS fixG s))
  have hf (s : ReplacementSlot S) : Summable (f s) :=
    summable_nativeKernelIntegralNWF D hS L γ δ A W layer hLayer tt k₀ κ.1 τ fixG Cw hW hA s
  apply (tsum_congr (fun ρ => reducedDecorationIntegrandNWF_glue D hS L γ δ A W layer hLayer tt k₀ fixG κ ρ τ)).trans
  rw [tsum_mul_left]
  exact congrArg (fun z => coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ * z) (tsum_pi_prod_complex f hf)

/-- The pinned weighted raw reduction (`WRed.tsum_integral_sel_reductionNW` with pins). -/
theorem tsum_integral_sel_reductionNWF (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) :
    (∑' κ : GenDecoration (D.garden hS) d n nfl,
      if selSk (collapseGenDecoration D hS κ) then
        ∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
          (fun b => tt b.1.1) 0 k₀ κ τ ∂(fixMeasure fixG)
      else 0) =
      ∑' κ : GenDecoration S d n nfl, if selSk κ then
        ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
          ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
            ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s ρ t
              ∂(fixMeasure (fixNative D hS fixG s))
          ∂(fixMeasure (fixCore D hS fixG))
      else 0 := by
  let f : GenDecoration (D.garden hS) d n nfl → ℂ := fun κ =>
    ∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
      (fun b => tt b.1.1) 0 k₀ κ τ ∂(fixMeasure fixG)
  have hs : Summable f := summable_integral_kernelAllIntegrandNW_fix L γ δ
    (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z)) _ _ _
    (Cw ^ Fintype.card (GNode (D.forest hS))) (norm_fullWeight_le D hS W Cw hCw hW) n nfl
    (lone_count_le_one_of_plain _ (D.garden_plain hS)) hA fixG
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
      ∫ τ, reducedDecorationIntegrandNWF D hS L γ δ A W layer hLayer tt k₀ fixG (glueGenDecoration D hS κ ρ) τ
        ∂(fixMeasure (fixCore D hS fixG)))
    · exact tsum_congr (fun ρ => integral_kernelAllIntegrandNW_reconstruction_fix D hS L γ δ A W layer hLayer
        tt k₀ fixG (glueGenDecoration D hS κ ρ))
    · apply (tsum_integral_reduced_fixed_skeletonNWF D hS L γ δ A W layer hLayer tt k₀ fixG Cw hCw hW κ hA).trans
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun τ => tsum_reduced_fixed_skeletonNWF D hS L γ δ A W layer hLayer tt k₀ fixG Cw hW κ τ hA))
  · simp only [hκ, ite_false]
    have hg : ∀ ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        g (glueGenDecoration D hS κ ρ) = 0 := by
      intro ρ
      simp only [g, collapseGenDecoration_glue, hκ, ite_false]
    rw [tsum_congr hg, tsum_zero]

theorem nativeKernelValueNWF_prod_eq (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    (∏ s : ReplacementSlot S, nativeKernelValueNWF D hS L γ δ A W layer hLayer tt k₀ κ τ fixG s) =
      (∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s) *
        ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ τ s ρ t
            ∂(fixMeasure (fixNative D hS fixG s)) := by
  simp_rw [nativeKernelValueNWF_eq_tsum_integral]
  exact Finset.prod_mul_distrib

/-- **The pinned weighted native reduction** (`WRed.kernelNodeW_native_reduction_sel` with pins). -/
theorem kernelNodeWF_native_reduction_selNWF (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) :
    (coupling d L γ δ : ℂ) ^ (D.garden hS).order * (D.garden hS).zeta *
      (∑' κ : GenDecoration (D.garden hS) d n nfl,
        if selSk (collapseGenDecoration D hS κ) then
          ∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
            (fun b => tt b.1.1) 0 k₀ κ τ ∂(fixMeasure fixG)
        else 0) =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then
          ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
            ∏ s : ReplacementSlot S, nativeKernelValueNWF D hS L γ δ A W layer hLayer tt k₀ κ.1 τ fixG s
            ∂(fixMeasure (fixCore D hS fixG))
        else 0 := by
  let P := ∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s
  have hp : (coupling d L γ δ : ℂ) ^ (D.garden hS).order * (D.garden hS).zeta =
      ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * P := by
    change _ = ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) *
      (∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s)
    rw [Fintype.prod_sum_type]
    exact (kernelPrefactor_reconstruction D hS layer hLayer (coupling d L γ δ)).trans (mul_assoc _ _ _)
  rw [tsum_integral_sel_reductionNWF D hS L γ δ A W layer hLayer tt k₀ fixG Cw hCw hW n nfl hA selSk, hp, mul_assoc]
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
    have hv := nativeKernelValueNWF_prod_eq D hS L γ δ A W layer hLayer tt k₀ fixG κ.1 τ
    exact (mul_left_comm P (coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ) _).trans
      (congrArg (fun z => coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ * z) hv).symm
  · simp only [hκ, ite_false, mul_zero]

end Reduction

end WaveTurbulence.Flower.MkSlots
