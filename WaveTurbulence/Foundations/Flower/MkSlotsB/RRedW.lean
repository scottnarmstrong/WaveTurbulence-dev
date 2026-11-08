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

/-- The relaxed weighted native integrand: node weight, slot weight `Θs`, relaxed native integrand. -/
def nativeKernelIntegrandNWR (s : ReplacementSlot S) (ρ : NativeRelativeDecoration D hS d s)
    (t : NativeTimeBlock D s) : ℂ :=
  nativeWeightFactor D hS L W k₀ κ s ρ * Θs s (slotMom hS L k₀ κ s) ρ *
    nativeKernelIntegrandNR D hS L γ δ A layer hLayer tt k₀ κ τ fixG s ρ t

/-- **The relaxed weighted native kernel of a replacement slot** (pins `fixNative D hS fixG s`, domain
`nativeDomainWR`, slot weight `Θs s` at the slot momentum). -/
def nativeKernelValueNWR : ReplacementSlot S → ℂ
  | .inl p => kernelNodeWR L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun k => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k a))
      (nativeDomainWR D hS layer hLayer tt τ fixG (.inl p))
      (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0
      (Θs (.inl p) (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode))) (fixNative D hS fixG (.inl p))
  | .inr b => kernelNodeWR L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (fun k => ∏ a, W (chainContextNode D hS b a) (k a))
      (nativeDomainWR D hS layer hLayer tt τ fixG (.inr b))
      (k₀ + latticePoint L (κ b.toNode)) (fun _ => 0) 0
      (Θs (.inr b) (k₀ + latticePoint L (κ b.toNode))) (fixNative D hS fixG (.inr b))

theorem nativeKernelValueNWR_eq_tsum_integral (s : ReplacementSlot S) :
    nativeKernelValueNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ τ fixG s =
      nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s *
        ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ τ fixG s ρ t
            ∂(fixMeasure (fixNative D hS fixG s)) := by
  cases s with
  | inl p =>
    exact kernelNodeWR_eq_tsum_integral_all L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun k => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k a))
      (nativeDomainWR D hS layer hLayer tt τ fixG (.inl p))
      (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0
      (Θs (.inl p) (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode))) (fixNative D hS fixG (.inl p))
  | inr b =>
    exact kernelNodeWR_eq_tsum_integral_all L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (fun k => ∏ a, W (chainContextNode D hS b a) (k a))
      (nativeDomainWR D hS layer hLayer tt τ fixG (.inr b))
      (k₀ + latticePoint L (κ b.toNode)) (fun _ => 0) 0
      (Θs (.inr b) (k₀ + latticePoint L (κ b.toNode))) (fixNative D hS fixG (.inr b))

theorem summable_nativeKernelIntegralNWR (Cw : ℝ) (hW : ∀ z x, ‖W z x‖ ≤ Cw) (CΘs : ℝ)
    (hΘs : ∀ s k ρ, ‖Θs s k ρ‖ ≤ CΘs)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (s : ReplacementSlot S) :
    Summable (fun ρ : NativeRelativeDecoration D hS d s =>
      ∫ t, nativeKernelIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ τ fixG s ρ t
        ∂(fixMeasure (fixNative D hS fixG s))) := by
  cases s with
  | inl p =>
    have hp : (nativeCoupleLayered D hS layer hLayer p).garden.IsPlain :=
      Comb.RootedSubforest.inducedGarden_plain (G := D.garden hS) (nativeCoupleForest D hS p)
        (nativeCoupleForest_closed D hS p)
    exact summable_integral_kernelAllIntegrandNWD_fix L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun k => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k a))
      (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) (kDomainR_subset_unitBoxR _ _ _ _ _ _) _
      (fun k => norm_prod_le_pow_card _ Cw fun a => hW _ _) (fun _ => 0) 0 _ CΘs (fun ρ => hΘs (.inl p) _ ρ)
      (lone_count_le_one_of_plain _ hp) (nativeCouple_input_summableN D hS L A k₀ κ hA p)
  | inr b =>
    exact summable_integral_kernelAllIntegrandNWD_fix L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (fun k => ∏ a, W (chainContextNode D hS b a) (k a))
      (k₀ + latticePoint L (κ b.toNode)) (kDomainR_subset_unitBoxR _ _ _ _ _ _) _
      (fun k => norm_prod_le_pow_card _ Cw fun a => hW _ _) (fun _ => 0) 0 _ CΘs (fun ρ => hΘs (.inr b) _ ρ)
      (card_lone_le_one (fun _ _ h h' => (decodedTree_isPairedTree _ _).eq_of_isLone h h'))
      (nativeChain_input_summableN D hS L A k₀ κ hA b)

theorem nativeKernelValueNWR_prod_eq :
    (∏ s : ReplacementSlot S, nativeKernelValueNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ τ fixG s) =
      (∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s) *
        ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ τ fixG s ρ t
            ∂(fixMeasure (fixNative D hS fixG s)) := by
  simp_rw [nativeKernelValueNWR_eq_tsum_integral]
  exact Finset.prod_mul_distrib

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

/-- The relaxed weighted reduced integrand. -/
def reducedDecorationIntegrandNWFR {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) : ℂ :=
  (∏ z, W z (cosetDecoration (D.garden hS) L k₀ κ.1 z)) * ΘSlots D hS L Θs k₀ κ *
    reducedDecorationIntegrandNFR D hS L γ δ A layer hLayer tt k₀ fixG κ τ

/-- The weighted garden integrand on the relaxed domain. -/
abbrev gardenIntegrandNWR {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) :
    (GBranch (D.forest hS) → ℝ) → ℂ :=
  kernelAllIntegrandNWD L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
    (kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG) k₀ (ΘSlots D hS L Θs k₀) κ

variable (hP : RelaxPins layer tt fixG)
include hP

theorem integral_gardenIntegrandNWR_reconstruction_fix {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (∫ τ, gardenIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ fixG κ τ ∂(fixMeasure fixG)) =
      ∫ τ, reducedDecorationIntegrandNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG κ τ
        ∂(fixMeasure (fixCore D hS fixG)) := by
  have h1 : (∫ τ, gardenIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ fixG κ τ ∂(fixMeasure fixG)) =
      ((∏ z, W z (cosetDecoration (D.garden hS) L k₀ κ.1 z)) * ΘSlots D hS L Θs k₀ κ) *
        ∫ τ, gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ τ ∂(fixMeasure fixG) :=
    integral_const_mul (μ := fixMeasure fixG) _ (gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ)
  have h2 : (∫ τ, reducedDecorationIntegrandNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG κ τ
        ∂(fixMeasure (fixCore D hS fixG))) =
      ((∏ z, W z (cosetDecoration (D.garden hS) L k₀ κ.1 z)) * ΘSlots D hS L Θs k₀ κ) *
        ∫ τ, reducedDecorationIntegrandNFR D hS L γ δ A layer hLayer tt k₀ fixG κ τ
          ∂(fixMeasure (fixCore D hS fixG)) :=
    integral_const_mul (μ := fixMeasure (fixCore D hS fixG)) _
      (reducedDecorationIntegrandNFR D hS L γ δ A layer hLayer tt k₀ fixG κ)
  rw [h1, h2, integral_kernelAllIntegrandD_reconstruction_fix D hS L γ δ A layer hLayer tt k₀ fixG hP κ]

theorem integrable_reducedDecorationIntegrandNWFR {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    Integrable (reducedDecorationIntegrandNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG κ)
      (fixMeasure (fixCore D hS fixG)) :=
  (integrable_reducedDecorationIntegrandNFR D hS L γ δ A layer hLayer tt k₀ fixG hP κ).const_mul _

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

theorem summable_integral_norm_reducedDecorationIntegrandNWFR (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hW : ∀ z x, ‖W z x‖ ≤ Cw) (CΘs : ℝ) (hΘs : ∀ s k ρ, ‖Θs s k ρ‖ ≤ CΘs) (n : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration (D.garden hS) d n nfl =>
      ∫ τ, ‖reducedDecorationIntegrandNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG κ τ‖
        ∂(fixMeasure (fixCore D hS fixG))) := by
  have hs0 : Summable (fun κ : GenDecoration (D.garden hS) d n nfl =>
      ∫ τ, ‖reducedDecorationIntegrandNFR D hS L γ δ A layer hLayer tt k₀ fixG κ τ‖
        ∂(fixMeasure (fixCore D hS fixG))) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun κ => integral_norm_reducedDecorationIntegrand_leNFR D hS L γ δ A layer hLayer tt k₀ fixG hP κ)
      (summable_integral_norm_gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG n nfl hA)
  have hs := hs0.mul_left (Cw ^ Fintype.card (GNode (D.forest hS)) * CΘs ^ Fintype.card (ReplacementSlot S))
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun κ => ?_) hs
  unfold reducedDecorationIntegrandNWFR
  simp_rw [norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (norm_fullWeight_le D hS W Cw hCw hW _) (norm_ΘSlots_le D hS L Θs k₀ CΘs hΘs κ) (norm_nonneg _)
      (pow_nonneg hCw _))
    (integral_nonneg fun _ => norm_nonneg _)

omit hP in
theorem reducedDecorationIntegrandNWFR_glue {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (τ : GBranch S.tree → ℝ) :
    reducedDecorationIntegrandNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG (glueGenDecoration D hS κ ρ) τ =
      coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG κ.1 τ *
        ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ.1 τ fixG s
          (ρ s) t ∂(fixMeasure (fixNative D hS fixG s)) := by
  unfold reducedDecorationIntegrandNWFR reducedDecorationIntegrandNFR ΘSlots
  rw [weight_relative_reconstruction D hS L W k₀ (glueGenDecoration D hS κ ρ),
    collapseGenDecoration_glue, restrictRelativeDecorations_glue]
  unfold nativeKernelIntegrandNWR
  simp_rw [integral_const_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

theorem tsum_integral_reduced_fixed_skeletonNWFR (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (CΘs : ℝ) (hΘs : ∀ s k ρ, ‖Θs s k ρ‖ ≤ CΘs)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration S d n nfl)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    (∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      ∫ τ, reducedDecorationIntegrandNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG (glueGenDecoration D hS κ ρ) τ
        ∂(fixMeasure (fixCore D hS fixG))) =
      ∫ τ, ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        reducedDecorationIntegrandNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG (glueGenDecoration D hS κ ρ) τ
          ∂(fixMeasure (fixCore D hS fixG)) := by
  have (s : ReplacementSlot S) : Countable (NativeRelativeDecoration D hS d s) := by
    cases s <;> dsimp only [NativeRelativeDecoration] <;> unfold GenDecoration <;> infer_instance
  have hs := (summable_integral_norm_reducedDecorationIntegrandNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG hP
    Cw hCw hW CΘs hΘs n nfl hA).comp_injective (glueGenDecoration_injective D hS κ)
  exact integral_tsum_of_summable_integral_norm
    (fun ρ => integrable_reducedDecorationIntegrandNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG hP
      (glueGenDecoration D hS κ ρ)) hs

omit hP in
theorem tsum_reduced_fixed_skeletonNWFR (Cw : ℝ) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (CΘs : ℝ) (hΘs : ∀ s k ρ, ‖Θs s k ρ‖ ≤ CΘs)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl) (τ : GBranch S.tree → ℝ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    (∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      reducedDecorationIntegrandNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG (glueGenDecoration D hS κ ρ) τ) =
      coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG κ.1 τ *
        ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ.1 τ fixG s ρ t
            ∂(fixMeasure (fixNative D hS fixG s)) := by
  have (s : ReplacementSlot S) : Countable (NativeRelativeDecoration D hS d s) := by
    cases s <;> dsimp only [NativeRelativeDecoration] <;> unfold GenDecoration <;> infer_instance
  let f := fun s (ρ : NativeRelativeDecoration D hS d s) =>
    ∫ t, nativeKernelIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ.1 τ fixG s ρ t
      ∂(fixMeasure (fixNative D hS fixG s))
  have hf (s : ReplacementSlot S) : Summable (f s) :=
    summable_nativeKernelIntegralNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ.1 τ fixG Cw hW CΘs hΘs hA s
  apply (tsum_congr (fun ρ => reducedDecorationIntegrandNWFR_glue D hS L γ δ A W Θs layer hLayer tt k₀ fixG
    κ ρ τ)).trans
  rw [tsum_mul_left]
  exact congrArg (fun z => coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG κ.1 τ * z) (tsum_pi_prod_complex f hf)

/-- The relaxed weighted raw reduction with the skeleton multiplier `Θ` and the slot weights `Θs`. -/
theorem tsum_integral_sel_reductionNWFMR (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (CΘs : ℝ) (hΘs : ∀ s k ρ, ‖Θs s k ρ‖ ≤ CΘs)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (Θ : GenDecoration S d n nfl → ℂ) (CΘ : ℝ)
    (hΘ : ∀ κ, ‖Θ κ‖ ≤ CΘ) :
    (∑' κ : GenDecoration (D.garden hS) d n nfl,
      if selSk (collapseGenDecoration D hS κ) then
        Θ (collapseGenDecoration D hS κ) *
          ∫ τ, gardenIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ fixG κ τ ∂(fixMeasure fixG)
      else 0) =
      ∑' κ : GenDecoration S d n nfl, if selSk κ then
        Θ κ * ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG κ.1 τ *
          ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
            ∫ t, nativeKernelIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ.1 τ fixG s ρ t
              ∂(fixMeasure (fixNative D hS fixG s))
          ∂(fixMeasure (fixCore D hS fixG))
      else 0 := by
  let f : GenDecoration (D.garden hS) d n nfl → ℂ := fun κ =>
    ∫ τ, gardenIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ fixG κ τ ∂(fixMeasure fixG)
  have hs : Summable f := summable_integral_kernelAllIntegrandNWD_fix L γ δ
    (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z)) k₀ (kDomainFix_subset_unitBoxR _ _ _)
    (Cw ^ Fintype.card (GNode (D.forest hS))) (norm_fullWeight_le D hS W Cw hCw hW) n nfl
    (ΘSlots D hS L Θs k₀) (CΘs ^ Fintype.card (ReplacementSlot S)) (norm_ΘSlots_le D hS L Θs k₀ CΘs hΘs)
    (lone_count_le_one_of_plain _ (D.garden_plain hS)) hA
  let g : GenDecoration (D.garden hS) d n nfl → ℂ := fun κ =>
    if selSk (collapseGenDecoration D hS κ) then Θ (collapseGenDecoration D hS κ) * f κ else 0
  have hgs : Summable g := by
    apply Summable.of_norm_bounded (hs.norm.mul_left CΘ)
    intro κ
    by_cases h : selSk (collapseGenDecoration D hS κ)
    · simp only [g, h, ite_true, norm_mul]
      exact mul_le_mul_of_nonneg_right (hΘ _) (norm_nonneg _)
    · simp only [g, h, ite_false, norm_zero]
      exact mul_nonneg ((norm_nonneg _).trans (hΘ (collapseGenDecoration D hS κ))) (norm_nonneg _)
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
        g (glueGenDecoration D hS κ ρ) = Θ κ * f (glueGenDecoration D hS κ ρ) := by
      intro ρ
      simp only [g, collapseGenDecoration_glue, hκ, ite_true]
    rw [tsum_congr hg, tsum_mul_left]
    congr 1
    apply Eq.trans (b := ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      ∫ τ, reducedDecorationIntegrandNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG (glueGenDecoration D hS κ ρ) τ
        ∂(fixMeasure (fixCore D hS fixG)))
    · exact tsum_congr (fun ρ => integral_gardenIntegrandNWR_reconstruction_fix D hS L γ δ A W Θs layer hLayer
        tt k₀ fixG hP (glueGenDecoration D hS κ ρ))
    · apply (tsum_integral_reduced_fixed_skeletonNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG hP Cw hCw hW
        CΘs hΘs κ hA).trans
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun τ => tsum_reduced_fixed_skeletonNWFR D hS L γ δ A W Θs layer hLayer tt k₀ fixG Cw hW CΘs hΘs κ τ hA))
  · simp only [hκ, ite_false]
    have hg : ∀ ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        g (glueGenDecoration D hS κ ρ) = 0 := by
      intro ρ
      simp only [g, collapseGenDecoration_glue, hκ, ite_false]
    rw [tsum_congr hg, tsum_zero]

/-- **The relaxed weighted native reduction with a skeleton multiplier and slot weights.** -/
theorem kernelNodeWR_native_reduction_selNWFMR (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (CΘs : ℝ) (hΘs : ∀ s k ρ, ‖Θs s k ρ‖ ≤ CΘs)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (Θ : GenDecoration S d n nfl → ℂ) (CΘ : ℝ)
    (hΘ : ∀ κ, ‖Θ κ‖ ≤ CΘ) :
    (coupling d L γ δ : ℂ) ^ (D.garden hS).order * (D.garden hS).zeta *
      (∑' κ : GenDecoration (D.garden hS) d n nfl,
        if selSk (collapseGenDecoration D hS κ) then
          Θ (collapseGenDecoration D hS κ) *
            ∫ τ, gardenIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ fixG κ τ ∂(fixMeasure fixG)
        else 0) =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then
          Θ κ * ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG κ.1 τ *
            ∏ s : ReplacementSlot S, nativeKernelValueNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ.1 τ fixG s
            ∂(fixMeasure (fixCore D hS fixG))
        else 0 := by
  let P := ∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s
  have hp : (coupling d L γ δ : ℂ) ^ (D.garden hS).order * (D.garden hS).zeta =
      ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * P := by
    change _ = ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) *
      (∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s)
    rw [Fintype.prod_sum_type]
    exact (kernelPrefactor_reconstruction D hS layer hLayer (coupling d L γ δ)).trans (mul_assoc _ _ _)
  rw [tsum_integral_sel_reductionNWFMR D hS L γ δ A W Θs layer hLayer tt k₀ fixG hP Cw hCw hW CΘs hΘs n nfl hA selSk
    Θ CΘ hΘ, hp, mul_assoc]
  apply congrArg (fun z => ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * z)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro κ
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    have key : P * ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG κ.1 τ *
          ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
            ∫ t, nativeKernelIntegrandNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ.1 τ fixG s ρ t
              ∂(fixMeasure (fixNative D hS fixG s)) ∂(fixMeasure (fixCore D hS fixG)) =
        ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG κ.1 τ *
          ∏ s : ReplacementSlot S, nativeKernelValueNWR D hS L γ δ A W Θs layer hLayer tt k₀ κ.1 τ fixG s
          ∂(fixMeasure (fixCore D hS fixG)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro τ
      have hv := nativeKernelValueNWR_prod_eq D hS L γ δ A W Θs layer hLayer tt k₀ κ.1 τ fixG
      exact (mul_left_comm P (coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG κ.1 τ) _).trans
        (congrArg (fun z => coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG κ.1 τ * z) hv).symm
    rw [← key]
    ring
  · simp only [hκ, ite_false, mul_zero]

end Reduction

end WaveTurbulence.Flower.MkSlotsB
