/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.RegionL
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Core1

/-! # MK-UNITS-L (B3-2): the weighted skeleton reduction with a skeleton multiplier

Stage1WNoVine's node-weighted skeleton reduction (`tsum_integral_sel_reductionNW`, `kernelNodeW_native_reduction_sel`,
`kernelLeaves_skeleton_reduction_selNW`, `valueSelW_skeleton_reduction`) with an extra bounded multiplier `Θ` of the
collapsed (skeleton) decoration: the decoration weight `fwWeight · Θ(collapse κ)` of the reconstruction reduces to the
skeleton sum with `Θ κ` in the skeleton integrand.  The selection is the special case already treated there; the
multiplier is constant on every fiber of the collapse, so each step is Stage1WNoVine's step times `Θ`.

* `tsum_integral_sel_reductionNWM`, `kernelNodeW_native_reduction_selM`, `valueSelW_skeleton_reductionM`.
* `skelValW_slotFWW`: the skeleton value of the weighted slot family with top weights is that skeleton sum at
  `Θ = topW` (Stage1WVine's `skelVal_slotFW`).

Adapted from `Flower/Stage1WNoVine/WRed.lean`, `WLeaves.lean`, `Core1.lean`, `Flower/Stage1WVine/WMember1.lean` (see
`COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkUnitsL
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.Stage1W WaveTurbulence.Represents
open WaveTurbulence.VineSpaceK (nodeWeight)

section Reduction

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d)

/-- The weighted raw reduction with a skeleton multiplier (Stage1WNoVine's `tsum_integral_sel_reductionNW`). -/
theorem tsum_integral_sel_reductionNWM (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (Θ : GenDecoration S d n nfl → ℂ) (CΘ : ℝ) (hΘ : ∀ κ, ‖Θ κ‖ ≤ CΘ) :
    (∑' κ : GenDecoration (D.garden hS) d n nfl,
      if selSk (collapseGenDecoration D hS κ) then
        Θ (collapseGenDecoration D hS κ) *
          ∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
            (fun b => tt b.1.1) 0 k₀ κ τ
      else 0) =
      ∑' κ : GenDecoration S d n nfl, if selSk κ then
        Θ κ * ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
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

/-- **The weighted native reduction with a skeleton multiplier** (Stage1WNoVine's
`kernelNodeW_native_reduction_sel`). -/
theorem kernelNodeW_native_reduction_selM (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (Θ : GenDecoration S d n nfl → ℂ) (CΘ : ℝ) (hΘ : ∀ κ, ‖Θ κ‖ ≤ CΘ) :
    (coupling d L γ δ : ℂ) ^ (D.garden hS).order * (D.garden hS).zeta *
      (∑' κ : GenDecoration (D.garden hS) d n nfl,
        if selSk (collapseGenDecoration D hS κ) then
          Θ (collapseGenDecoration D hS κ) *
            ∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
              (fun b => tt b.1.1) 0 k₀ κ τ
        else 0) =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then
          Θ κ * ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
            ∏ s : ReplacementSlot S, nativeKernelValueNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s
        else 0 := by
  let P := ∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s
  have hp : (coupling d L γ δ : ℂ) ^ (D.garden hS).order * (D.garden hS).zeta =
      ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * P := by
    change _ = ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) *
      (∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s)
    rw [Fintype.prod_sum_type]
    exact (kernelPrefactor_reconstruction D hS layer hLayer (coupling d L γ δ)).trans (mul_assoc _ _ _)
  rw [tsum_integral_sel_reductionNWM D hS L γ δ A W layer hLayer tt k₀ Cw hCw hW n nfl hA selSk Θ CΘ hΘ, hp,
    mul_assoc]
  apply congrArg (fun z => ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * z)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro κ
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    have key : P * ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
          ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
            ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s ρ t =
        ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
          ∏ s : ReplacementSlot S, nativeKernelValueNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro τ
      have hv := nativeKernelValueNW_prod_eq D hS L γ δ A W layer hLayer tt k₀ κ.1 τ
      exact (mul_left_comm P (coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ) _).trans
        (congrArg (fun z => coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ * z) hv).symm
    rw [← key]
    ring
  · simp only [hκ, ite_false, mul_zero]

end Reduction

/-- **The weighted value of a reconstruction with a skeleton multiplier is the skeleton sum with the multiplier in
the skeleton integrand** (Stage1WNoVine's `valueSelW_skeleton_reduction`). -/
theorem valueSelW_skeleton_reductionM {P : WTParams} {R : ℕ} (F : LeafFamily P (2 * R))
    {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hctrl : F.Controlled (layeredReconstruction D hS layer hLayer))
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration S P.d roots 0 → Prop)
    (p : ℕ) (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (Θ : GenDecoration S P.d roots 0 → ℂ) (CΘ : ℝ) (hΘ : ∀ κ, ‖Θ κ‖ ≤ CΘ) :
    valueSelW F tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ))
        (fun κ => fwWeight p g base (layeredReconstruction D hS layer hLayer) κ * Θ (collapseGenDecoration D hS κ)) =
      @Finset.sum (F.ι (layeredReconstruction D hS layer hLayer)) ℂ _
        (@Finset.univ _ (F.fin (layeredReconstruction D hS layer hLayer))) fun i =>
        ((F.sign (layeredReconstruction D hS layer hLayer) i : ℝ) : ℂ) *
          ((coupling P.d P.L P.γ P.δ : ℂ) ^ S.order * S.zeta *
            ∑' κ : GenDecoration S P.d roots 0, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
              (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
                (fun τ => phaseProd P.L P.γ P.δ S (cosetDecoration S P.L base κ.1) τ *
                  (reducedStarProductLeavesNW D hS P.L P.γ P.δ (F.H (layeredReconstruction D hS layer hLayer) i)
                    (fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer tt base κ.1 τ * Θ κ)) τ
            else 0) := by
  unfold valueSelW
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hint : ∀ κ : GenDecoration (D.garden hS) P.d roots 0,
      (if selSk (collapseGenDecoration D hS κ) then
        (fwWeight p g base (layeredReconstruction D hS layer hLayer) κ * Θ (collapseGenDecoration D hS κ)) *
          kernelLeavesTerm P.L P.γ P.δ (layeredReconstruction D hS layer hLayer)
            (F.H (layeredReconstruction D hS layer hLayer) i) (fun b => tt b.1.1) 0 base κ
        else 0) =
      if selSk (collapseGenDecoration D hS κ) then
        Θ (collapseGenDecoration D hS κ) *
          ∫ τ, kernelAllIntegrandNW P.L P.γ P.δ (layeredReconstruction D hS layer hLayer)
            (fun a => F.H (layeredReconstruction D hS layer hLayer) i a.1)
            (fun k => ∏ z, fwNode (layeredReconstruction D hS layer hLayer) p g z (k z)) (fun b => tt b.1.1) 0 base κ τ
        else 0 := by
    intro κ
    by_cases h : selSk (collapseGenDecoration D hS κ)
    · simp only [h, ite_true]
      rw [integral_kernelAllIntegrandNW P.L P.γ P.δ (layeredReconstruction D hS layer hLayer) _ _ _ 0 base
        (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) κ]
      rw [mul_comm _ (Θ (collapseGenDecoration D hS κ)), mul_assoc]
      rfl
    · simp only [h, ite_false]
  unfold kernelLeavesSelW
  refine Eq.trans (congrArg (fun z => (coupling P.d P.L P.γ P.δ : ℂ) ^ (D.garden hS).order * (D.garden hS).zeta * z)
    (tsum_congr hint)) ?_
  refine (kernelNodeW_native_reduction_selM D hS P.L P.γ P.δ
    (fun a => F.H (layeredReconstruction D hS layer hLayer) i a.1)
    (fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer tt base cψ (by linarith)
    (norm_fwNode_le (layeredReconstruction D hS layer hLayer) p g cψ hc hg) roots 0
    ((hctrl i).summable_coset hd hL base) selSk Θ CΘ hΘ).trans ?_
  apply congrArg (fun z => ((coupling P.d P.L P.γ P.δ : ℂ) ^ S.order * S.zeta) * z)
  refine tsum_congr fun κ => ?_
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    rw [← integral_core_mul D hS P.L P.γ P.δ layer tt base κ.1, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    unfold reducedStarProductLeavesNW
    ring
  · simp only [hκ, ite_false]

end WaveTurbulence.Flower.MkUnitsL
