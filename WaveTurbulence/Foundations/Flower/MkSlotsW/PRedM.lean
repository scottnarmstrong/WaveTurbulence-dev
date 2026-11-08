/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PRedLeaves

/-! # B3s-HELPER: the pinned weighted skeleton reduction with a skeleton multiplier

The pinned twin of `MkUnitsL/RedL` (B3-2's weighted skeleton reduction with a bounded multiplier `Θ` of the collapsed
skeleton decoration), built on B3s's pinned reduction `MkSlots/PRedRed`, `MkSlots/PRedLeaves`.  The multiplier
`Θ (collapseGenDecoration D hS κ)` is constant on every fiber of the collapse, so every step is the pinned step of
`PRedRed` times `Θ`, exactly as `RedL`'s steps are `Stage1WNoVine.WRed`'s times `Θ`.

The leaf kernel of `PRedLeaves` (`MkSlots.kernelLeavesSelNWF`) carries a weight `m` of the MOMENTA `k` of the
reconstructed garden; a skeleton multiplier `Θ (collapse κ)` is a function of the DECORATION `κ` (reading it as a
function of `k` would mean inverting `cosetDecoration`).  So the left-hand side is stated with an explicit extra
decoration weight `Θg` (`kernelLeavesSelNWFM`; `Θg = 1` is `kernelLeavesSelNWF`, `kernelLeavesSelNWFM_one`), as
`RedL` states its left-hand side through `valueSelW`'s decoration weight.

* `tsum_integral_sel_reductionNWFM`, `kernelNodeWF_native_reduction_selNWFM` (`PRedRed`'s steps with `Θ`);
* `kernelLeavesSelNWFM`, `kernelLeavesSelNWFM_one`, `kernelLeavesSelNWFM_eq_integral`;
* **`kernelLeaves_skeleton_reduction_selNWFM`**; `kernelLeaves_skeleton_reduction_selNWFM_one` (`Θ = 1`: the statement
  of `MkSlots.kernelLeaves_skeleton_reduction_selNWF`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlotsW
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.MkSlots WaveTurbulence.LGSpine

/-! ### The pinned reduction steps with a skeleton multiplier -/

section Reduction

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (fixG : GBranch (D.forest hS) → Option ℝ)

/-- The pinned weighted raw reduction with a skeleton multiplier (`MkSlots.tsum_integral_sel_reductionNWF` with
`RedL`'s `Θ`). -/
theorem tsum_integral_sel_reductionNWFM (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (Θ : GenDecoration S d n nfl → ℂ) (CΘ : ℝ)
    (hΘ : ∀ κ, ‖Θ κ‖ ≤ CΘ) :
    (∑' κ : GenDecoration (D.garden hS) d n nfl,
      if selSk (collapseGenDecoration D hS κ) then
        Θ (collapseGenDecoration D hS κ) *
          ∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
            (fun b => tt b.1.1) 0 k₀ κ τ ∂(fixMeasure fixG)
      else 0) =
      ∑' κ : GenDecoration S d n nfl, if selSk κ then
        Θ κ * ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
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

/-- **The pinned weighted native reduction with a skeleton multiplier** (`MkSlots.kernelNodeWF_native_reduction_selNWF`
with `RedL`'s `Θ`). -/
theorem kernelNodeWF_native_reduction_selNWFM (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (Θ : GenDecoration S d n nfl → ℂ) (CΘ : ℝ)
    (hΘ : ∀ κ, ‖Θ κ‖ ≤ CΘ) :
    (coupling d L γ δ : ℂ) ^ (D.garden hS).order * (D.garden hS).zeta *
      (∑' κ : GenDecoration (D.garden hS) d n nfl,
        if selSk (collapseGenDecoration D hS κ) then
          Θ (collapseGenDecoration D hS κ) *
            ∫ τ, kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
              (fun b => tt b.1.1) 0 k₀ κ τ ∂(fixMeasure fixG)
        else 0) =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then
          Θ κ * ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
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
  rw [tsum_integral_sel_reductionNWFM D hS L γ δ A W layer hLayer tt k₀ fixG Cw hCw hW n nfl hA selSk Θ CΘ hΘ, hp,
    mul_assoc]
  apply congrArg (fun z => ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * z)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro κ
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    have key : P * ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
          ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
            ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ.1 τ s ρ t
              ∂(fixMeasure (fixNative D hS fixG s))
          ∂(fixMeasure (fixCore D hS fixG)) =
        ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
          ∏ s : ReplacementSlot S, nativeKernelValueNWF D hS L γ δ A W layer hLayer tt k₀ κ.1 τ fixG s
          ∂(fixMeasure (fixCore D hS fixG)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro τ
      have hv := nativeKernelValueNWF_prod_eq D hS L γ δ A W layer hLayer tt k₀ fixG κ.1 τ
      exact (mul_left_comm P (coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ) _).trans
        (congrArg (fun z => coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ * z) hv).symm
    rw [← key]
    ring
  · simp only [hκ, ite_false, mul_zero]

end Reduction

/-! ### The pinned weighted leaf kernel with a decoration multiplier -/

/-- **The pinned decoration-restricted weighted leaf kernel with a decoration multiplier**: `MkSlots.kernelLeavesSelNWF`
with every selected summand multiplied by `Θg κ`. -/
def kernelLeavesSelNWFM {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (Θg : GenDecoration LG.garden d nroot nfl → ℂ) (fix : GBranch LG.garden.tree → Option ℝ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      if sel κ then Θg κ * (m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          (∫ τ, (kDomain LG up s).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ
            ∂(fixMeasure fix)) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)))
      else 0

/-- **The multiplier `1`**: `kernelLeavesSelNWFM` is `MkSlots.kernelLeavesSelNWF`. -/
theorem kernelLeavesSelNWFM_one {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelLeavesSelNWFM L γ δ LG H up s k₀ nroot nfl sel m (fun _ => 1) fix =
      kernelLeavesSelNWF L γ δ LG H up s k₀ nroot nfl sel m fix := by
  unfold kernelLeavesSelNWFM kernelLeavesSelNWF
  simp only [one_mul]

theorem kernelLeavesSelNWFM_eq_integral {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (Θg : GenDecoration LG.garden d nroot nfl → ℂ) (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelLeavesSelNWFM L γ δ LG H up s k₀ nroot nfl sel m Θg fix =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, if sel κ then
          Θg κ * ∫ τ, kernelAllIntegrandNW L γ δ LG (fun a => H a.1) m up s k₀ κ τ ∂(fixMeasure fix) else 0 := by
  unfold kernelLeavesSelNWFM
  congr 1
  refine tsum_congr fun κ => ?_
  by_cases h : sel κ
  · simp only [h, ite_true]
    rw [integral_kernelAllIntegrandNW_fix L γ δ LG (fun a => H a.1) m up s k₀ κ fix]
    rfl
  · simp only [h, ite_false]

/-! ### The pinned weighted leafwise skeleton reduction with a skeleton multiplier -/

/-- The pinned weighted leafwise skeleton reduction with a skeleton multiplier, slot product in native form. -/
theorem kernelLeaves_skeleton_reduction_selNWFM_native {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (fixG : GBranch (D.forest hS) → Option ℝ)
    (Θ : GenDecoration S d n nfl → ℂ) (CΘ : ℝ) (hΘ : ∀ κ, ‖Θ κ‖ ≤ CΘ) :
    kernelLeavesSelNWFM L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀ n nfl
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fun k => ∏ z, W z (k z))
        (fun κ => Θ (collapseGenDecoration D hS κ)) fixG =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              (reducedStarProductLeavesNWF D hS L γ δ H W layer hLayer tt k₀ κ.1 τ fixG * Θ κ)) τ
            ∂(fixMeasure (fixCore D hS fixG)) else 0 := by
  rw [kernelLeavesSelNWFM_eq_integral L γ δ (layeredReconstruction D hS layer hLayer) H _ _ k₀ n nfl _ _ _ fixG]
  refine (kernelNodeWF_native_reduction_selNWFM D hS L γ δ (fun a => H a.1) W layer hLayer tt k₀ fixG
    Cw hCw hW n nfl hH selSk Θ CΘ hΘ).trans ?_
  apply congrArg (fun z => ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * z)
  refine tsum_congr fun κ => ?_
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    rw [← integral_core_mul_measure D hS L γ δ layer tt k₀ κ.1 _ _, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    unfold reducedStarProductLeavesNWF
    ring
  · simp only [hκ, ite_false]

/-- **The pinned weighted skeleton reduction with a skeleton multiplier.**  For ANY pins `fixG` on the branches of the
reconstructed garden and a bounded multiplier `Θ` of the skeleton decoration, the pinned weighted leaf kernel of the
reconstruction with the decoration multiplier `Θ (collapse κ)` is the skeleton value of
`MkSlots.kernelLeaves_skeleton_reduction_selNWF` with `Θ κ` multiplied inside the core integrand (as `RedL` multiplies
`Θ κ`): the core integral is against `fixMeasure (fixCore D hS fixG)`, the slot kernels are the pinned
`slotFnNWF … fixG`. -/
theorem kernelLeaves_skeleton_reduction_selNWFM {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (fixG : GBranch (D.forest hS) → Option ℝ)
    (Θ : GenDecoration S d n nfl → ℂ) (CΘ : ℝ) (hΘ : ∀ κ, ‖Θ κ‖ ≤ CΘ) :
    kernelLeavesSelNWFM L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀ n nfl
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fun k => ∏ z, W z (k z))
        (fun κ => Θ (collapseGenDecoration D hS κ)) fixG =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              ((∏ s, slotFnNWF D hS L γ δ H W layer hLayer fixG s (Represents.slotTs hS tt τ s)
                (k₀ + latticePoint L (κ.1 (Represents.slotNode hS s)))) * Θ κ)) τ
            ∂(fixMeasure (fixCore D hS fixG))
          else 0 := by
  simp_rw [prod_slotFnNWF D hS L γ δ H W layer hLayer fixG tt k₀]
  exact kernelLeaves_skeleton_reduction_selNWFM_native D hS L γ δ H W Cw hCw hW layer hLayer tt k₀ n nfl hH selSk
    fixG Θ CΘ hΘ

/-- **`Θ = 1` recovers `MkSlots.kernelLeaves_skeleton_reduction_selNWF`** (statement for statement). -/
theorem kernelLeaves_skeleton_reduction_selNWFM_one {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (fixG : GBranch (D.forest hS) → Option ℝ) :
    kernelLeavesSelNWF L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀ n nfl
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fun k => ∏ z, W z (k z)) fixG =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              ∏ s, slotFnNWF D hS L γ δ H W layer hLayer fixG s (Represents.slotTs hS tt τ s)
                (k₀ + latticePoint L (κ.1 (Represents.slotNode hS s)))) τ ∂(fixMeasure (fixCore D hS fixG))
          else 0 := by
  refine (kernelLeavesSelNWFM_one L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀ n nfl
    (fun κ => selSk (collapseGenDecoration D hS κ)) (fun k => ∏ z, W z (k z)) fixG).symm.trans
    ((kernelLeaves_skeleton_reduction_selNWFM D hS L γ δ H W Cw hCw hW layer hLayer tt k₀ n nfl hH selSk fixG
      (fun _ => 1) 1 (fun _ => by simp)).trans ?_)
  simp only [mul_one]

end WaveTurbulence.Flower.MkSlotsW
