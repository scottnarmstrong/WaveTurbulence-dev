/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.FixMeasure
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.WNode

/-! # B3s MK-SLOTS: pinned node-weighted kernels (PRED, part 1)

The pinned twin of `Stage1WNoVine.WNode` (general part): the time integral of a garden kernel is taken against
`fixMeasure fix` (Lebesgue at the free branches, Dirac masses at the pinned values) instead of the flower-parent
slice `phaseIntegral`.  The integrand is the same pointwise function `kernelAllIntegrandN`; only the measure
changes.  Its support lies in the unit layer box, whose `fixMeasure` is at most one for EVERY pin function, so the
pinned integrals are integrable and bounded by the input-leaf majorant with no hypothesis on the pins.

* `integrable_of_norm_le_indicator`, `integral_norm_le_of_norm_le_indicator`: bounded functions supported on a set of
  measure at most one;
* `unitBox`, `fixMeasure_unitBox_le_one`, `norm_kernelAllIntegrandN_le_unitBox`;
* `integrable_kernelAllIntegrandN_fix`, `integral_norm_kernelAllIntegrandN_fix_le`;
* `kernelNodeWF` and `kernelNodeWF_none` (no pins: `WNode.kernelNodeW`), `kernelNodeWF_eq_tsum_integral_all`,
  `summable_integral_kernelAllIntegrandNW_fix`. -/

/- PLAN (PRed*: the pinned copy of `Stage1WNoVine.{WNode, WRed, WLeaves}`).
 1. `PRedNode` (this file, general layered garden): the measure-agnostic integrability/L¹ bound of the literal
    summand `kernelAllIntegrandN` under `fixMeasure fix` (support in the unit layer box, `fixMeasure ≤ 1` there),
    the pinned weighted kernel `kernelNodeWF`, its literal-summand form, summability over decorations, and the
    unpinned instance `kernelNodeWF … (fun _ => none) = kernelNodeW …` (no flower parents).
 2. `PRedRed` (reconstructed garden): the pinned weighted native kernels (`nativeKernelValueNWF`, pins
    `fixNative D hS fixG s`), the reduced integrand with pinned native integrals, its integrability and L¹ bound
    from the pinned split (`RedFix.measurePreserving_sourceNativeTimeSplit_fix`), and the pinned weighted raw and
    native reductions (`tsum_integral_sel_reductionNWF`, `kernelNodeWF_native_reduction_selNWF`).
 3. `PRedLeaves`: `kernelLeavesSelNWF` (+ unpinned instance), `slotFnNWF` (+ unpinned instance), `prod_slotFnNWF`,
    and the deliverable `kernelLeaves_skeleton_reduction_selNWF` (core integral against `fixMeasure (fixCore …)`).
 No hypothesis on the pins is needed anywhere: every pinned integrand is bounded and supported in the unit box. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlots
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine

/-! ### Bounded functions supported on a set of measure at most one -/

theorem integrable_of_norm_le_indicator {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : α → E} {B : Set α} (hB : MeasurableSet B) (hμB : μ B ≤ 1) (M : ℝ)
    (hF : AEStronglyMeasurable F μ) (hle : ∀ x, ‖F x‖ ≤ B.indicator (fun _ => M) x) : Integrable F μ := by
  have hi : Integrable (B.indicator (fun _ => M)) μ :=
    (integrable_indicator_iff hB).2 (integrableOn_const (hμB.trans_lt ENNReal.one_lt_top).ne)
  exact hi.mono' hF (Filter.Eventually.of_forall hle)

theorem integral_norm_le_of_norm_le_indicator {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : α → E} {B : Set α} (hB : MeasurableSet B) (hμB : μ B ≤ 1) (M : ℝ) (hM : 0 ≤ M)
    (hle : ∀ x, ‖F x‖ ≤ B.indicator (fun _ => M) x) : ∫ x, ‖F x‖ ∂μ ≤ M := by
  have hi : Integrable (B.indicator (fun _ => M)) μ :=
    (integrable_indicator_iff hB).2 (integrableOn_const (hμB.trans_lt ENNReal.one_lt_top).ne)
  have h1 : ∫ x, ‖F x‖ ∂μ ≤ ∫ x, B.indicator (fun _ => M) x ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hi
      (Filter.Eventually.of_forall hle)
  have hr : μ.real B ≤ 1 := by
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hμB)
  rw [integral_indicator_const M hB, smul_eq_mul] at h1
  exact h1.trans (mul_le_of_le_one_left hM hr)

/-! ### The unit layer box -/

/-! ### The literal summand under a pinned measure -/

section General

variable {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)

/-! ### The pinned weighted kernel -/

/-- **The pinned weighted garden kernel**: `WNode.kernelNodeW` with the phase integral `phaseIntegral … (kDomain
LG up s) s …` replaced by the integral of the same indicator against `fixMeasure fix`. -/
def kernelNodeWF (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (fix : GBranch LG.garden.tree → Option ℝ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          (∫ τ, (kDomain LG up s).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ
            ∂(fixMeasure fix)) *
          ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))

/-- Without pins and without flower parents the pinned phase integral is `phaseIntegral`. -/
theorem integral_phase_fixMeasure_none (hG : ∀ b, ¬ LG.garden.IsFlowerParent b) (k : GNode LG.garden.tree → Mom d) :
    ∫ τ, (kDomain LG up s).indicator (phaseProd L γ δ LG.garden k) τ ∂(fixMeasure fun _ => none) =
      phaseIntegral L γ δ LG.garden (kDomain LG up s) s k := by
  rw [fixMeasure_none, phaseIntegral,
    ← (measurePreserving_allTimeEquiv LG.garden hG).integral_comp' ((kDomain LG up s).indicator _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  dsimp only
  rw [extendTime_eq_allTimeEquiv LG.garden hG]

/-- **No pins: the pinned weighted kernel is `WNode.kernelNodeW`.** -/
theorem kernelNodeWF_none (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelNodeWF L γ δ LG A m up s k₀ nroot nfl (fun _ => none) = kernelNodeW L γ δ LG A m up s k₀ nroot nfl := by
  unfold kernelNodeWF kernelNodeW
  congr 1
  refine tsum_congr fun κ => ?_
  rw [integral_phase_fixMeasure_none L γ δ LG up s hG]

end General

end WaveTurbulence.Flower.MkSlots
