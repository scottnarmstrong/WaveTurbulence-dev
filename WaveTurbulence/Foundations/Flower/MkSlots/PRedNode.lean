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

/-- Every branch time in the open unit window of its layer. -/
def unitBox {w : ℕ} (LG : LayeredGarden w) : Set (GBranch LG.garden.tree → ℝ) :=
  Set.pi Set.univ fun b => Set.Ioo (LG.layer b.toNode : ℝ) (LG.layer b.toNode + 1)

theorem measurableSet_unitBox {w : ℕ} (LG : LayeredGarden w) : MeasurableSet (unitBox LG) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem kDomain_subset_unitBox {w : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) :
    kDomain LG up s ⊆ unitBox LG :=
  fun _ hτ b _ => ⟨(hτ b).1, (hτ b).2.1⟩

/-- A box of unit windows has `fixMeasure` at most one, whatever the pins. -/
theorem fixMeasure_pi_Ioo_le_one {ι : Type*} [Fintype ι] (fix : ι → Option ℝ) (a : ι → ℝ) :
    fixMeasure fix (Set.pi Set.univ fun i => Set.Ioo (a i) (a i + 1)) ≤ 1 := by
  rw [fixMeasure, Measure.pi_pi]
  refine Finset.prod_le_one fun i _ => ?_
  cases h : fix i with
  | none => simp [fixFactor, Real.volume_Ioo]
  | some v =>
    simp only [fixFactor, Option.elim]
    exact prob_le_one

theorem fixMeasure_unitBox_le_one {w : ℕ} (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ) :
    fixMeasure fix (unitBox LG) ≤ 1 :=
  fixMeasure_pi_Ioo_le_one fix fun b => (LG.layer b.toNode : ℝ)

/-! ### The literal summand under a pinned measure -/

section General

variable {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)

theorem measurable_kernelAllIntegrandN {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) : Measurable (kernelAllIntegrandN L γ δ LG A up s k₀ κ) := by
  unfold kernelAllIntegrandN
  exact (measurable_const.mul ((LGSpine.continuous_phaseProd L γ δ LG.garden _).measurable.indicator
    (LGSpine.measurableSet_kDomain LG up s))).mul measurable_const

theorem norm_kernelAllIntegrandN_le_unitBox {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : GBranch LG.garden.tree → ℝ) :
    ‖kernelAllIntegrandN L γ δ LG A up s k₀ κ τ‖ ≤
      (unitBox LG).indicator (fun _ => inputNodeMajorant L LG A k₀ κ) τ := by
  have he := abs_epsDec_le_one LG.garden κ.1
  have hprod : 0 ≤ inputNodeMajorant L LG A k₀ κ := Finset.prod_nonneg fun _ _ => abs_nonneg _
  unfold kernelAllIntegrandN
  rw [norm_mul, norm_mul, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  change |epsDec LG.garden κ.1| * ‖_‖ * inputNodeMajorant L LG A k₀ κ ≤ _
  by_cases hD : τ ∈ kDomain LG up s
  · rw [Set.indicator_of_mem hD, Set.indicator_of_mem (kDomain_subset_unitBox LG up s hD)]
    have hp : ‖phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1) τ‖ = 1 := by
      simp only [phaseProd, norm_prod]
      exact Finset.prod_eq_one fun b _ => Complex.norm_exp_ofReal_mul_I _
    rw [hp, mul_one]
    exact mul_le_of_le_one_left hprod he
  · rw [Set.indicator_of_notMem hD, norm_zero, mul_zero, zero_mul]
    exact Set.indicator_nonneg (fun _ _ => hprod) _

/-- **The pinned literal summand is integrable**, for every pin function. -/
theorem integrable_kernelAllIntegrandN_fix {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (fix : GBranch LG.garden.tree → Option ℝ) :
    Integrable (kernelAllIntegrandN L γ δ LG A up s k₀ κ) (fixMeasure fix) :=
  integrable_of_norm_le_indicator (measurableSet_unitBox LG) (fixMeasure_unitBox_le_one LG fix) _
    (measurable_kernelAllIntegrandN L γ δ LG A up s k₀ κ).aestronglyMeasurable
    (norm_kernelAllIntegrandN_le_unitBox L γ δ LG A up s k₀ κ)

theorem integral_norm_kernelAllIntegrandN_fix_le {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (fix : GBranch LG.garden.tree → Option ℝ) :
    ∫ τ, ‖kernelAllIntegrandN L γ δ LG A up s k₀ κ τ‖ ∂(fixMeasure fix) ≤ inputNodeMajorant L LG A k₀ κ :=
  integral_norm_le_of_norm_le_indicator (measurableSet_unitBox LG) (fixMeasure_unitBox_le_one LG fix) _
    (Finset.prod_nonneg fun _ _ => abs_nonneg _) (norm_kernelAllIntegrandN_le_unitBox L γ δ LG A up s k₀ κ)

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

theorem integral_kernelAllIntegrandNW_fix {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (fix : GBranch LG.garden.tree → Option ℝ) :
    (∫ τ, kernelAllIntegrandNW L γ δ LG A m up s k₀ κ τ ∂(fixMeasure fix)) =
      m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          (∫ τ, (kDomain LG up s).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ
            ∂(fixMeasure fix)) *
          ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) := by
  unfold kernelAllIntegrandNW kernelAllIntegrandN
  rw [integral_const_mul, integral_mul_const, integral_const_mul]

theorem kernelNodeWF_eq_tsum_integral_all (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelNodeWF L γ δ LG A m up s k₀ nroot nfl fix =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl,
          ∫ τ, kernelAllIntegrandNW L γ δ LG A m up s k₀ κ τ ∂(fixMeasure fix) := by
  unfold kernelNodeWF
  congr 1
  exact tsum_congr fun κ => (integral_kernelAllIntegrandNW_fix L γ δ LG A m up s k₀ κ fix).symm

theorem integrable_kernelAllIntegrandNW_fix {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (fix : GBranch LG.garden.tree → Option ℝ) :
    Integrable (kernelAllIntegrandNW L γ δ LG A m up s k₀ κ) (fixMeasure fix) :=
  (integrable_kernelAllIntegrandN_fix L γ δ LG A up s k₀ κ fix).const_mul _

theorem integral_norm_kernelAllIntegrandNW_fix_le (Mm : ℝ) (hm : ∀ k, ‖m k‖ ≤ Mm)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    (∫ τ, ‖kernelAllIntegrandNW L γ δ LG A m up s k₀ κ τ‖ ∂(fixMeasure fix)) ≤
      Mm * inputNodeMajorant L LG A k₀ κ := by
  unfold kernelAllIntegrandNW
  simp_rw [norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul (hm _) (integral_norm_kernelAllIntegrandN_fix_le L γ δ LG A up s k₀ κ fix)
    (integral_nonneg fun _ => norm_nonneg _) ((norm_nonneg _).trans (hm 0))

theorem summable_integral_norm_kernelAllIntegrandNW_fix (Mm : ℝ) (hm : ∀ k, ‖m k‖ ≤ Mm)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hA : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      ∫ τ, ‖kernelAllIntegrandNW L γ δ LG A m up s k₀ κ τ‖ ∂(fixMeasure fix)) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (fun κ => integral_norm_kernelAllIntegrandNW_fix_le L γ δ LG A m up s k₀ Mm hm κ fix)
    ((summable_inputNodeMajorant L LG A k₀ nroot nfl hlone hA).mul_left Mm)

theorem summable_integral_kernelAllIntegrandNW_fix (Mm : ℝ) (hm : ∀ k, ‖m k‖ ≤ Mm)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hA : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      ∫ τ, kernelAllIntegrandNW L γ δ LG A m up s k₀ κ τ ∂(fixMeasure fix)) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun κ => norm_integral_le_integral_norm (kernelAllIntegrandNW L γ δ LG A m up s k₀ κ))
    (summable_integral_norm_kernelAllIntegrandNW_fix L γ δ LG A m up s k₀ Mm hm nroot nfl hlone hA fix)

end General

end WaveTurbulence.Flower.MkSlots
