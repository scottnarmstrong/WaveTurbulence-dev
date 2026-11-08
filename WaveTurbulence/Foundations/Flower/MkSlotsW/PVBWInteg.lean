/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsW.PVBWModes
public import WaveTurbulence.Foundations.Flower.MkSlots.PVBInteg
public import WaveTurbulence.Foundations.Flower.MkUnitsL.WIntegW

/-! # B3s-HELPER: pinned VINE-B♯ with unit top weights (4/4) — integrability of the pinned outer integrand

Pinned copy of the measure-dependent part of `MkUnitsL/WIntegW`, exactly as `MkSlots/PVBInteg` is of
`Stage1WVine/WInteg`: the outer integrand `VineC.outerIntegrandM` of `outerValMμ` (with the top-weighted unit kernels
`unitKernelMGW Fs`) is integrable against ANY pinned measure `fixMeasure fixSb` on the `G_sb` times (the box of the
layer windows has pinned measure `≤ 1`), and the decoration sum of `outerValMμ` is absolutely summable for every
complex weight `‖Zw‖ ≤ 1`.  No condition on the pins is needed.  The unit-kernel bounds (`norm_unitKernelMG_leW`,
`measurable_unitKernelMG_clocksW`, `kerConstGW`, `norm_outerIntegrandMG_leW`) are reused by import, as is
`MkSlots.outerValMμ_eq_outerIntegrandM`.

* `measurable_outerIntegrandMGW`, `integrable_outerIntegrandMGW_fix`, `integral_norm_outerIntegrandMGW_le_fix`,
  `summable_outer_decorationsGW_fix`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlotsW
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB
open WaveTurbulence.Flower.MkSlots (fixMeasure fixMeasure_boxSb_le integrable_indicator_const_of_le_one
  integral_indicator_const_le_of_le_one)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW unitKernelMGW kerConstGW kerConstG_nonnegW
  norm_outerIntegrandMG_leW measurable_unitKernelMG_clocksW)

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
  {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}
variable (Φ : SpliceShape blk Gsb)

theorem measurable_outerIntegrandMGW (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) :
    Measurable (VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb
      amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z) := by
  unfold VineC.outerIntegrandM
  refine Measurable.indicator ?_ (Represents.measurableSet_splicedTimeDomain _ _ _)
  have h1 := Φ.measurable_sbInt hS hSb L γ δ base tt amp frq z
  have h2 : Measurable fun τ' : GBranch Gsb.tree → ℝ => ∏ j, unitKernelMGW blk D hS Fs L γ δ layer base j
      (modLam frq (Φ.route hS hSb) j) (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c))
      (fun c => base + latticePoint L (z.1 (Φ.hmom hd j c))) := by
    refine Finset.measurable_prod _ fun j _ => ?_
    simp_rw [MkUnitsL.UnitGW.unitKernelMG_clocksW Φ hd D hS Fs L γ δ layer base tt _ j]
    exact measurable_unitKernelMG_clocksW Φ RB D γ δ layer j _ _
  exact h1.mul h2

/-- **The pinned top-weighted outer integrand is integrable** (cf. `MkUnitsL.integrable_outerIntegrandMGW`), for any
pins. -/
theorem integrable_outerIntegrandMGW_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (D : ReconstructionData S) (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0)
    (fixSb : GBranch Gsb.tree → Option ℝ) :
    Integrable (VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp
      frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z)
      (fixMeasure fixSb) := by
  have hQ : MeasurableSet (boxSb (Gsb := Gsb) (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)) :=
    measurableSet_boxSb _
  refine Integrable.mono' (g := (boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
    (fun _ => ampBound hSb L base amp z * kerConstGW blk RB γ δ)) ?_
    (measurable_outerIntegrandMGW Φ RB hd D hSb γ δ layer tt amp frq z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ' => norm_outerIntegrandMG_leW Φ RB hd D hSb γ δ layer tt amp frq z τ')
  exact integrable_indicator_const_of_le_one hQ (fixMeasure_boxSb_le _ fixSb) _

theorem integral_norm_outerIntegrandMGW_le_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (D : ReconstructionData S) (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0)
    (fixSb : GBranch Gsb.tree → Option ℝ) :
    ∫ τ, ‖VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb
      amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z τ‖
        ∂(fixMeasure fixSb) ≤ ampBound hSb L base amp z * kerConstGW blk RB γ δ := by
  have hQ : MeasurableSet (boxSb (Gsb := Gsb) (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)) :=
    measurableSet_boxSb _
  have h1 := fixMeasure_boxSb_le (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) fixSb
  have hc : 0 ≤ ampBound hSb L base amp z * kerConstGW blk RB γ δ :=
    mul_nonneg (ampBound_nonneg _ _ _ _ _) (kerConstG_nonnegW RB γ δ (fun _ => base))
  refine (integral_mono (integrable_outerIntegrandMGW_fix Φ RB hd D hSb γ δ layer tt amp frq z fixSb).norm
    (integrable_indicator_const_of_le_one hQ h1 _)
    fun τ' => norm_outerIntegrandMG_leW Φ RB hd D hSb γ δ layer tt amp frq z τ').trans ?_
  exact integral_indicator_const_le_of_le_one hQ h1 hc

/-- **The pinned top-weighted decoration sum is absolutely summable** (cf.
`MkUnitsL.summable_outer_decorationsGW`), for any pins and any complex decoration weight bounded by one. -/
theorem summable_outer_decorationsGW_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (D : ReconstructionData S) (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z)
    (fixSb : GBranch Gsb.tree → Option ℝ) :
    Summable (fun z : GenDecoration Gsb d roots 0 =>
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * Zw z *
        ∫ τ, VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp
          frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z τ
            ∂(fixMeasure fixSb)) := by
  refine Summable.of_norm_bounded (hsum.mul_right (kerConstGW blk RB γ δ)) fun z => ?_
  have hint := integral_norm_outerIntegrandMGW_le_fix Φ RB hd D hSb γ δ layer tt amp frq z fixSb
  have he : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_splicedEpsilon_le _ _ _
  rw [norm_mul, norm_mul]
  calc _ ≤ 1 * 1 * ∫ τ, ‖VineC.outerIntegrandM Gsb L γ δ base roots tt
        (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base) z τ‖ ∂(fixMeasure fixSb) :=
        mul_le_mul (mul_le_mul he (hZw z) (norm_nonneg _) zero_le_one) (norm_integral_le_integral_norm _)
          (norm_nonneg _) (by norm_num)
    _ ≤ _ := by rw [one_mul, one_mul]; exact hint

end WaveTurbulence.Flower.MkSlotsW
