/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB15
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: `hint` and `hsm` of VINE-C's class sum, for the unit kernel `unitKernelM`
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineB
  WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C
  WaveTurbulence.VineEstS5C.Cont MeasureTheory Filter Topology

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

theorem integrable_outerIntegrandM (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0) :
    Integrable (VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp
      frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelM blk D hS L γ δ h layer hLayer base) z) := by
  have hmeas : Measurable (VineC.outerIntegrandM Gsb L γ δ base roots tt
      (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
      (unitKernelM blk D hS L γ δ h layer hLayer base) z) := by
    unfold VineC.outerIntegrandM
    refine Measurable.indicator ?_ (measurableSet_splicedTimeDomain _ _ _)
    have h1 := Φ.measurable_sbInt hS hSb L γ δ base tt amp frq z
    have h2 : Measurable fun τ' : GBranch Gsb.tree → ℝ => ∏ j, unitKernelM blk D hS L γ δ h layer hLayer base j
        (modLam frq (Φ.route hS hSb) j) (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c))
        (fun c => base + latticePoint L (z.1 (Φ.hmom hd j c))) := by
      refine Finset.measurable_prod _ fun j _ => ?_
      simp_rw [Φ.unitKernelM_clocks hd D hS L γ δ h layer hLayer base tt _ j]
      exact measurable_unitKernelM_clocks Φ D hS hL γ δ h layer hLayer base j (hF j) _ _
    exact h1.mul h2
  have hQ : MeasurableSet (boxSb (Gsb := Gsb) (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)) :=
    measurableSet_boxSb _
  refine Integrable.mono' (g := (boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
    (fun _ => ampBound hSb L base amp z * kerConst blk D hS L γ δ h layer hLayer base)) ?_
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun τ' =>
      norm_outerIntegrandM_le Φ hd D hS hSb hL γ δ base h layer hLayer tt amp frq hF z τ')
  exact (integrable_indicator_iff hQ).2 (integrableOn_const (by rw [volume_boxSb]; exact ENNReal.one_ne_top))

theorem summable_outer_decorations (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (Zw : GenDecoration Gsb d roots 0 → ℝ) (hZw : ∀ z, |Zw z| ≤ 1)
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z) :
    Summable (fun z : GenDecoration Gsb d roots 0 =>
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Zw z : ℂ) *
        ∫ τ, VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp
          frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelM blk D hS L γ δ h layer hLayer base) z τ) := by
  refine Summable.of_norm_bounded (hsum.mul_right (kerConst blk D hS L γ δ h layer hLayer base)) fun z => ?_
  have hQ : MeasurableSet (boxSb (Gsb := Gsb) (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)) :=
    measurableSet_boxSb _
  have hint : ∫ τ, ‖VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp
      frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelM blk D hS L γ δ h layer hLayer base) z τ‖ ≤
      ampBound hSb L base amp z * kerConst blk D hS L γ δ h layer hLayer base := by
    have hg : Integrable ((boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
        (fun _ => ampBound hSb L base amp z * kerConst blk D hS L γ δ h layer hLayer base)) :=
      (integrable_indicator_iff hQ).2 (integrableOn_const (by rw [volume_boxSb]; exact ENNReal.one_ne_top))
    refine (integral_mono (integrable_outerIntegrandM Φ hd D hS hSb hL γ δ base h layer hLayer tt amp frq hF z).norm hg
      fun τ' => norm_outerIntegrandM_le Φ hd D hS hSb hL γ δ base h layer hLayer tt amp frq hF z τ').trans_eq ?_
    rw [integral_indicator_const _ hQ, Measure.real, volume_boxSb]
    simp
  have he : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_splicedEpsilon_le _ _ _
  have hzw : ‖(Zw z : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hZw z
  rw [norm_mul, norm_mul]
  calc _ ≤ 1 * 1 * ∫ τ, ‖VineC.outerIntegrandM Gsb L γ δ base roots tt
        (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelM blk D hS L γ δ h layer hLayer base) z τ‖ :=
        mul_le_mul (mul_le_mul he hzw (norm_nonneg _) zero_le_one) (norm_integral_le_integral_norm _)
          (norm_nonneg _) (by norm_num)
    _ ≤ _ := by rw [one_mul, one_mul]; exact hint

end WaveTurbulence.Represents
