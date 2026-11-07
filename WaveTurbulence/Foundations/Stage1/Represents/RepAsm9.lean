/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm8
import Mathlib.Tactic

/-!
# S2 REPRESENTS: measurability and integrability bounds of the assembled summand
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

variable {w d : ℕ} {S : Garden w} (A : AsmCtx S d)

theorem continuous_phaseProd {G : Garden w} (L γ δ : ℝ) (k : GNode G.tree → Mom d) :
    Continuous (fun τ : GBranch G.tree → ℝ => phaseProd L γ δ G k τ) := by
  unfold phaseProd
  refine continuous_finsetProd _ fun b _ => ?_
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    (continuous_const.mul (continuous_apply b))).mul continuous_const)

theorem continuous_timeFac (fam : SlotFam S d) (hS : S.IsPlain) (ξ : XiT fam) :
    Continuous (fun τ : GBranch S.tree → ℝ => timeFac fam hS ξ τ) := by
  unfold timeFac
  refine continuous_finsetProd _ fun b _ => ?_
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    (continuous_const.mul (continuous_apply b))).mul continuous_const)

theorem AsmCtx.meas_gI (ξ : XiT A.fam) (κ : GenDecoration S d A.roots 0) :
    AEStronglyMeasurable (A.gI ξ κ) volume := by
  classical
  unfold AsmCtx.gI
  refine aestronglyMeasurable_const.mul ?_
  refine (Continuous.aestronglyMeasurable ?_).indicator (measurableSet_splicedTimeDomain S A.layer0 A.tt)
  exact (continuous_phaseProd _ _ _ _).mul (continuous_timeFac A.fam A.hS ξ)

theorem AsmCtx.norm_gI_le (ξ : XiT A.fam) (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    ‖A.gI ξ κ τ‖ ≤ (splicedTimeDomain S A.layer0 A.tt).indicator
      (fun _ => ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ * ‖A.E ξ κ‖) τ := by
  classical
  unfold AsmCtx.gI
  by_cases hτ : τ ∈ splicedTimeDomain S A.layer0 A.tt
  · simp only [Set.indicator_of_mem hτ]
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖(if A.selSk κ then ((epsDec S κ.1 : ℝ) : ℂ) else 0)‖ ≤ 1 := by
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs]; exact norm_epsDec_le _
      · simp
    have h2 : ‖phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * timeFac A.fam A.hS ξ τ‖ = 1 := by
      rw [norm_mul, norm_phaseProd_le, one_mul]
      unfold timeFac
      rw [norm_prod]
      exact Finset.prod_eq_one fun u _ => Complex.norm_exp_ofReal_mul_I _
    calc ‖(if A.selSk κ then ((epsDec S κ.1 : ℝ) : ℂ) else 0)‖ *
          (‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ * ‖A.E ξ κ‖) *
          ‖phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * timeFac A.fam A.hS ξ τ‖
        = ‖(if A.selSk κ then ((epsDec S κ.1 : ℝ) : ℂ) else 0)‖ *
          (‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ * ‖A.E ξ κ‖) := by rw [h2, mul_one]
      _ ≤ 1 * (‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ * ‖A.E ξ κ‖) := by
          gcongr
      _ = _ := one_mul _
  · simp [Set.indicator_of_notMem hτ]

end WaveTurbulence.Represents
