/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB14
public import WaveTurbulence.Foundations.Vine.C.VCApi
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: the outer integrand with the unit kernel `unitKernelM` is integrable, its decoration sum
is summable (hypotheses `hint`, `hsm` of VINE-C's class sum)
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

/-- The uniform bound of the product of the unit kernels. -/
noncomputable def kerConst (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) : ℝ :=
  ∏ j, (‖unitConst (d := d) blk L γ δ j‖ *
    lbConst D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j)))

theorem norm_outerIntegrandM_le (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) :
    ‖VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp frq
        (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelM blk D hS L γ δ h layer hLayer base) z τ'‖ ≤
      (boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
        (fun _ => ampBound hSb L base amp z * kerConst blk D hS L γ δ h layer hLayer base) τ' := by
  unfold VineC.outerIntegrandM
  by_cases hτ : τ' ∈ splicedTimeDomain Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
  · rw [Set.indicator_of_mem hτ]
    have hbox : τ' ∈ boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) := fun c _ => hτ.1 c
    rw [Set.indicator_of_mem hbox]
    rw [norm_mul, norm_mul, norm_mul, norm_phaseProd_le, one_mul, norm_routedPhase, mul_one, norm_prod, norm_prod]
    refine mul_le_mul le_rfl ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) (ampBound_nonneg _ _ _ _ _)
    unfold kerConst
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
    rw [Φ.unitKernelM_clocks hd D hS L γ δ h layer hLayer base tt τ' j]
    exact norm_unitKernelM_le D hS hL γ δ h layer hLayer base j (hF j) _ _ _
  · rw [Set.indicator_of_notMem hτ, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => mul_nonneg (ampBound_nonneg _ _ _ _ _)
      (Finset.prod_nonneg fun j _ => mul_nonneg (norm_nonneg _) (lbConst_nonneg _ _ _ _ _ _ _ _ _ _))) _

end WaveTurbulence.Represents
