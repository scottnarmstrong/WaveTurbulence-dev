/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB13
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: measurability of the unit kernel in the outer times
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

theorem measurable_unitKernelM_clocks (D : ReconstructionData S) (hS : S.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) (j : J) (hF : HF D hS L (unitProfile blk h j) layer base)
    (lam : ℤ) (β : Fin 4 → Mom d) :
    Measurable fun τ' : GBranch Gsb.tree → ℝ => unitKernelM blk D hS L γ δ h layer hLayer base j lam (Φ.clocks τ' j) β := by
  simp_rw [unitKernelM_eq]
  have hcl : ∀ i, Measurable fun p : (GBranch Gsb.tree → ℝ) × CLInternalTime (regionOf (blk j)) =>
      Φ.clocks p.1 j i := fun i => (Φ.measurable_clocks j i).comp measurable_fst
  have hτ : ∀ v, Measurable fun p : (GBranch Gsb.tree → ℝ) × CLInternalTime (regionOf (blk j)) => p.2 v :=
    fun v => (measurable_pi_apply v).comp measurable_snd
  refine Measurable.mul ?_ (measurable_const.mul ?_)
  · unfold recExp
    exact Measurable.cexp ((Complex.measurable_ofReal.comp
      (((Φ.measurable_clocks j 0).const_mul (-(Real.pi * δ * L ^ (2 * γ)))).mul_const
        (boundaryEnergyFromMomenta (S.sign (blk j).upper.toNode) (β 0) (β 1) (β 2) (β 3)))).mul_const Complex.I)
  · refine measurable_tsum_complex _ (fun κ => ?_) (fun τ' => ?_)
    · have h1 := measurable_clLocalSummand_joint (γ := γ) (δ := δ) (hLayer := hLayer) (regionOf (blk j)) hF β κ
        (fun p : (GBranch Gsb.tree → ℝ) × CLInternalTime (regionOf (blk j)) => Φ.clocks p.1 j) (fun p => p.2) hcl hτ
      have h2 : Measurable fun p : (GBranch Gsb.tree → ℝ) × CLInternalTime (regionOf (blk j)) =>
          lowModC (regionOf (blk j)) (lam : ℝ) (Φ.clocks p.1 j) p.2 := by
        have hb := measurable_clLocalClock_joint (regionOf (blk j))
          (fun p : (GBranch Gsb.tree → ℝ) × CLInternalTime (regionOf (blk j)) => Φ.clocks p.1 j) (fun p => p.2) hcl hτ
          (blk j).lower
        unfold lowModC
        exact Measurable.cexp ((Complex.measurable_ofReal.comp (hb.const_mul (Real.pi * (lam : ℝ)))).mul_const
          Complex.I)
      exact (h2.mul h1).stronglyMeasurable.integral_prod_right'.measurable
    · exact Summable.of_norm_bounded
        (summable_tsum_localBound (γ := γ) (δ := δ) (hLayer := hLayer) (blk j).isBlock (regionOf (blk j)) hF hL β).1
        fun κ => norm_integral_gUnit_le (γ := γ) (hLayer := hLayer) (regionOf (blk j)) hF (lam : ℝ) β (Φ.clocks τ' j) κ

end WaveTurbulence.Represents
