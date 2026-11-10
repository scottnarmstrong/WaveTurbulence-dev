/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.GenModesW
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB16

/-! # MK-UNITS-L (B3-2), generic VINE-B♯ with per-unit top weights: integrability of the outer integrand with an arbitrary regional slot family

Copy-generalization of `Represents/RepVB13–RepVB16` from main's unit kernel `unitKernelM` (native slot kernels, bound
`lbConst`) to `unitKernelMGW Fs` under an abstract regional bound `RegBoundW` (bound `RB.lbC`):
`norm_unitKernelMG_leW`, `measurable_unitKernelMG_clocksW`, `norm_outerIntegrandMG_leW`, `integrable_outerIntegrandMGW`,
`summable_outer_decorationsGW` (the hypotheses `hint`, `hsm` of the class sum).

Stage1WVine's `WInteg` with the slot family `Fs` a `SlotFamW` (slot kernels and per-unit top weights, `GenW1`); the
proofs are verbatim, every declaration renamed with the suffix `W`.  Adapted from `Flower/Stage1WVine/WInteg.lean`
(see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnitsL
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB Filter Topology

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
  {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

theorem norm_unitKernelMG_leW (RB : RegBoundW blk hS Fs L base) (D : ReconstructionData S) (γ δ : ℝ)
    (layer : GNode (D.forest hS) → ℕ) (j : J) (lam : ℤ) (t : Fin 3 → ℝ) (β : Fin 4 → Mom d) :
    ‖unitKernelMGW blk D hS Fs L γ δ layer base j lam t β‖ ≤ ‖unitConst (d := d) blk L γ δ j‖ * RB.lbC j := by
  unfold unitKernelMGW
  rw [norm_mul, norm_recExp, one_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hn : ∀ κ : CLLocalDecoration (regionOf (blk j)) L base β, ‖∫ τ : CLInternalTime (regionOf (blk j)),
      lowModC (regionOf (blk j)) (lam : ℝ) t τ *
        clLocalSummandGW D hS (regionOf (blk j)) Fs L γ δ layer base β t κ τ‖ ≤
      RB.lb j (clExtendIndices (regionOf (blk j)) κ.1) :=
    fun κ => norm_integral_gUnitG_leW RB D γ δ layer j (lam : ℝ) β t κ
  have hs := RB.summable j β
  calc _ ≤ ∑' κ : CLLocalDecoration (regionOf (blk j)) L base β, ‖∫ τ : CLInternalTime (regionOf (blk j)),
      lowModC (regionOf (blk j)) (lam : ℝ) t τ *
        clLocalSummandGW D hS (regionOf (blk j)) Fs L γ δ layer base β t κ τ‖ :=
        norm_tsum_le_tsum_norm (Summable.of_norm_bounded hs hn).norm
    _ ≤ ∑' κ : CLLocalDecoration (regionOf (blk j)) L base β, RB.lb j (clExtendIndices (regionOf (blk j)) κ.1) :=
        Summable.tsum_le_tsum hn (Summable.of_norm_bounded hs hn).norm hs
    _ ≤ _ := RB.tsum_le j β

variable (Φ : SpliceShape blk Gsb)

theorem measurable_unitKernelMG_clocksW (RB : RegBoundW blk hS Fs L base) (D : ReconstructionData S) (γ δ : ℝ)
    (layer : GNode (D.forest hS) → ℕ) (j : J) (lam : ℤ) (β : Fin 4 → Mom d) :
    Measurable fun τ' : GBranch Gsb.tree → ℝ => unitKernelMGW blk D hS Fs L γ δ layer base j lam (Φ.clocks τ' j) β := by
  unfold unitKernelMGW
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
    · have h1 := measurable_clLocalSummandG_jointW D hS (regionOf (blk j)) Fs L γ δ base (RB.meas j) layer β κ
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
    · exact Summable.of_norm_bounded (RB.summable j β)
        fun κ => norm_integral_gUnitG_leW RB D γ δ layer j (lam : ℝ) β (Φ.clocks τ' j) κ

/-- The uniform bound of the product of the unit kernels. -/
def kerConstGW (blk : J → CLBlock S) (RB : RegBoundW blk hS Fs L base) (γ δ : ℝ) : ℝ :=
  ∏ j, (‖unitConst (d := d) blk L γ δ j‖ * RB.lbC j)

theorem kerConstG_nonnegW (RB : RegBoundW blk hS Fs L base) (γ δ : ℝ) (β : Fin 4 → Mom d) :
    0 ≤ kerConstGW blk RB γ δ :=
  Finset.prod_nonneg fun j _ => mul_nonneg (norm_nonneg _) (lbC_nonnegW RB j β)

end WaveTurbulence.Flower.MkUnitsL
