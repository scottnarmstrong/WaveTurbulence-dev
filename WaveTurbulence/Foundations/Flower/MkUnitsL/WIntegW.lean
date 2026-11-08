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

theorem norm_outerIntegrandMG_leW (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) :
    ‖VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp frq
        (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z τ'‖ ≤
      (boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
        (fun _ => ampBound hSb L base amp z * kerConstGW blk RB γ δ) τ' := by
  unfold VineC.outerIntegrandM
  by_cases hτ : τ' ∈ splicedTimeDomain Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
  · rw [Set.indicator_of_mem hτ]
    have hbox : τ' ∈ boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) := fun c _ => hτ.1 c
    rw [Set.indicator_of_mem hbox]
    rw [norm_mul, norm_mul, norm_mul, norm_phaseProd_le, one_mul, norm_routedPhase, mul_one, norm_prod, norm_prod]
    refine mul_le_mul le_rfl ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) (ampBound_nonneg _ _ _ _ _)
    unfold kerConstGW
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
    rw [UnitGW.unitKernelMG_clocksW Φ hd D hS Fs L γ δ layer base tt τ' j]
    exact norm_unitKernelMG_leW RB D γ δ layer j _ _ _
  · rw [Set.indicator_of_notMem hτ, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => mul_nonneg (ampBound_nonneg _ _ _ _ _)
      (kerConstG_nonnegW RB γ δ (fun _ => base))) _

theorem integrable_outerIntegrandMGW (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) :
    Integrable (VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp
      frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z) := by
  have hmeas : Measurable (VineC.outerIntegrandM Gsb L γ δ base roots tt
      (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
      (unitKernelMGW blk D hS Fs L γ δ layer base) z) := by
    unfold VineC.outerIntegrandM
    refine Measurable.indicator ?_ (Represents.measurableSet_splicedTimeDomain _ _ _)
    have h1 := Φ.measurable_sbInt hS hSb L γ δ base tt amp frq z
    have h2 : Measurable fun τ' : GBranch Gsb.tree → ℝ => ∏ j, unitKernelMGW blk D hS Fs L γ δ layer base j
        (modLam frq (Φ.route hS hSb) j) (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c))
        (fun c => base + latticePoint L (z.1 (Φ.hmom hd j c))) := by
      refine Finset.measurable_prod _ fun j _ => ?_
      simp_rw [UnitGW.unitKernelMG_clocksW Φ hd D hS Fs L γ δ layer base tt _ j]
      exact measurable_unitKernelMG_clocksW Φ RB D γ δ layer j _ _
    exact h1.mul h2
  have hQ : MeasurableSet (boxSb (Gsb := Gsb) (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)) :=
    measurableSet_boxSb _
  refine Integrable.mono' (g := (boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
    (fun _ => ampBound hSb L base amp z * kerConstGW blk RB γ δ)) ?_
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun τ' =>
      norm_outerIntegrandMG_leW Φ RB hd D hSb γ δ layer tt amp frq z τ')
  exact (integrable_indicator_iff hQ).2 (integrableOn_const (by rw [volume_boxSb]; exact ENNReal.one_ne_top))

theorem summable_outer_decorationsGW (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zw : GenDecoration Gsb d roots 0 → ℝ) (hZw : ∀ z, |Zw z| ≤ 1)
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z) :
    Summable (fun z : GenDecoration Gsb d roots 0 =>
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Zw z : ℂ) *
        ∫ τ, VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp
          frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z τ) := by
  refine Summable.of_norm_bounded (hsum.mul_right (kerConstGW blk RB γ δ)) fun z => ?_
  have hQ : MeasurableSet (boxSb (Gsb := Gsb) (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)) :=
    measurableSet_boxSb _
  have hint : ∫ τ, ‖VineC.outerIntegrandM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb
      amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z τ‖ ≤
      ampBound hSb L base amp z * kerConstGW blk RB γ δ := by
    have hg : Integrable ((boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
        (fun _ => ampBound hSb L base amp z * kerConstGW blk RB γ δ)) :=
      (integrable_indicator_iff hQ).2 (integrableOn_const (by rw [volume_boxSb]; exact ENNReal.one_ne_top))
    refine (integral_mono (integrable_outerIntegrandMGW Φ RB hd D hSb γ δ layer tt amp frq z).norm hg
      fun τ' => norm_outerIntegrandMG_leW Φ RB hd D hSb γ δ layer tt amp frq z τ').trans_eq ?_
    rw [integral_indicator_const _ hQ, Measure.real, volume_boxSb]
    simp
  have he : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_splicedEpsilon_le _ _ _
  have hzw : ‖(Zw z : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hZw z
  rw [norm_mul, norm_mul]
  calc _ ≤ 1 * 1 * ∫ τ, ‖VineC.outerIntegrandM Gsb L γ δ base roots tt
        (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hSb amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base) z τ‖ :=
        mul_le_mul (mul_le_mul he hzw (norm_nonneg _) zero_le_one) (norm_integral_le_integral_norm _)
          (norm_nonneg _) (by norm_num)
    _ ≤ _ := by rw [one_mul, one_mul]; exact hint

end WaveTurbulence.Flower.MkUnitsL
