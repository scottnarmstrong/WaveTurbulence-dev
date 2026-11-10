/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBR4

/-! # B3s-HELPER3 B2 (6): integrability of the outer integrand on a general domain

Domain-generic copy of `MkSlotsW/PVBWInteg` (the pinned copy of `MkUnitsL/WIntegW`): the outer integrand of
`outerValMμD … Dom …` (with the top-weighted unit kernels `unitKernelMGW Fs`) is integrable against every measure `μ`
giving `Dom` mass `≤ 1`, and the decoration sum is absolutely summable for every complex weight `‖Zw‖ ≤ 1`. The
relaxed instances (`Dom = splicedTimeDomainFix … ∩ lbDomR …` or `splicedTimeDomainFix …`, `μ = fixMeasure fixSb`)
need no condition on the pins.

* `outerIntegrandMD`, `outerValMμD_eq_outerIntegrandMD` (rfl);
* `measurable_outerIntegrandMDGW`, `norm_outerIntegrandMDGW_le`, `integrable_outerIntegrandMDGW`,
  `integral_norm_outerIntegrandMDGW_le`, `summable_outer_decorationsGWD`;
* the relaxed instances `measurableSet_splicedTimeDomainFix_lb`, `fixMeasure_splicedTimeDomainFix_lb_le`,
  **`integrable_outerIntegrandMDGW_fixR`**, **`summable_outer_decorationsGWD_fixR`** (with lower bounds; `lbS ≡ none`
  gives the instances without). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlotsB
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB
open WaveTurbulence.Flower.MkSlots (fixMeasure integrable_indicator_const_of_le_one
  integral_indicator_const_le_of_le_one outerValMμD)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW unitKernelMGW kerConstGW kerConstG_nonnegW
  norm_unitKernelMG_leW measurable_unitKernelMG_clocksW)

variable {w d : ℕ}

/-- The outer integrand of `outerValMμD` on the domain `Dom` (`VineC.outerIntegrandM` with `Dom`). -/
def outerIntegrandMD (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ)
    (Dom : Set (GBranch G.tree → ℝ)) (hS : G.IsPlain)
    (amp : ReplacementSlot G → Mom d → ℂ) (frq : ReplacementSlot G → Fin 2 → ℤ)
    {J : Type} [Fintype J] [DecidableEq J] (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) (z : GenDecoration G d roots 0) (τ : GBranch G.tree → ℝ) :
    ℂ :=
  Dom.indicator (fun τ =>
    phaseProd L γ δ G (cosetDecoration G L base z.1) τ *
      (∏ s, amp s (base + latticePoint L (z.1 (slotNode hS s)))) * routedPhase frq route tt τ *
      ∏ j, HkM j (modLam frq route j) (fun c => clockOf G tt τ (hclk j c))
        (fun c => base + latticePoint L (z.1 (hmom j c)))) τ

variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
  {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}
variable (Φ : SpliceShape blk Gsb)

theorem measurable_outerIntegrandMDGW (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) {Dom : Set (GBranch Gsb.tree → ℝ)}
    (hDom : MeasurableSet Dom) :
    Measurable (outerIntegrandMD Gsb L γ δ base roots tt Dom hSb amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
      (unitKernelMGW blk D hS Fs L γ δ layer base) z) := by
  unfold outerIntegrandMD
  refine Measurable.indicator ?_ hDom
  have h1 := Φ.measurable_sbInt hS hSb L γ δ base tt amp frq z
  have h2 : Measurable fun τ' : GBranch Gsb.tree → ℝ => ∏ j, unitKernelMGW blk D hS Fs L γ δ layer base j
      (modLam frq (Φ.route hS hSb) j) (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c))
      (fun c => base + latticePoint L (z.1 (Φ.hmom hd j c))) := by
    refine Finset.measurable_prod _ fun j _ => ?_
    simp_rw [MkUnitsL.UnitGW.unitKernelMG_clocksW Φ hd D hS Fs L γ δ layer base tt _ j]
    exact measurable_unitKernelMG_clocksW Φ RB D γ δ layer j _ _
  exact h1.mul h2

theorem norm_outerIntegrandMDGW_le (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) (Dom : Set (GBranch Gsb.tree → ℝ))
    (τ' : GBranch Gsb.tree → ℝ) :
    ‖outerIntegrandMD Gsb L γ δ base roots tt Dom hSb amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base) z τ'‖ ≤
      Dom.indicator (fun _ => ampBound hSb L base amp z * kerConstGW blk RB γ δ) τ' := by
  unfold outerIntegrandMD
  by_cases hτ : τ' ∈ Dom
  · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ]
    rw [norm_mul, norm_mul, norm_mul, norm_phaseProd_le, one_mul, norm_routedPhase, mul_one, norm_prod, norm_prod]
    refine mul_le_mul le_rfl ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) (ampBound_nonneg _ _ _ _ _)
    unfold kerConstGW
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
    rw [MkUnitsL.UnitGW.unitKernelMG_clocksW Φ hd D hS Fs L γ δ layer base tt τ' j]
    exact norm_unitKernelMG_leW RB D γ δ layer j _ _ _
  · rw [Set.indicator_of_notMem hτ, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => mul_nonneg (ampBound_nonneg _ _ _ _ _)
      (kerConstG_nonnegW RB γ δ (fun _ => base))) _

/-- **The outer integrand on a domain `Dom` of mass `≤ 1` is integrable.** -/
theorem integrable_outerIntegrandMDGW (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (D : ReconstructionData S) (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) {Dom : Set (GBranch Gsb.tree → ℝ)}
    (hDom : MeasurableSet Dom) (μ : Measure (GBranch Gsb.tree → ℝ)) (hμ : μ Dom ≤ 1) :
    Integrable (outerIntegrandMD Gsb L γ δ base roots tt Dom hSb amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
      (unitKernelMGW blk D hS Fs L γ δ layer base) z) μ :=
  (integrable_indicator_const_of_le_one hDom hμ _).mono'
    (measurable_outerIntegrandMDGW Φ RB hd D hSb γ δ layer tt amp frq z hDom).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ' => norm_outerIntegrandMDGW_le Φ RB hd D hSb γ δ layer tt amp frq z Dom τ')

theorem integral_norm_outerIntegrandMDGW_le (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (D : ReconstructionData S) (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) {Dom : Set (GBranch Gsb.tree → ℝ)}
    (hDom : MeasurableSet Dom) (μ : Measure (GBranch Gsb.tree → ℝ)) (hμ : μ Dom ≤ 1) :
    ∫ τ, ‖outerIntegrandMD Gsb L γ δ base roots tt Dom hSb amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
      (unitKernelMGW blk D hS Fs L γ δ layer base) z τ‖ ∂μ ≤ ampBound hSb L base amp z * kerConstGW blk RB γ δ := by
  have hc : 0 ≤ ampBound hSb L base amp z * kerConstGW blk RB γ δ :=
    mul_nonneg (ampBound_nonneg _ _ _ _ _) (kerConstG_nonnegW RB γ δ (fun _ => base))
  refine (integral_mono (integrable_outerIntegrandMDGW Φ RB hd D hSb γ δ layer tt amp frq z hDom μ hμ).norm
    (integrable_indicator_const_of_le_one hDom hμ _)
    fun τ' => norm_outerIntegrandMDGW_le Φ RB hd D hSb γ δ layer tt amp frq z Dom τ').trans ?_
  exact integral_indicator_const_le_of_le_one hDom hμ hc

/-- **The decoration sum of `outerValMμD` is absolutely summable** (any complex weight `‖Zw‖ ≤ 1`). -/
theorem summable_outer_decorationsGWD (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (D : ReconstructionData S) (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z)
    {Dom : Set (GBranch Gsb.tree → ℝ)} (hDom : MeasurableSet Dom) (μ : Measure (GBranch Gsb.tree → ℝ))
    (hμ : μ Dom ≤ 1) :
    Summable (fun z : GenDecoration Gsb d roots 0 =>
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * Zw z *
        ∫ τ, outerIntegrandMD Gsb L γ δ base roots tt Dom hSb amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
          (unitKernelMGW blk D hS Fs L γ δ layer base) z τ ∂μ) := by
  refine Summable.of_norm_bounded (hsum.mul_right (kerConstGW blk RB γ δ)) fun z => ?_
  have hint := integral_norm_outerIntegrandMDGW_le Φ RB hd D hSb γ δ layer tt amp frq z hDom μ hμ
  have he : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_splicedEpsilon_le _ _ _
  rw [norm_mul, norm_mul]
  calc _ ≤ 1 * 1 * ∫ τ, ‖outerIntegrandMD Gsb L γ δ base roots tt Dom hSb amp frq (Φ.route hS hSb) (Φ.hclk hd)
        (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z τ‖ ∂μ :=
        mul_le_mul (mul_le_mul he (hZw z) (norm_nonneg _) zero_le_one) (norm_integral_le_integral_norm _)
          (norm_nonneg _) (by norm_num)
    _ ≤ _ := by rw [one_mul, one_mul]; exact hint

/-! ## The relaxed instances -/

theorem measurableSet_splicedTimeDomainFix_lb (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ)
    (fix lb : GBranch G.tree → Option ℝ) : MeasurableSet (splicedTimeDomainFix G layer tt fix ∩ lbDomR lb) :=
  (FlowerP5.measurableSet_splicedTimeDomainFix G layer tt fix).inter (measurableSet_lbDomR lb)

theorem fixMeasure_splicedTimeDomainFix_lb_le (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ)
    (fix lb : GBranch G.tree → Option ℝ) :
    fixMeasure fix (splicedTimeDomainFix G layer tt fix ∩ lbDomR lb) ≤ 1 :=
  (measure_mono (Set.inter_subset_left.trans (splicedTimeDomainFix_subset_boxSbR G layer tt fix))).trans
    (fixMeasure_boxSbR_le layer fix)

/-- **The relaxed outer integrand (with lower bounds) is integrable against the pinned measure**, for any pins. -/
theorem integrable_outerIntegrandMDGW_fixR (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (D : ReconstructionData S) (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0)
    (fixSb lbSb : GBranch Gsb.tree → Option ℝ) :
    Integrable (outerIntegrandMD Gsb L γ δ base roots tt
      (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt fixSb ∩ lbDomR lbSb) hSb amp
      frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z)
      (fixMeasure fixSb) :=
  integrable_outerIntegrandMDGW Φ RB hd D hSb γ δ layer tt amp frq z
    (measurableSet_splicedTimeDomainFix_lb _ _ _ _ _) _ (fixMeasure_splicedTimeDomainFix_lb_le _ _ _ _ _)

/-- **The relaxed decoration sum (with lower bounds) is absolutely summable**, for any pins. -/
theorem summable_outer_decorationsGWD_fixR (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (D : ReconstructionData S) (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z)
    (fixSb lbSb : GBranch Gsb.tree → Option ℝ) :
    Summable (fun z : GenDecoration Gsb d roots 0 =>
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * Zw z *
        ∫ τ, outerIntegrandMD Gsb L γ δ base roots tt
          (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt fixSb ∩ lbDomR lbSb) hSb
          amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z τ
            ∂(fixMeasure fixSb)) :=
  summable_outer_decorationsGWD Φ RB hd D hSb γ δ layer tt amp frq Zw hZw hsum
    (measurableSet_splicedTimeDomainFix_lb _ _ _ _ _) _ (fixMeasure_splicedTimeDomainFix_lb_le _ _ _ _ _)

end WaveTurbulence.Flower.MkSlotsB
