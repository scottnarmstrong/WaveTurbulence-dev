/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBR3

/-! # B3s-HELPER3 B2 (4): the domain-generic pinned glue and the per-mode identity

Domain-generic copy of the glue part of `MkSlotsW/PVBW2` (itself the pinned copy of `MkUnitsL/GenW3`). The domains
enter through `GlueDomR Φ hd D hS layer fixS A B`: `B` measurable of pinned mass `≤ 1`, and the domain split
`glueTime τ' τs ∈ A ↔ τ' ∈ B ∧ (unit domains)` for glued vectors on the pinned slice with free times off the pins
(`PinnedAt`, a `fixMeasure fixS`-full set). Since the split is only needed a.e., the glue identity
`modeGWD (modal) A = psiIntGWD B ∘ timeSplit` holds `fixMeasure fixS`-a.e. (`modeGWD_glue_ae`), which is all the
measure-preserving time split (`MkSlots.measurePreserving_timeSplit_fix`, needing `hU`) uses. The outer domain `Dom`
of the conclusion may differ from `B` on a `fixMeasure fixSb`-null set (`hDB`).

* `GlueDomR`, **`GlueDomR.relaxed`** (`A = coreTimeDomainWR`, `B = openSbR`), **`GlueDomR.relaxedLB`** (with lower
  bounds), `GlueDomR.unpinned` (main's domains, no pins);
* `glueTime_timeSplit`, `modeGWD_glue_ae`, `skelTerm_glueGWD_fix`, `norm_skelTerm_glueGWD_le_fix`,
  `tsum_skelTermGWD_fix`, `outer_term_eqGWD_fix`;
* **`skelVal_modal_eq_outerValMGWD_fix`**: `skelValWD (modalFnGW Fs amp frq) A fixS = outerValMμD … Dom … (fixMeasure
  fixSb) … (unitKernelMGW Fs)`. -/

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
open WaveTurbulence.Flower.MkSlots (fixMeasure fixMeasure_none measurePreserving_timeSplit_fix outerValMμD)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW unitIGW modalFnGW unitKernelMGW)
open WaveTurbulence.Flower.MkUnitsL.UnitGW (prod_unitKernelMGW resDec_glueDecGW kBoundGW summable_kBoundGW
  summable_fib_kBoundGW const_splitGW)

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

/-! ## The domain hypotheses -/

/-- **The domain hypotheses of the generic chain**: the `G_sb` domain `B` is measurable of pinned mass `≤ 1`, and the
glued vectors on the pinned slice split between `A` and `B` × the unit domains. -/
structure GlueDomR (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (fixS : GBranch S.tree → Option ℝ) (A : Set (GBranch S.tree → ℝ)) (B : Set (GBranch Gsb.tree → ℝ)) : Prop where
  meas : MeasurableSet B
  mass : fixMeasure (fun c => fixS (Φ.br c)) B ≤ 1
  dom : ∀ τ' τs, PinnedAt fixS (Φ.glueTime hd τ' τs) →
    (Φ.glueTime hd τ' τs ∈ A ↔ τ' ∈ B ∧
      ∀ j, τs j ∈ clLocalTimeDomain (regionOf (blk j)) (fun b => layer (D.coreBranch hS b).toNode) (Φ.clocks τ' j))

/-- The relaxed domains form a `GlueDomR` (PVBR2). -/
theorem GlueDomR.relaxed (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (tt : Fin w → ℝ) (fixS : GBranch S.tree → Option ℝ)
    (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS) :
    GlueDomR Φ hd D hS layer fixS (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
      (openSbR Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c))) where
  meas := measurableSet_openSbR _ _ _ _
  mass := fixMeasure_openSbR_le _ _ _ _
  dom τ' τs hτ := mem_coreTimeDomainWR_glue_iff Φ hd _ tt fixS hU hP τ' τs hτ

/-- The relaxed domains with lower bounds form a `GlueDomR` (ruling R187). -/
theorem GlueDomR.relaxedLB (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (tt : Fin w → ℝ) (fixS lbS : GBranch S.tree → Option ℝ)
    (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none) (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS) :
    GlueDomR Φ hd D hS layer fixS
      (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS)
      (openSbR Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
        lbDomR (fun c => lbS (Φ.br c))) where
  meas := (measurableSet_openSbR _ _ _ _).inter (measurableSet_lbDomR _)
  mass := (MeasureTheory.measure_mono Set.inter_subset_left).trans (fixMeasure_openSbR_le _ _ _ _)
  dom τ' τs hτ := mem_coreTimeDomainWR_lb_glue_iff Φ hd _ tt fixS lbS hU hlbU hP τ' τs hτ

/-- Main's unpinned domains form a `GlueDomR` for the empty pins. -/
theorem GlueDomR.unpinned (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (tt : Fin w → ℝ) :
    GlueDomR Φ hd D hS layer (fun _ => none) (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt)
      (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt) where
  meas := measurableSet_openSb _ _ _
  mass := by
    rw [← openSbR_none]
    exact fixMeasure_openSbR_le _ _ _ _
  dom τ' τs _ := Φ.dom_iff hd _ tt τ' τs

/-! ## The pinned glue -/

theorem glueTime_timeSplit (hd : Disj blk) (τ : GBranch S.tree → ℝ) :
    Φ.glueTime hd (Φ.timeSplit hd τ).1 (Φ.timeSplit hd τ).2 = τ := by
  rw [← Φ.timeSplit_symm hd]
  exact (Φ.timeSplit hd).symm_apply_apply τ

variable {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

/-- **The glue identity holds `fixMeasure fixS`-a.e.** -/
theorem modeGWD_glue_ae (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (fixS : GBranch S.tree → Option ℝ) {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)}
    (hG : GlueDomR Φ hd D hS layer fixS A B) (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ∀ᵐ τ ∂(fixMeasure fixS), modeGWD blk (modalFnGW Φ hS hSb Fs amp frq) hS L γ δ base tt A
        (Φ.glueDec hS hd hL base z κs) τ =
      psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B (Φ.timeSplit hd τ) := by
  filter_upwards [ae_pinnedAt fixS] with τ hτ
  have h := integrand_glueGWD Φ hd hS hSb hL γ δ base D layer Fs tt amp frq z κs A B (Φ.timeSplit hd τ).1
    (Φ.timeSplit hd τ).2 (hG.dom _ _ (by rw [glueTime_timeSplit]; exact hτ))
  rw [glueTime_timeSplit] at h
  exact h

open scoped Classical in
/-- **The pinned glued term on general domains** (cf. `MkSlotsW.skelTerm_glueGW_fix`). -/
theorem skelTerm_glueGWD_fix (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    skelTermWD blk hS L γ δ base roots tt selSk (modalFnGW Φ hS hSb Fs amp frq) A fixS
        (Φ.glueDec hS hd hL base z κs) =
    (Zw z : ℂ) * ∫ p, psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B p
      ∂((fixMeasure (fun c => fixS (Φ.br c))).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
  have hZz := hZ (Φ.glueDec hS hd hL base z κs)
  rw [resDec_glueDecGW Φ hd hL base z κs] at hZz
  rw [skelTermWD_eq_integral]
  by_cases hs : selSk (Φ.glueDec hS hd hL base z κs)
  · rw [ite_eq_left hs] at hZz ⊢
    rw [← hZz]
    simp only [Complex.ofReal_one, one_mul]
    have hmp := measurePreserving_timeSplit_fix Φ hd fixS hU
    rw [← hmp.integral_comp' (psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B)]
    exact integral_congr_ae (modeGWD_glue_ae Φ hd hSb hL γ δ D layer tt amp frq fixS hG z κs)
  · rw [ite_eq_right hs] at hZz ⊢
    rw [← hZz]
    simp

open scoped Classical in
theorem norm_skelTerm_glueGWD_le_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖skelTermWD blk hS L γ δ base roots tt selSk (modalFnGW Φ hS hSb Fs amp frq) A fixS
        (Φ.glueDec hS hd hL base z κs)‖ ≤
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  rw [skelTerm_glueGWD_fix Φ hd hSb hL γ δ D layer tt amp frq selSk Zw hZ fixS hU hG z κs, norm_mul]
  have hZz := hZ (Φ.glueDec hS hd hL base z κs)
  rw [resDec_glueDecGW Φ hd hL base z κs] at hZz
  have h1 : ‖(Zw z : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, ← hZz]
    split_ifs <;> simp
  calc _ ≤ 1 * _ := mul_le_mul h1
        (norm_integral_psiIntGWD_le_fix Φ RB hd D hSb γ δ layer tt amp frq z κs (fun c => fixS (Φ.br c))
          hG.meas hG.mass) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

open scoped Classical in
theorem tsum_skelTermGWD_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B) :
    ∑' κ : GenDecoration S d roots 0,
        skelTermWD blk hS L γ δ base roots tt selSk (modalFnGW Φ hS hSb Fs amp frq) A fixS κ =
    ∑' z : GenDecoration Gsb d roots 0, (Zw z : ℂ) *
      ∫ τ' : GBranch Gsb.tree → ℝ, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
        B.indicator
          (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
            ∏ j, (Φ.recJ L γ δ base z τ' j *
              ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
                unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ' ∂(fixMeasure (fun c => fixS (Φ.br c))) := by
  have hglue : ∀ p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      skelTermWD blk hS L γ δ base roots tt selSk (modalFnGW Φ hS hSb Fs amp frq) A fixS
        ((Φ.decSplit hS hd hL base roots).symm p) = (Zw p.1 : ℂ) *
      ∫ q, psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq p.1 p.2 B q
        ∂((fixMeasure (fun c => fixS (Φ.br c))).prod
          (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    fun p => skelTerm_glueGWD_fix Φ hd hSb hL γ δ D layer tt amp frq selSk Zw hZ fixS hU hG p.1 p.2
  have hnorm : ∀ p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      ‖skelTermWD blk hS L γ δ base roots tt selSk (modalFnGW Φ hS hSb Fs amp frq) A fixS
        ((Φ.decSplit hS hd hL base roots).symm p)‖ ≤ kBoundGW Φ RB hSb amp p :=
    fun p => norm_skelTerm_glueGWD_le_fix Φ RB hd hSb hL γ δ D layer tt amp frq selSk Zw hZ fixS hU hG p.1 p.2
  have hFs : Summable fun p => skelTermWD blk hS L γ δ base roots tt selSk
      (modalFnGW Φ hS hSb Fs amp frq) A fixS ((Φ.decSplit hS hd hL base roots).symm p) :=
    Summable.of_norm_bounded (summable_kBoundGW Φ RB hSb (roots := roots) amp hsum) hnorm
  have hfib : ∀ z : GenDecoration Gsb d roots 0,
      Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
        skelTermWD blk hS L γ δ base roots tt selSk (modalFnGW Φ hS hSb Fs amp frq) A fixS
          ((Φ.decSplit hS hd hL base roots).symm ⟨z, κs⟩) :=
    fun z => Summable.of_norm_bounded (summable_fib_kBoundGW Φ RB hSb amp z) fun κs => hnorm ⟨z, κs⟩
  have e2 := Summable.tsum_sigma' (f := fun p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      skelTermWD blk hS L γ δ base roots tt selSk (modalFnGW Φ hS hSb Fs amp frq) A fixS
        ((Φ.decSplit hS hd hL base roots).symm p)) hfib hFs
  have e1 := (Φ.decSplit hS hd hL base roots).symm.tsum_eq (skelTermWD blk hS L γ δ base roots tt selSk
      (modalFnGW Φ hS hSb Fs amp frq) A fixS)
  refine (e1.symm.trans e2).trans (tsum_congr fun z => ?_)
  have hz : ∀ κs, skelTermWD blk hS L γ δ base roots tt selSk (modalFnGW Φ hS hSb Fs amp frq) A fixS
      ((Φ.decSplit hS hd hL base roots).symm ⟨z, κs⟩) = (Zw z : ℂ) *
      ∫ q, psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B q
        ∂((fixMeasure (fun c => fixS (Φ.br c))).prod
          (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := fun κs => hglue ⟨z, κs⟩
  simp_rw [hz]
  rw [tsum_mul_left, fiber_sumGWD_fix Φ RB hd D hSb γ δ layer tt amp frq z (fun c => fixS (Φ.br c)) hG.meas
    hG.mass]

/-- The pinned outer term on a domain `Dom` agreeing a.e. with `B` (cf. `MkSlotsW.outer_term_eqGW_fix`). -/
theorem outer_term_eqGWD_fix (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (Fs : SlotFamW S d)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zw : GenDecoration Gsb d roots 0 → ℝ) (fixSb : GBranch Gsb.tree → Option ℝ)
    (Dom B : Set (GBranch Gsb.tree → ℝ)) (hDB : ∀ᵐ τ' ∂(fixMeasure fixSb), τ' ∈ Dom ↔ τ' ∈ B)
    (z : GenDecoration Gsb d roots 0) :
    (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Zw z : ℂ) *
      ∫ τ' : GBranch Gsb.tree → ℝ,
        Dom.indicator (fun τ' =>
          phaseProd L γ δ Gsb (cosetDecoration Gsb L base z.1) τ' *
            (∏ s, amp s (base + latticePoint L (z.1 (slotNode hSb s)))) *
              routedPhase frq (Φ.route hS hSb) tt τ' *
            ∏ j, unitKernelMGW blk D hS Fs L γ δ layer base j (modLam frq (Φ.route hS hSb) j)
              (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c))
              (fun c => base + latticePoint L (z.1 (Φ.hmom hd j c)))) τ' ∂(fixMeasure fixSb) =
    (∏ j, unitConst (d := d) blk L γ δ j) * ((Zw z : ℂ) * ∫ τ' : GBranch Gsb.tree → ℝ,
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
        B.indicator
          (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
            ∏ j, (Φ.recJ L γ δ base z τ' j *
              ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
                unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ' ∂(fixMeasure fixSb)) := by
  rw [integral_congr_ae (indicator_ae_eq_of_ae_iff hDB _)]
  simp_rw [prod_unitKernelMGW Φ hd D hS hSb L γ δ base Fs layer tt frq z]
  rw [← integral_const_mul, ← integral_const_mul]
  have : ∀ τ' : GBranch Gsb.tree → ℝ, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Zw z : ℂ) *
      B.indicator
        (fun τ' => phaseProd L γ δ Gsb (cosetDecoration Gsb L base z.1) τ' *
          (∏ s, amp s (base + latticePoint L (z.1 (slotNode hSb s)))) *
            routedPhase frq (Φ.route hS hSb) tt τ' *
          ((∏ j, unitConst (d := d) blk L γ δ j) * ∏ j, (Φ.recJ L γ δ base z τ' j *
            ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
              unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ))) τ' =
      (∏ j, unitConst (d := d) blk L γ δ j) * ((Zw z : ℂ) *
        ((splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
        B.indicator
          (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
            ∏ j, (Φ.recJ L γ δ base z τ' j *
              ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
                unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ')) := by
    intro τ'
    by_cases hp : τ' ∈ B
    · simp only [Set.indicator_of_mem hp]
      unfold SpliceShape.sbInt
      ring
    · simp [Set.indicator_of_notMem hp]
  simp_rw [this]
  rw [integral_const_mul, integral_const_mul]

open scoped Classical in
/-- **The pinned per-mode single-state factorization on general domains** (cf.
`MkSlotsW.skelVal_modal_eq_outerValMGW_fix`): unit interiors unpinned (`hU`), the domain split `hG`, and the outer
domain `Dom` a.e. equal to `B` (`hDB`). -/
theorem skelVal_modal_eq_outerValMGWD_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (Dom : Set (GBranch Gsb.tree → ℝ))
    (hDB : ∀ᵐ τ' ∂(fixMeasure (fun c => fixS (Φ.br c))), τ' ∈ Dom ↔ τ' ∈ B) :
    skelValWD blk hS L γ δ base roots tt selSk (modalFnGW Φ hS hSb Fs amp frq) A fixS =
    outerValMμD Gsb L γ δ base roots tt Dom (Φ.hinges hd) (fun z => (Zw z : ℂ)) hSb
      (fixMeasure (fun c => fixS (Φ.br c))) amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
      (unitKernelMGW blk D hS Fs L γ δ layer base) := by
  have hs := tsum_skelTermGWD_fix Φ RB hd hSb hL γ δ D layer tt amp frq selSk Zw hZ hsum fixS hU hG
  have hC := const_splitGW (d := d) Φ hd L γ δ
  rw [skelValWD, hs, hC]
  unfold outerValMμD
  simp_rw [outer_term_eqGWD_fix Φ hd D hS hSb L γ δ base Fs layer tt amp frq Zw (fun c => fixS (Φ.br c)) Dom B hDB]
  rw [tsum_mul_left]
  ring

end WaveTurbulence.Flower.MkSlotsB
