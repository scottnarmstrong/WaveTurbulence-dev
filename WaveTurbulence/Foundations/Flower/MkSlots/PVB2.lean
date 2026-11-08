/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PVB1
public import WaveTurbulence.Foundations.Flower.MkSlots.OuterFix
public import WaveTurbulence.Foundations.Flower.Stage1WVine.GenVB3

/-! # B3s MK-SLOTS: pinned VINE-B♯ (2/4) — pinned Fubini and the pinned per-mode identity

Pinned copy of the measure-dependent part of `Stage1WVine/GenVB2` (section `Fiber`) and `Stage1WVine/GenVB3`: the
`G_sb` times are integrated against `fixMeasure fixSb`, the skeleton times against `fixMeasure fixS`, the unit-interior
times against `volume` (unchanged). The pointwise glue (`integrand_glueG`), `psiIntG`, `fibIntG`, `inner_psiIntG`,
`unitIG`, the unit bounds and the decoration bounds `kBoundG` are reused from `Stage1WVine` by import.

* `integrable_psiIntG_fix`, `norm_integral_psiIntG_le_fix`, `integral_psiIntG_fix`, `integrable_fibIntG_fix`,
  `fiber_sumG_fix` (box measures `≤ 1` replace `volume_boxQ`/`volume_boxSb`);
* `skelTerm_glueG_fix` (the pinned time split `measurePreserving_timeSplit_fix`), `norm_skelTerm_glueG_le_fix`,
  `tsum_skelTermG_fix`;
* `outer_term_eqG_fix` (the pinned a.e. step `indicator_openSb_ae_fix`);
* **`skelVal_modal_eq_outerValMG_fix`**: `skelValF (modalFnG Fs amp frq) fixS = outerValMμ (…) (fixMeasure fixSb) (…)`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlots
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.Stage1WVine.UnitG

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)
variable {hS : S.IsPlain} {Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ} {L : ℝ} {base : Mom d}

/-! ## Pinned Fubini (cf. `GenVB2`, section `Fiber`) -/

theorem integrable_psiIntG_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (fixSb : GBranch Gsb.tree → Option ℝ) :
    Integrable (psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs)
      ((fixMeasure fixSb).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
  have hQ := SpliceShape.measurableSet_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hg := integrable_indicator_const_of_le_one hQ (fixMeasure_boxQ_le (blk := blk) D hS layer
    (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) fixSb)
    (ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1))
  exact hg.mono' (measurable_psiIntG Φ RB hd D hSb γ δ layer tt amp frq z κs).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => norm_psiIntG_le Φ RB hd D hSb γ δ layer tt amp frq z κs p)

theorem norm_integral_psiIntG_le_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (fixSb : GBranch Gsb.tree → Option ℝ) :
    ‖∫ p, psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p
        ∂((fixMeasure fixSb).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j)))))‖ ≤
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  refine (norm_integral_le_integral_norm _).trans ?_
  have hQ := SpliceShape.measurableSet_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have h1 := fixMeasure_boxQ_le (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) fixSb
  have hc : 0 ≤ ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)
  refine (integral_mono (integrable_psiIntG_fix Φ RB hd D hSb γ δ layer tt amp frq z κs fixSb).norm
    (integrable_indicator_const_of_le_one hQ h1 _)
    fun p => norm_psiIntG_le Φ RB hd D hSb γ δ layer tt amp frq z κs p).trans ?_
  exact integral_indicator_const_le_of_le_one hQ h1 hc

theorem integral_psiIntG_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (fixSb : GBranch Gsb.tree → Option ℝ) :
    ∫ p, psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p
        ∂((fixMeasure fixSb).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) =
      ∫ τ', fibIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs τ' ∂(fixMeasure fixSb) := by
  rw [integral_prod _ (integrable_psiIntG_fix Φ RB hd D hSb γ δ layer tt amp frq z κs fixSb)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ' =>
    inner_psiIntG Φ hd D hSb γ δ layer tt amp frq z κs τ')

theorem integrable_fibIntG_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (fixSb : GBranch Gsb.tree → Option ℝ) :
    Integrable (fibIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs) (fixMeasure fixSb) := by
  have := (integrable_psiIntG_fix Φ RB hd D hSb γ δ layer tt amp frq z κs fixSb).integral_prod_left
  have hfun : (fun τ' => ∫ τs : (∀ j, CLInternalTime (regionOf (blk j))),
      psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs (τ', τs)) =
      fibIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs :=
    funext fun τ' => inner_psiIntG Φ hd D hSb γ δ layer tt amp frq z κs τ'
  rwa [hfun] at this

theorem fiber_sumG_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0) (fixSb : GBranch Gsb.tree → Option ℝ) :
    ∑' κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      ∫ p, psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p
        ∂((fixMeasure fixSb).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) =
    ∫ τ' : GBranch Gsb.tree → ℝ, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
      (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
        (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
          ∏ j, (Φ.recJ L γ δ base z τ' j *
            ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
              unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ' ∂(fixMeasure fixSb) := by
  have hK : Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    ((summable_pi_prod_dep (fun j (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      RB.lb j (clExtendIndices (regionOf (blk j)) κ.1))
      (fun j κ => RB.nonneg j _) (fun j => RB.summable j _)).1).mul_left _
  have hsum : Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      ∫ τ', ‖fibIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs τ'‖ ∂(fixMeasure fixSb) := by
    refine Summable.of_nonneg_of_le (fun κs => integral_nonneg fun _ => norm_nonneg _) (fun κs => ?_) hK
    have hB := measurableSet_boxSb (Gsb := Gsb) (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
    have h1 := fixMeasure_boxSb_le (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) fixSb
    have hc : 0 ≤ ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
      mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)
    refine (integral_mono (integrable_fibIntG_fix Φ RB hd D hSb γ δ layer tt amp frq z κs fixSb).norm
      (integrable_indicator_const_of_le_one hB h1 _)
      fun τ' => norm_fibIntG_le Φ RB hd D hSb γ δ layer tt amp frq z κs τ').trans ?_
    exact integral_indicator_const_le_of_le_one hB h1 hc
  simp_rw [integral_psiIntG_fix Φ RB hd D hSb γ δ layer tt amp frq z _ fixSb]
  rw [integral_tsum_of_summable_integral_norm
    (fun κs => integrable_fibIntG_fix Φ RB hd D hSb γ δ layer tt amp frq z κs fixSb) hsum]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ' => ?_)
  by_cases hp : τ' ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
  · unfold fibIntG
    simp only [Set.indicator_of_mem hp]
    rw [tsum_mul_left, tsum_mul_left]
    congr 2
    have hs : ∀ j, Summable fun κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j) =>
        Φ.recJ L γ δ base z τ' j * unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ :=
      fun j => (summable_unitIG Φ RB D hSb γ δ layer frq z τ' j).mul_left _
    rw [tsum_pi_prod_complex (fun j κ => Φ.recJ L γ δ base z τ' j *
      unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ) hs]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [tsum_mul_left]
  · unfold fibIntG
    simp [Set.indicator_of_notMem hp]

/-! ## The pinned glue (cf. `GenVB3`) -/

open scoped Classical in
/-- **The pinned glued term** (cf. `skelTerm_glueG`). -/
theorem skelTerm_glueG_fix (_RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    skelTermF D hS L γ δ base roots tt layer selSk (modalFnG Φ hS hSb Fs amp frq) fixS
        (Φ.glueDec hS hd hL base z κs) =
    (Zw z : ℂ) * ∫ p, psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p
      ∂((fixMeasure (fun c => fixS (Φ.br c))).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
  have hZz := hZ (Φ.glueDec hS hd hL base z κs)
  rw [resDec_glueDecG Φ hd hL base z κs] at hZz
  unfold skelTermF
  by_cases hs : selSk (Φ.glueDec hS hd hL base z κs)
  · rw [ite_eq_left hs] at hZz ⊢
    rw [← hZz]
    simp only [Complex.ofReal_one, one_mul]
    rw [← integral_const_mul]
    have hmp := (measurePreserving_timeSplit_fix Φ hd fixS hU).symm (Φ.timeSplit hd)
    rw [← hmp.integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [Φ.timeSplit_symm hd]
    exact integrand_glueG Φ hd hS hSb hL γ δ base D layer Fs tt amp frq z κs p.1 p.2
  · rw [ite_eq_right hs] at hZz ⊢
    rw [← hZz]
    simp

open scoped Classical in
theorem norm_skelTerm_glueG_le_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖skelTermF D hS L γ δ base roots tt layer selSk (modalFnG Φ hS hSb Fs amp frq) fixS
        (Φ.glueDec hS hd hL base z κs)‖ ≤
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  rw [skelTerm_glueG_fix Φ RB hd hSb hL γ δ D layer tt amp frq selSk Zw hZ fixS hU z κs, norm_mul]
  have hZz := hZ (Φ.glueDec hS hd hL base z κs)
  rw [resDec_glueDecG Φ hd hL base z κs] at hZz
  have h1 : ‖(Zw z : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, ← hZz]
    split_ifs <;> simp
  calc _ ≤ 1 * _ := mul_le_mul h1
        (norm_integral_psiIntG_le_fix Φ RB hd D hSb γ δ layer tt amp frq z κs (fun c => fixS (Φ.br c)))
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

open scoped Classical in
theorem tsum_skelTermG_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none) :
    ∑' κ : GenDecoration S d roots 0,
        skelTermF D hS L γ δ base roots tt layer selSk (modalFnG Φ hS hSb Fs amp frq) fixS κ =
    ∑' z : GenDecoration Gsb d roots 0, (Zw z : ℂ) *
      ∫ τ' : GBranch Gsb.tree → ℝ, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
        (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
          (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
            ∏ j, (Φ.recJ L γ δ base z τ' j *
              ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
                unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ' ∂(fixMeasure (fun c => fixS (Φ.br c))) := by
  have hglue : ∀ p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      skelTermF D hS L γ δ base roots tt layer selSk (modalFnG Φ hS hSb Fs amp frq) fixS
        ((Φ.decSplit hS hd hL base roots).symm p) = (Zw p.1 : ℂ) *
      ∫ q, psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq p.1 p.2 q
        ∂((fixMeasure (fun c => fixS (Φ.br c))).prod
          (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    fun p => skelTerm_glueG_fix Φ RB hd hSb hL γ δ D layer tt amp frq selSk Zw hZ fixS hU p.1 p.2
  have hnorm : ∀ p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      ‖skelTermF D hS L γ δ base roots tt layer selSk (modalFnG Φ hS hSb Fs amp frq) fixS
        ((Φ.decSplit hS hd hL base roots).symm p)‖ ≤ kBoundG Φ RB hSb amp p :=
    fun p => norm_skelTerm_glueG_le_fix Φ RB hd hSb hL γ δ D layer tt amp frq selSk Zw hZ fixS hU p.1 p.2
  have hFs : Summable fun p => skelTermF D hS L γ δ base roots tt layer selSk (modalFnG Φ hS hSb Fs amp frq) fixS
      ((Φ.decSplit hS hd hL base roots).symm p) :=
    Summable.of_norm_bounded (summable_kBoundG Φ RB hSb (roots := roots) amp hsum) hnorm
  have hfib : ∀ z : GenDecoration Gsb d roots 0,
      Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
        skelTermF D hS L γ δ base roots tt layer selSk (modalFnG Φ hS hSb Fs amp frq) fixS
          ((Φ.decSplit hS hd hL base roots).symm ⟨z, κs⟩) :=
    fun z => Summable.of_norm_bounded (summable_fib_kBoundG Φ RB hSb amp z) fun κs => hnorm ⟨z, κs⟩
  have e2 := Summable.tsum_sigma' (f := fun p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      skelTermF D hS L γ δ base roots tt layer selSk (modalFnG Φ hS hSb Fs amp frq) fixS
        ((Φ.decSplit hS hd hL base roots).symm p)) hfib hFs
  have e1 := (Φ.decSplit hS hd hL base roots).symm.tsum_eq (skelTermF D hS L γ δ base roots tt layer selSk
      (modalFnG Φ hS hSb Fs amp frq) fixS)
  refine (e1.symm.trans e2).trans (tsum_congr fun z => ?_)
  have hz : ∀ κs, skelTermF D hS L γ δ base roots tt layer selSk (modalFnG Φ hS hSb Fs amp frq) fixS
      ((Φ.decSplit hS hd hL base roots).symm ⟨z, κs⟩) = (Zw z : ℂ) *
      ∫ q, psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs q
        ∂((fixMeasure (fun c => fixS (Φ.br c))).prod
          (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := fun κs => hglue ⟨z, κs⟩
  simp_rw [hz]
  rw [tsum_mul_left, fiber_sumG_fix Φ RB hd D hSb γ δ layer tt amp frq z (fun c => fixS (Φ.br c))]

/-- The pinned outer term (cf. `outer_term_eqG`): the closed spliced domain becomes the open one a.e. on the pinned
slice. -/
theorem outer_term_eqG_fix (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zw : GenDecoration Gsb d roots 0 → ℝ) (fixSb : GBranch Gsb.tree → Option ℝ)
    (hW : ∀ c v, fixSb c = some v → v ≠ (layer (D.coreBranch hS (Φ.br c)).toNode : ℝ) ∧
      v ≠ (layer (D.coreBranch hS (Φ.br c)).toNode : ℝ) + 1)
    (z : GenDecoration Gsb d roots 0) :
    (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Zw z : ℂ) *
      ∫ τ' : GBranch Gsb.tree → ℝ,
        (splicedTimeDomain Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator (fun τ' =>
          phaseProd L γ δ Gsb (cosetDecoration Gsb L base z.1) τ' *
            (∏ s, amp s (base + latticePoint L (z.1 (slotNode hSb s)))) *
              routedPhase frq (Φ.route hS hSb) tt τ' *
            ∏ j, unitKernelMG blk D hS Fs L γ δ layer base j (modLam frq (Φ.route hS hSb) j)
              (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c))
              (fun c => base + latticePoint L (z.1 (Φ.hmom hd j c)))) τ' ∂(fixMeasure fixSb) =
    (∏ j, unitConst (d := d) blk L γ δ j) * ((Zw z : ℂ) * ∫ τ' : GBranch Gsb.tree → ℝ,
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
        (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
          (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
            ∏ j, (Φ.recJ L γ δ base z τ' j *
              ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
                unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ' ∂(fixMeasure fixSb)) := by
  rw [integral_congr_ae (indicator_openSb_ae_fix Gsb _ tt fixSb hW _)]
  simp_rw [prod_unitKernelMG Φ hd D hS hSb L γ δ base Fs layer tt frq z]
  rw [← integral_const_mul, ← integral_const_mul]
  have : ∀ τ' : GBranch Gsb.tree → ℝ, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Zw z : ℂ) *
      (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
        (fun τ' => phaseProd L γ δ Gsb (cosetDecoration Gsb L base z.1) τ' *
          (∏ s, amp s (base + latticePoint L (z.1 (slotNode hSb s)))) *
            routedPhase frq (Φ.route hS hSb) tt τ' *
          ((∏ j, unitConst (d := d) blk L γ δ j) * ∏ j, (Φ.recJ L γ δ base z τ' j *
            ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
              unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ))) τ' =
      (∏ j, unitConst (d := d) blk L γ δ j) * ((Zw z : ℂ) *
        ((splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
        (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
          (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
            ∏ j, (Φ.recJ L γ δ base z τ' j *
              ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
                unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ')) := by
    intro τ'
    by_cases hp : τ' ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
    · simp only [Set.indicator_of_mem hp]
      unfold SpliceShape.sbInt
      ring
    · simp [Set.indicator_of_notMem hp]
  simp_rw [this]
  rw [integral_const_mul, integral_const_mul]

open scoped Classical in
/-- **The pinned per-mode single-state factorization with an arbitrary regional slot family** (cf.
`skelVal_modal_eq_outerValMG`): unit interiors unpinned (`hU`), pinned values off their layer-window endpoints
(`hW`). -/
theorem skelVal_modal_eq_outerValMG_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hW : ∀ b v, fixS b = some v → v ≠ (layer (D.coreBranch hS b).toNode : ℝ) ∧
      v ≠ (layer (D.coreBranch hS b).toNode : ℝ) + 1) :
    skelValF D hS L γ δ base roots tt layer selSk (modalFnG Φ hS hSb Fs amp frq) fixS =
    outerValMμ Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) (Φ.hinges hd)
      (fun z => (Zw z : ℂ)) hSb (fixMeasure (fun c => fixS (Φ.br c))) amp frq (Φ.route hS hSb) (Φ.hclk hd)
      (Φ.hmom hd) (unitKernelMG blk D hS Fs L γ δ layer base) := by
  have hs := tsum_skelTermG_fix Φ RB hd hSb hL γ δ D layer tt amp frq selSk Zw hZ hsum fixS hU
  have hC := const_splitG (d := d) Φ hd L γ δ
  rw [skelValF_eq, hs, hC]
  unfold outerValMμ
  simp_rw [outer_term_eqG_fix Φ hd D hS hSb L γ δ base Fs layer tt amp frq Zw (fun c => fixS (Φ.br c))
    (fun c v h => hW (Φ.br c) v h)]
  rw [tsum_mul_left]
  ring

end WaveTurbulence.Flower.MkSlots
