/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBR4

/-! # B3s-HELPER3 B2 (5): the relaxed pinned VINE-B♯ with unit top weights — the mode expansion

Domain-generic copy of `MkSlotsW/PVBWModes` (the pinned copy of `MkUnitsL/GenModesW`), with the glue identity used
`fixMeasure fixS`-a.e. (`modeGWD_glue_ae`) and the slot boxes required only on the pinned slice of the core domain
(`hbox`).

* `integrable_modeGGWD_fix`, `integral_norm_modeGWD_le_fix`, `hasSum_modeGGWD`, `hasSum_skelTerm_modesGWD_fix`,
  `hasSum_skelVal_modesGWD_fix`, `hasSum_skelValWD_outerValMμD` (generic domains);
* **`hasSum_skelValWFRL_outerValMμD`**: the relaxed pinned VINE-B♯ with lower bounds (ruling R187);
* **`hasSum_skelValWFRL_outerValMμD_lbnone`** = **`hasSum_skelValWFR_outerValMμD`**: without lower bounds;
* `hasSum_skelValWFR_outerValMμD_none`: without pins it is exactly `MkUnitsL.hasSum_skelVal_outerValMGW`.

Deviation from the MkSlotsW binders (necessary, see the docstring of `hasSum_skelValWFR_outerValMμD`): `hbox` is
required on the pinned slice of the RELAXED core domain instead of on `coreTimeDomainW`. -/

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
  WaveTurbulence.VineB WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkSlots (fixMeasure fixMeasure_none integrable_indicator_const_of_le_one
  integral_indicator_const_le_of_le_one measurePreserving_timeSplit_fix outerValMμ outerValMμD outerValMμ_volume
  outerValMμ_eq_D)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW modalFnGW unitKernelMGW skelValW hasSum_modal_prodGW
  topW_modalFnGW tsum_kBoundG_leW)
open WaveTurbulence.Flower.MkUnitsL.UnitGW (kBoundGW kBoundG_nonnegW summable_kBoundGW)

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)
variable {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

theorem integrable_modeGGWD_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Integrable (fun τ => modeGWD blk (modalFnGW Φ hS hSb Fs amp frq) hS L γ δ base tt A
      (Φ.glueDec hS hd hL base z κs) τ) (fixMeasure fixS) := by
  have hi := integrable_psiIntGWD_fix Φ RB hd D hSb γ δ layer tt amp frq z κs (fun c => fixS (Φ.br c)) hG.meas
    hG.mass
  have hmp := measurePreserving_timeSplit_fix Φ hd fixS hU
  have := (hmp.integrable_comp_emb (Φ.timeSplit hd).measurableEmbedding).2 hi
  exact this.congr ((modeGWD_glue_ae Φ hd hSb hL γ δ D layer tt amp frq fixS hG z κs).mono fun τ h => h.symm)

theorem integral_norm_modeGWD_le_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ∫ τ, ‖modeGWD blk (modalFnGW Φ hS hSb Fs amp frq) hS L γ δ base tt A (Φ.glueDec hS hd hL base z κs) τ‖
        ∂(fixMeasure fixS) ≤
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  have hmp := measurePreserving_timeSplit_fix Φ hd fixS hU
  have e : ∫ τ, ‖modeGWD blk (modalFnGW Φ hS hSb Fs amp frq) hS L γ δ base tt A
      (Φ.glueDec hS hd hL base z κs) τ‖ ∂(fixMeasure fixS) =
      ∫ p, ‖psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B p‖
        ∂((fixMeasure (fun c => fixS (Φ.br c))).prod
          (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
    rw [← hmp.integral_comp' (fun p => ‖psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B p‖)]
    exact integral_congr_ae ((modeGWD_glue_ae Φ hd hSb hL γ δ D layer tt amp frq fixS hG z κs).mono
      fun τ h => congrArg norm h)
  rw [e]
  have hQ := measurableSet_boxQD (blk := blk) D hS layer hG.meas
  have h1 := fixMeasure_boxQD_le (blk := blk) D hS layer (fun c => fixS (Φ.br c)) hG.mass
  have hc : 0 ≤ ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)
  refine (integral_mono (integrable_psiIntGWD_fix Φ RB hd D hSb γ δ layer tt amp frq z κs _ hG.meas hG.mass).norm
    (integrable_indicator_const_of_le_one hQ h1 _)
    fun p => norm_psiIntGWD_le Φ RB hd D hSb γ δ layer tt amp frq z κs B p).trans ?_
  exact integral_indicator_const_le_of_le_one hQ h1 hc

open scoped Classical in
/-- The pointwise mode expansion of the skeleton integrand on the domain `A`, at a time vector whose slot times are in
the boxes as soon as it is in `A`. -/
theorem hasSum_modeGGWD (hd : Disj blk) (hSb : Gsb.IsPlain) (γ δ : ℝ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (A : Set (GBranch S.tree → ℝ)) (κ : GenDecoration S d roots 0) (τ : GBranch S.tree → ℝ)
    (hτbox : τ ∈ A → ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      modeGWD blk (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')))
        hS L γ δ base tt A κ τ)
      (modeGWD blk Fs hS L γ δ base tt A κ τ) := by
  by_cases hτ : τ ∈ A
  · have hm := hasSum_modal_prodGW Φ hd hS hSb Fs fam tt τ (fun x => base + latticePoint L (κ.1 x)) Box hexp
      (hτbox hτ)
    have h2 := hm.mul_left ((epsDec S κ.1 : ℂ) * phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
      MkUnitsL.topW blk Fs L base κ.1)
    unfold modeGWD
    simp only [Set.indicator_of_mem hτ, topW_modalFnGW]
    convert h2 using 1
    · funext ξ; ring
    · ring
  · unfold modeGWD
    simp only [Set.indicator_of_notMem hτ, mul_zero]
    exact hasSum_zero

open scoped Classical in
theorem hasSum_skelTerm_modesGWD_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (hbox : ∀ τ, PinnedAt fixS τ → τ ∈ A → ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      skelTermWD blk hS L γ δ base roots tt selSk
        (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) A fixS
        (Φ.glueDec hS hd hL base z κs))
      (skelTermWD blk hS L γ δ base roots tt selSk Fs A fixS (Φ.glueDec hS hd hL base z κs)) := by
  by_cases hs : selSk (Φ.glueDec hS hd hL base z κs)
  · set κ := Φ.glueDec hS hd hL base z κs with hκ
    simp only [skelTermWD_eq_integral, hs, ite_true]
    have : ∀ s, Countable (fam.Λ s) := fam.cnt
    set M : ℝ := ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) with hM
    have hM0 : 0 ≤ M := Finset.prod_nonneg fun j _ => RB.nonneg j _
    have hwt : Summable (modeWt fam) :=
      (hasSum_prod_real (fun s l => fam.w s l) (fun s l => fam.w_nn s l) (fun s => fam.w_sum s)).summable
    let G : (∀ s, fam.Λ s) → (GBranch S.tree → ℝ) → ℂ := fun ξ τ => ((modeWt fam ξ : ℝ) : ℂ) *
      modeGWD blk (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')))
        hS L γ δ base tt A κ τ
    have hint : ∀ ξ, Integrable (G ξ) (fixMeasure fixS) := fun ξ =>
      (integrable_modeGGWD_fix Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
        (fun s' => fam.m s' (ξ s')) fixS hU hG z κs).const_mul _
    have hnorm : Summable fun ξ => ∫ τ, ‖G ξ τ‖ ∂(fixMeasure fixS) := by
      refine Summable.of_nonneg_of_le (fun ξ => integral_nonneg fun τ => norm_nonneg _) (fun ξ => ?_)
        (hwt.mul_right M)
      have e1 : ∫ τ, ‖G ξ τ‖ ∂(fixMeasure fixS) = modeWt fam ξ * ∫ τ, ‖modeGWD blk
          (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')))
            hS L γ δ base tt A κ τ‖ ∂(fixMeasure fixS) := by
        simp only [G, norm_mul, Complex.norm_real, Real.norm_of_nonneg (modeWt_nonneg fam ξ)]
        rw [integral_const_mul]
      rw [e1]
      refine mul_le_mul_of_nonneg_left
        ((integral_norm_modeGWD_le_fix Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
          (fun s' => fam.m s' (ξ s')) fixS hU hG z κs).trans ?_) (modeWt_nonneg fam ξ)
      have hab : ampBound hSb L base (fun s' x => fam.a s' (ξ s') x) z ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun s _ => fam.a_one _ _ _
      calc _ ≤ 1 * M := mul_le_mul_of_nonneg_right hab hM0
        _ = M := one_mul _
    have key := hasSum_integral_of_summable_integral_norm hint hnorm
    have hpt : (fun τ => ∑' ξ, G ξ τ) =ᵐ[fixMeasure fixS] fun τ => modeGWD blk Fs hS L γ δ base tt A κ τ := by
      filter_upwards [ae_pinnedAt fixS] with τ hτ
      exact (hasSum_modeGGWD Φ hd hSb γ δ tt fam Box hexp A κ τ (hbox τ hτ)).tsum_eq
    rw [integral_congr_ae hpt] at key
    refine key.congr_fun fun ξ => ?_
    simp only [G]
    rw [integral_const_mul]
  · simp only [skelTermWD_eq_integral, hs, ite_false, mul_zero]
    exact hasSum_zero

open scoped Classical in
theorem hasSum_skelVal_modesGWD_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (hbox : ∀ τ, PinnedAt fixS τ → τ ∈ A → ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      skelValWD blk hS L γ δ base roots tt selSk
        (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) A fixS)
      (skelValWD blk hS L γ δ base roots tt selSk Fs A fixS) := by
  have hL : L ≠ 0 := hL0.ne'
  have hcnt : ∀ s, Countable (fam.Λ s) := fam.cnt
  have hwt : Summable (modeWt fam) :=
    (hasSum_prod_real (fun s l => fam.w s l) (fun s l => fam.w_nn s l) (fun s => fam.w_sum s)).summable
  have key := hasSum_tsum_interchange (modeWt fam) (modeWt_nonneg fam) hwt (Φ.decSplit hS hd hL base roots)
    (fun ξ p => kBoundGW Φ RB hSb (fun s' x => fam.a s' (ξ s') x) p)
    (fun ξ p => kBoundG_nonnegW Φ RB hSb _ p)
    (fun ξ => summable_kBoundGW Φ RB hSb (roots := roots) _ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1)
    ((((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair Gsb) : ℕ) * ∏ j, RB.lbC j)
    (fun ξ => tsum_kBoundG_leW Φ RB hSb _ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1 _
      (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).2)
    (fun ξ κ => skelTermWD blk hS L γ δ base roots tt selSk
      (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) A fixS κ)
    (fun κ => skelTermWD blk hS L γ δ base roots tt selSk Fs A fixS κ)
    (fun ξ κ => by
      have := norm_skelTerm_glueGWD_le_fix Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
        (fun s' => fam.m s' (ξ s')) selSk Zw hZ fixS hU hG ((Φ.decSplit hS hd hL base roots) κ).1
        ((Φ.decSplit hS hd hL base roots) κ).2
      have hκ : Φ.glueDec hS hd hL base ((Φ.decSplit hS hd hL base roots) κ).1
          ((Φ.decSplit hS hd hL base roots) κ).2 = κ := (Φ.decSplit hS hd hL base roots).symm_apply_apply κ
      rw [hκ] at this
      exact this)
    (fun κ => by
      have := hasSum_skelTerm_modesGWD_fix Φ RB hd hSb hL γ δ D layer tt selSk fam Box hexp fixS hU hG hbox
        ((Φ.decSplit hS hd hL base roots) κ).1 ((Φ.decSplit hS hd hL base roots) κ).2
      have hκ : Φ.glueDec hS hd hL base ((Φ.decSplit hS hd hL base roots) κ).1
          ((Φ.decSplit hS hd hL base roots) κ).2 = κ := (Φ.decSplit hS hd hL base roots).symm_apply_apply κ
      rwa [hκ] at this)
  have h2 := key.mul_left ((coupling d L γ δ : ℂ) ^ S.order * S.zeta)
  rw [skelValWD]
  convert h2 using 1
  funext ξ
  rw [skelValWD]
  ring

open scoped Classical in
/-- **The pinned mode form on general domains**: core domain `A`, `G_sb` domain `B` (`hG`), outer domain `Dom`
a.e. equal to `B` (`hDB`). -/
theorem hasSum_skelValWD_outerValMμD (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (Dom : Set (GBranch Gsb.tree → ℝ))
    (hDB : ∀ᵐ τ' ∂(fixMeasure (fun c => fixS (Φ.br c))), τ' ∈ Dom ↔ τ' ∈ B)
    (hbox : ∀ τ, PinnedAt fixS τ → τ ∈ A → ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValMμD Gsb L γ δ base roots tt Dom (Φ.hinges hd) (fun z => (Zw z : ℂ)) hSb
        (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWD blk hS L γ δ base roots tt selSk Fs A fixS) := by
  have key := hasSum_skelVal_modesGWD_fix Φ RB hd hSb hL0 γ δ D layer tt selSk Zw hZ fam Box hexp fixS hU hG hbox
  refine key.congr_fun fun ξ => ?_
  rw [skelVal_modal_eq_outerValMGWD_fix Φ RB hd hSb hL0.ne' γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
    (fun s' => fam.m s' (ξ s')) selSk Zw hZ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1 fixS hU hG Dom hDB]

/-! ## The relaxed pinned VINE-B♯ -/

open scoped Classical in
/-- **The relaxed pinned VINE-B♯ with unit top weights and lower bounds** (B2 + ruling R187): the twin of
`MkSlotsW.hasSum_skelValWF_outerValMμ` with the relaxed core domain `coreTimeDomainWR … fixS ∩ lbDomR lbS` in the
skeleton value (`skelValWFRL`) and main's relaxed spliced domain `splicedTimeDomainFix … (fixS ∘ Φ.br) ∩
lbDomR (lbS ∘ Φ.br)` in the conclusion. Against MkSlotsW: `hW` dropped; `lbS`, `hlbU` (no lower bound at a unit
interior) and the pin hypotheses `hP` (`val`, `mono`) added; `hbox` on the pinned slice of the relaxed core domain. -/
theorem hasSum_skelValWFRL_outerValMμD (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValMμD Gsb L γ δ base roots tt
        (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
          lbDomR (fun c => lbS (Φ.br c)))
        (Φ.hinges hd) (fun z => (Zw z : ℂ)) hSb (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWFRL blk D hS L γ δ base roots tt layer selSk Fs fixS lbS) :=
  hasSum_skelValWD_outerValMμD Φ RB hd hSb hL0 γ δ D layer tt selSk Zw hZ fam Box hexp fixS hU
    (GlueDomR.relaxedLB Φ hd D hS layer tt fixS lbS hU hlbU hP) _
    (ae_mem_splicedTimeDomainFix_lb_iff Gsb _ tt _ _) hbox

open scoped Classical in
/-- **No lower bounds** (`lbS ≡ none`): the relaxed pinned VINE-B♯ of B2. -/
theorem hasSum_skelValWFRL_outerValMμD_lbnone (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (hSb : Gsb.IsPlain) (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ → τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS →
      ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValMμD Gsb L γ δ base roots tt
        (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)))
        (Φ.hinges hd) (fun z => (Zw z : ℂ)) hSb (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWFR blk D hS L γ δ base roots tt layer selSk Fs fixS) := by
  have h := hasSum_skelValWFRL_outerValMμD Φ RB hd hSb hL0 γ δ D layer tt selSk Zw hZ fam Box hexp fixS
    (fun _ => none) hU (fun _ _ _ => rfl) hP (fun τ hτ h' => hbox τ hτ h'.1)
  rw [skelValWFRL_lbnone] at h
  simpa only [lbDomR_none, Set.inter_univ] using h

open scoped Classical in
/-- **The relaxed pinned VINE-B♯ with unit top weights** (Deliverable B2): `MkSlotsW.hasSum_skelValWF_outerValMμ`
with the relaxed core domain in the skeleton value (`skelValWFR`) and the conclusion on main's relaxed spliced domain
`splicedTimeDomainFix Gsb … (fun c => fixS (Φ.br c))` (`MkSlots.outerValMμD`). Against the MkSlotsW binders: `hW`
dropped; the pin hypotheses `hP : RelaxPinsS …` (`val`: `layer < v ≤ layer + 1`, `v ≤ tt`; `mono`: monotone along
skeleton ancestry) added; `hbox` is required on the pinned slice of the RELAXED core domain. This is necessary: the
relaxed slice contains slot times never attained on `coreTimeDomainW` (a pin at `layer + 1` or at `tt`; a pinned
chain-slot top equal to its pinned clock, slot times `(s, s)`, outside main's `slotBox` = `timeBoxGt`), where `hexp`
says nothing about `Fs`; changing `Fs.fs` there keeps MkSlotsW's `hbox`/`hexp` and the mode side, but changes
`skelValWFR` on a set of positive pinned measure. -/
theorem hasSum_skelValWFR_outerValMμD (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ → τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS →
      ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValMμD Gsb L γ δ base roots tt
        (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)))
        (Φ.hinges hd) (fun z => (Zw z : ℂ)) hSb (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWFR blk D hS L γ δ base roots tt layer selSk Fs fixS) :=
  hasSum_skelValWFRL_outerValMμD_lbnone Φ RB hd hSb hL0 γ δ D layer tt selSk Zw hZ fam Box hexp fixS hU hP hbox

/-- Without pins the relaxed spliced domain is main's closed spliced domain. -/
theorem splicedTimeDomainFix_none (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ) :
    splicedTimeDomainFix G layer tt (fun _ => none) = splicedTimeDomain G layer tt := by
  ext t
  simp only [splicedTimeDomainFix, splicedTimeDomain, true_or, forall_const, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun v => (h1 v).1, h2, fun v => (h1 v).2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun v => ⟨h1 v, h3 v⟩, h2⟩

open scoped Classical in
/-- **No pins**: `hasSum_skelValWFR_outerValMμD` at `fixS = fun _ => none` has exactly the statement of
`MkUnitsL.hasSum_skelVal_outerValMGW`. -/
theorem hasSum_skelValWFR_outerValMμD_none (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) (Φ.hinges hd) Zw hSb
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValW blk D hS L γ δ base roots tt layer selSk Fs) := by
  have h := hasSum_skelValWFR_outerValMμD Φ RB hd hSb hL0 γ δ D layer tt selSk Zw hZ fam Box hexp
    (fun _ => none) (fun _ _ _ => rfl) ⟨fun _ _ h => absurd h (by simp), fun _ _ _ _ h => absurd h (by simp)⟩
    (fun τ _ hτ => hbox τ (by rwa [coreTimeDomainWR_none] at hτ))
  rw [skelValWFR_none] at h
  have hfix : fixMeasure (fun c : GBranch Gsb.tree => (fun _ : GBranch S.tree => (none : Option ℝ)) (Φ.br c)) =
      volume := fixMeasure_none
  simp only [hfix, splicedTimeDomainFix_none, ← outerValMμ_eq_D, outerValMμ_volume] at h
  exact h

end WaveTurbulence.Flower.MkSlotsB
