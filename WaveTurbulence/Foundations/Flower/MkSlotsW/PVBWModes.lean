/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsW.PVBW2
public import WaveTurbulence.Foundations.Flower.MkUnitsL.GenModesW

/-! # B3s-HELPER: pinned VINE-B♯ with unit top weights (3/4) — the pinned mode expansion of the outer slots

Pinned copy of the measure-dependent part of `MkUnitsL/GenModesW`, exactly as `MkSlots/PVBModes` is of
`Stage1WVine/GenModes`: the skeleton times are integrated against `fixMeasure fixS`, the `G_sb` times against
`fixMeasure fixSb` (`fixSb c = fixS (Φ.br c)`), the unit interiors against `volume`.  The pointwise mode expansion
(`hasSum_modal_prodGW`, `hasSum_modeGGW`), `modeG_eq_psiGW`, the decoration bounds (`tsum_kBoundG_leW`) and
`hasSum_tsum_interchange` are reused by import.

* `integrable_modeGGW_fix`, `integral_norm_modeGW_le_fix`, `hasSum_skelTerm_modesGW_fix`, `hasSum_skelVal_modesGW_fix`;
* **`hasSum_skelValWF_outerValMμ`**: the pinned twin of `MkUnitsL.hasSum_skelVal_outerValMGW`;
* `hasSum_skelValWF_outerValMμ_none`: with no pins it is `MkUnitsL.hasSum_skelVal_outerValMGW` (statement for
  statement). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlotsW
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkSlots (fixMeasure fixMeasure_none fixMeasure_boxQ_le
  integrable_indicator_const_of_le_one integral_indicator_const_le_of_le_one measurePreserving_timeSplit_fix
  outerValMμ outerValMμ_volume)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW psiIntGW modalFnGW unitKernelMGW modeGW skelValW
  norm_psiIntG_leW modeG_eq_psiGW hasSum_modeGGW tsum_kBoundG_leW)
open WaveTurbulence.Flower.MkUnitsL.UnitGW (kBoundGW kBoundG_nonnegW summable_kBoundGW)

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)
variable {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

theorem integrable_modeGGW_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Integrable (fun τ => modeGW blk (modalFnGW Φ hS hSb Fs amp frq) D hS L γ δ base tt layer
      (Φ.glueDec hS hd hL base z κs) τ) (fixMeasure fixS) := by
  have hi := integrable_psiIntGW_fix Φ RB hd D hSb γ δ layer tt amp frq z κs (fun c => fixS (Φ.br c))
  have hmp := measurePreserving_timeSplit_fix Φ hd fixS hU
  have := (hmp.integrable_comp_emb (Φ.timeSplit hd).measurableEmbedding).2 hi
  refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
  exact (modeG_eq_psiGW Φ hd hS hSb hL γ δ base D layer Fs tt amp frq z κs τ).symm

theorem integral_norm_modeGW_le_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ∫ τ, ‖modeGW blk (modalFnGW Φ hS hSb Fs amp frq) D hS L γ δ base tt layer (Φ.glueDec hS hd hL base z κs) τ‖
        ∂(fixMeasure fixS) ≤
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  have hmp := measurePreserving_timeSplit_fix Φ hd fixS hU
  have e : ∫ τ, ‖modeGW blk (modalFnGW Φ hS hSb Fs amp frq) D hS L γ δ base tt layer
      (Φ.glueDec hS hd hL base z κs) τ‖ ∂(fixMeasure fixS) =
      ∫ p, ‖psiIntGW Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p‖
        ∂((fixMeasure (fun c => fixS (Φ.br c))).prod
          (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
    rw [← hmp.integral_comp' (fun p => ‖psiIntGW Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p‖)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [modeG_eq_psiGW Φ hd hS hSb hL γ δ base D layer Fs tt amp frq z κs τ]
  rw [e]
  have hQ := SpliceShape.measurableSet_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have h1 := fixMeasure_boxQ_le (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
    (fun c => fixS (Φ.br c))
  have hc : 0 ≤ ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)
  refine (integral_mono (integrable_psiIntGW_fix Φ RB hd D hSb γ δ layer tt amp frq z κs _).norm
    (integrable_indicator_const_of_le_one hQ h1 _)
    fun p => norm_psiIntG_leW Φ RB hd D hSb γ δ layer tt amp frq z κs p).trans ?_
  exact integral_indicator_const_le_of_le_one hQ h1 hc

open scoped Classical in
theorem hasSum_skelTerm_modesGW_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      skelTermWF blk D hS L γ δ base roots tt layer selSk
        (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) fixS
        (Φ.glueDec hS hd hL base z κs))
      (skelTermWF blk D hS L γ δ base roots tt layer selSk Fs fixS (Φ.glueDec hS hd hL base z κs)) := by
  by_cases hs : selSk (Φ.glueDec hS hd hL base z κs)
  · set κ := Φ.glueDec hS hd hL base z κs with hκ
    simp only [skelTermWF_eq_integral, hs, ite_true]
    have : ∀ s, Countable (fam.Λ s) := fam.cnt
    set M : ℝ := ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) with hM
    have hM0 : 0 ≤ M := Finset.prod_nonneg fun j _ => RB.nonneg j _
    have hwt : Summable (modeWt fam) :=
      (hasSum_prod_real (fun s l => fam.w s l) (fun s l => fam.w_nn s l) (fun s => fam.w_sum s)).summable
    let G : (∀ s, fam.Λ s) → (GBranch S.tree → ℝ) → ℂ := fun ξ τ => ((modeWt fam ξ : ℝ) : ℂ) *
      modeGW blk (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')))
        D hS L γ δ base tt layer κ τ
    have hint : ∀ ξ, Integrable (G ξ) (fixMeasure fixS) := fun ξ =>
      (integrable_modeGGW_fix Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
        (fun s' => fam.m s' (ξ s')) fixS hU z κs).const_mul _
    have hnorm : Summable fun ξ => ∫ τ, ‖G ξ τ‖ ∂(fixMeasure fixS) := by
      refine Summable.of_nonneg_of_le (fun ξ => integral_nonneg fun τ => norm_nonneg _) (fun ξ => ?_)
        (hwt.mul_right M)
      have e1 : ∫ τ, ‖G ξ τ‖ ∂(fixMeasure fixS) = modeWt fam ξ * ∫ τ, ‖modeGW blk
          (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')))
            D hS L γ δ base tt layer κ τ‖ ∂(fixMeasure fixS) := by
        simp only [G, norm_mul, Complex.norm_real, Real.norm_of_nonneg (modeWt_nonneg fam ξ)]
        rw [integral_const_mul]
      rw [e1]
      refine mul_le_mul_of_nonneg_left
        ((integral_norm_modeGW_le_fix Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
          (fun s' => fam.m s' (ξ s')) fixS hU z κs).trans ?_) (modeWt_nonneg fam ξ)
      have hab : ampBound hSb L base (fun s' x => fam.a s' (ξ s') x) z ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun s _ => fam.a_one _ _ _
      calc _ ≤ 1 * M := mul_le_mul_of_nonneg_right hab hM0
        _ = M := one_mul _
    have key := hasSum_integral_of_summable_integral_norm hint hnorm
    have hpt : ∀ τ, ∑' ξ, G ξ τ = modeGW blk Fs D hS L γ δ base tt layer κ τ :=
      fun τ => (hasSum_modeGGW Φ hd hSb γ δ D layer tt fam Box hexp hbox κ τ).tsum_eq
    simp only [hpt] at key
    refine key.congr_fun fun ξ => ?_
    simp only [G]
    rw [integral_const_mul]
  · simp only [skelTermWF_eq_integral, hs, ite_false, mul_zero]
    exact hasSum_zero

open scoped Classical in
theorem hasSum_skelVal_modesGW_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      skelValWF blk D hS L γ δ base roots tt layer selSk
        (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) fixS)
      (skelValWF blk D hS L γ δ base roots tt layer selSk Fs fixS) := by
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
    (fun ξ κ => skelTermWF blk D hS L γ δ base roots tt layer selSk
      (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) fixS κ)
    (fun κ => skelTermWF blk D hS L γ δ base roots tt layer selSk Fs fixS κ)
    (fun ξ κ => by
      have := norm_skelTerm_glueGW_le_fix Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
        (fun s' => fam.m s' (ξ s')) selSk Zw hZ fixS hU ((Φ.decSplit hS hd hL base roots) κ).1
        ((Φ.decSplit hS hd hL base roots) κ).2
      have hκ : Φ.glueDec hS hd hL base ((Φ.decSplit hS hd hL base roots) κ).1
          ((Φ.decSplit hS hd hL base roots) κ).2 = κ := (Φ.decSplit hS hd hL base roots).symm_apply_apply κ
      rw [hκ] at this
      exact this)
    (fun κ => by
      have := hasSum_skelTerm_modesGW_fix Φ RB hd hSb hL γ δ D layer tt selSk fam Box hexp hbox fixS hU
        ((Φ.decSplit hS hd hL base roots) κ).1 ((Φ.decSplit hS hd hL base roots) κ).2
      have hκ : Φ.glueDec hS hd hL base ((Φ.decSplit hS hd hL base roots) κ).1
          ((Φ.decSplit hS hd hL base roots) κ).2 = κ := (Φ.decSplit hS hd hL base roots).symm_apply_apply κ
      rwa [hκ] at this)
  have h2 := key.mul_left ((coupling d L γ δ : ℂ) ^ S.order * S.zeta)
  rw [skelValWF_eq]
  convert h2 using 1
  funext ξ
  rw [skelValWF_eq]
  ring

open scoped Classical in
/-- **The pinned mode form of the skeleton value with unit top weights** (the pinned twin of
`MkUnitsL.hasSum_skelVal_outerValMGW`): the skeleton core integral is against `fixMeasure fixS`, the outer `G_sb`
integral against `fixMeasure` of the pins of the old names `Φ.br c`, the unit-interior integrals (inside
`unitKernelMGW`, which also carries the unit top weights `Fs.tw`) against Lebesgue measure.  Extra hypotheses: `hU` —
no unit-interior branch is pinned (`inter blk j` = the atoms of unit `j` other than its upper joint); `hW` — no pinned
value is an endpoint of its layer window. -/
theorem hasSum_skelValWF_outerValMμ (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hW : ∀ b v, fixS b = some v → v ≠ (layer (D.coreBranch hS b).toNode : ℝ) ∧
      v ≠ (layer (D.coreBranch hS b).toNode : ℝ) + 1) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValMμ Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) (Φ.hinges hd)
        (fun z => (Zw z : ℂ)) hSb (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWF blk D hS L γ δ base roots tt layer selSk Fs fixS) := by
  have key := hasSum_skelVal_modesGW_fix Φ RB hd hSb hL0 γ δ D layer tt selSk Zw hZ fam Box hexp hbox fixS hU
  refine key.congr_fun fun ξ => ?_
  rw [skelVal_modal_eq_outerValMGW_fix Φ RB hd hSb hL0.ne' γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
    (fun s' => fam.m s' (ξ s')) selSk Zw hZ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1 fixS hU hW]

open scoped Classical in
/-- **No pins**: `hasSum_skelValWF_outerValMμ` at `fixS = fun _ => none` has exactly the statement of
`MkUnitsL.hasSum_skelVal_outerValMGW` (`skelValW`, main's `outerValM`). -/
theorem hasSum_skelValWF_outerValMμ_none (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
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
  have h := hasSum_skelValWF_outerValMμ Φ RB hd hSb hL0 γ δ D layer tt selSk Zw hZ fam Box hexp hbox
    (fun _ => none) (fun _ _ _ => rfl) (fun _ v h => absurd h (by simp))
  rw [skelValWF_none] at h
  have hfix : fixMeasure (fun c : GBranch Gsb.tree => (fun _ : GBranch S.tree => (none : Option ℝ)) (Φ.br c)) =
      volume := fixMeasure_none
  simp only [hfix, outerValMμ_volume] at h
  exact h

end WaveTurbulence.Flower.MkSlotsW
