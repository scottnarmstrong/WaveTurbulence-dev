/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PVB2
public import WaveTurbulence.Foundations.Flower.Stage1WVine.GenModes

/-! # B3s MK-SLOTS: pinned VINE-B♯ (3/4) — the pinned mode expansion of the outer slots

Pinned copy of the measure-dependent part of `Stage1WVine/GenModes`: the skeleton times are integrated against
`fixMeasure fixS`, the `G_sb` times against `fixMeasure fixSb` (`fixSb c = fixS (Φ.br c)`), the unit interiors against
`volume`. The pointwise mode expansion (`hasSum_modal_prodG`, `hasSum_modeGG`), `modeG_eq_psiG`, the decoration
bounds and `hasSum_tsum_interchange` are reused by import.

* `skelTermF_eq_integral`, `integrable_modeGG_fix`, `integral_norm_modeG_leG_fix`, `hasSum_skelTerm_modesG_fix`,
  `hasSum_skelVal_modesG_fix`;
* **`hasSum_skelValF_outerValMμ`**: the pinned twin of `hasSum_skelVal_outerValMG`;
* `hasSum_skelValF_outerValMμ_none`: with no pins it is `hasSum_skelVal_outerValMG` (statement for statement). -/

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
  WaveTurbulence.VineB WaveTurbulence.RepAnalytic WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.Stage1WVine.UnitG

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

open scoped Classical in
/-- The pinned skeleton term is the pinned integral of main's `modeG` (cf. `Represents.skelTerm_eq_integral`). -/
theorem skelTermF_eq_integral (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (selSk : GenDecoration S d roots 0 → Prop)
    (fixS : GBranch S.tree → Option ℝ) (κ : GenDecoration S d roots 0) :
    skelTermF D hS L γ δ base roots tt layer selSk Fs fixS κ =
      if selSk κ then ∫ τ, modeG Fs D hS L γ δ base tt layer κ τ ∂(fixMeasure fixS) else 0 := by
  unfold skelTermF modeG
  split_ifs
  · rw [integral_const_mul]
  · rfl

variable (Φ : SpliceShape blk Gsb)
variable {hS : S.IsPlain} {Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ} {L : ℝ} {base : Mom d}

theorem integrable_modeGG_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Integrable (fun τ => modeG (modalFnG Φ hS hSb Fs amp frq) D hS L γ δ base tt layer
      (Φ.glueDec hS hd hL base z κs) τ) (fixMeasure fixS) := by
  have hi := integrable_psiIntG_fix Φ RB hd D hSb γ δ layer tt amp frq z κs (fun c => fixS (Φ.br c))
  have hmp := measurePreserving_timeSplit_fix Φ hd fixS hU
  have := (hmp.integrable_comp_emb (Φ.timeSplit hd).measurableEmbedding).2 hi
  refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
  exact (modeG_eq_psiG Φ hd hS hSb hL γ δ base D layer Fs tt amp frq z κs τ).symm

theorem integral_norm_modeG_leG_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ∫ τ, ‖modeG (modalFnG Φ hS hSb Fs amp frq) D hS L γ δ base tt layer (Φ.glueDec hS hd hL base z κs) τ‖
        ∂(fixMeasure fixS) ≤
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  have hmp := measurePreserving_timeSplit_fix Φ hd fixS hU
  have e : ∫ τ, ‖modeG (modalFnG Φ hS hSb Fs amp frq) D hS L γ δ base tt layer (Φ.glueDec hS hd hL base z κs) τ‖
      ∂(fixMeasure fixS) =
      ∫ p, ‖psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p‖
        ∂((fixMeasure (fun c => fixS (Φ.br c))).prod
          (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
    rw [← hmp.integral_comp' (fun p => ‖psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p‖)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [modeG_eq_psiG Φ hd hS hSb hL γ δ base D layer Fs tt amp frq z κs τ]
  rw [e]
  have hQ := SpliceShape.measurableSet_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have h1 := fixMeasure_boxQ_le (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
    (fun c => fixS (Φ.br c))
  have hc : 0 ≤ ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)
  refine (integral_mono (integrable_psiIntG_fix Φ RB hd D hSb γ δ layer tt amp frq z κs _).norm
    (integrable_indicator_const_of_le_one hQ h1 _)
    fun p => norm_psiIntG_le Φ RB hd D hSb γ δ layer tt amp frq z κs p).trans ?_
  exact integral_indicator_const_le_of_le_one hQ h1 hc

open scoped Classical in
theorem hasSum_skelTerm_modesG_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      skelTermF D hS L γ δ base roots tt layer selSk
        (modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) fixS
        (Φ.glueDec hS hd hL base z κs))
      (skelTermF D hS L γ δ base roots tt layer selSk Fs fixS (Φ.glueDec hS hd hL base z κs)) := by
  by_cases hs : selSk (Φ.glueDec hS hd hL base z κs)
  · set κ := Φ.glueDec hS hd hL base z κs with hκ
    simp only [skelTermF_eq_integral, hs, ite_true]
    have : ∀ s, Countable (fam.Λ s) := fam.cnt
    set M : ℝ := ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) with hM
    have hM0 : 0 ≤ M := Finset.prod_nonneg fun j _ => RB.nonneg j _
    have hwt : Summable (modeWt fam) :=
      (hasSum_prod_real (fun s l => fam.w s l) (fun s l => fam.w_nn s l) (fun s => fam.w_sum s)).summable
    let G : (∀ s, fam.Λ s) → (GBranch S.tree → ℝ) → ℂ := fun ξ τ => ((modeWt fam ξ : ℝ) : ℂ) *
      modeG (modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')))
        D hS L γ δ base tt layer κ τ
    have hint : ∀ ξ, Integrable (G ξ) (fixMeasure fixS) := fun ξ =>
      (integrable_modeGG_fix Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
        (fun s' => fam.m s' (ξ s')) fixS hU z κs).const_mul _
    have hnorm : Summable fun ξ => ∫ τ, ‖G ξ τ‖ ∂(fixMeasure fixS) := by
      refine Summable.of_nonneg_of_le (fun ξ => integral_nonneg fun τ => norm_nonneg _) (fun ξ => ?_)
        (hwt.mul_right M)
      have e1 : ∫ τ, ‖G ξ τ‖ ∂(fixMeasure fixS) = modeWt fam ξ * ∫ τ, ‖modeG
          (modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')))
            D hS L γ δ base tt layer κ τ‖ ∂(fixMeasure fixS) := by
        simp only [G, norm_mul, Complex.norm_real, Real.norm_of_nonneg (modeWt_nonneg fam ξ)]
        rw [integral_const_mul]
      rw [e1]
      refine mul_le_mul_of_nonneg_left
        ((integral_norm_modeG_leG_fix Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
          (fun s' => fam.m s' (ξ s')) fixS hU z κs).trans ?_) (modeWt_nonneg fam ξ)
      have hab : ampBound hSb L base (fun s' x => fam.a s' (ξ s') x) z ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun s _ => fam.a_one _ _ _
      calc _ ≤ 1 * M := mul_le_mul_of_nonneg_right hab hM0
        _ = M := one_mul _
    have key := hasSum_integral_of_summable_integral_norm hint hnorm
    have hpt : ∀ τ, ∑' ξ, G ξ τ = modeG Fs D hS L γ δ base tt layer κ τ :=
      fun τ => (hasSum_modeGG Φ hd hSb γ δ D layer tt fam Box hexp hbox κ τ).tsum_eq
    simp only [hpt] at key
    refine key.congr_fun fun ξ => ?_
    simp only [G]
    rw [integral_const_mul]
  · simp only [skelTermF_eq_integral, hs, ite_false, mul_zero]
    exact hasSum_zero

open scoped Classical in
theorem hasSum_skelVal_modesG_fix (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      skelValF D hS L γ δ base roots tt layer selSk
        (modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) fixS)
      (skelValF D hS L γ δ base roots tt layer selSk Fs fixS) := by
  have hL : L ≠ 0 := hL0.ne'
  have hcnt : ∀ s, Countable (fam.Λ s) := fam.cnt
  have hwt : Summable (modeWt fam) :=
    (hasSum_prod_real (fun s l => fam.w s l) (fun s l => fam.w_nn s l) (fun s => fam.w_sum s)).summable
  have key := hasSum_tsum_interchange (modeWt fam) (modeWt_nonneg fam) hwt (Φ.decSplit hS hd hL base roots)
    (fun ξ p => kBoundG Φ RB hSb (fun s' x => fam.a s' (ξ s') x) p)
    (fun ξ p => kBoundG_nonneg Φ RB hSb _ p)
    (fun ξ => summable_kBoundG Φ RB hSb (roots := roots) _ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1)
    ((((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair Gsb) : ℕ) * ∏ j, RB.lbC j)
    (fun ξ => tsum_kBoundG_le Φ RB hSb _ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1 _
      (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).2)
    (fun ξ κ => skelTermF D hS L γ δ base roots tt layer selSk
      (modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) fixS κ)
    (fun κ => skelTermF D hS L γ δ base roots tt layer selSk Fs fixS κ)
    (fun ξ κ => by
      have := norm_skelTerm_glueG_le_fix Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
        (fun s' => fam.m s' (ξ s')) selSk Zw hZ fixS hU ((Φ.decSplit hS hd hL base roots) κ).1
        ((Φ.decSplit hS hd hL base roots) κ).2
      have hκ : Φ.glueDec hS hd hL base ((Φ.decSplit hS hd hL base roots) κ).1
          ((Φ.decSplit hS hd hL base roots) κ).2 = κ := (Φ.decSplit hS hd hL base roots).symm_apply_apply κ
      rw [hκ] at this
      exact this)
    (fun κ => by
      have := hasSum_skelTerm_modesG_fix Φ RB hd hSb hL γ δ D layer tt selSk fam Box hexp hbox fixS hU
        ((Φ.decSplit hS hd hL base roots) κ).1 ((Φ.decSplit hS hd hL base roots) κ).2
      have hκ : Φ.glueDec hS hd hL base ((Φ.decSplit hS hd hL base roots) κ).1
          ((Φ.decSplit hS hd hL base roots) κ).2 = κ := (Φ.decSplit hS hd hL base roots).symm_apply_apply κ
      rwa [hκ] at this)
  have h2 := key.mul_left ((coupling d L γ δ : ℂ) ^ S.order * S.zeta)
  rw [skelValF_eq]
  convert h2 using 1
  funext ξ
  rw [skelValF_eq]
  ring

open scoped Classical in
/-- **The pinned mode form of the skeleton expression with an arbitrary slot family** (the pinned twin of
`Stage1WVine.hasSum_skelVal_outerValMG`): the skeleton core integral is against `fixMeasure fixS`, the outer `G_sb`
integral against `fixMeasure` of the pins of the old names `Φ.br c`, the unit-interior integrals (inside
`unitKernelMG`) against Lebesgue measure. Extra hypotheses: `hU` — no unit-interior branch is pinned (`inter blk j` =
the atoms of unit `j` other than its upper joint, the old name of the hinge); `hW` — no pinned value is an endpoint of
its layer window. -/
theorem hasSum_skelValF_outerValMμ (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hW : ∀ b v, fixS b = some v → v ≠ (layer (D.coreBranch hS b).toNode : ℝ) ∧
      v ≠ (layer (D.coreBranch hS b).toNode : ℝ) + 1) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValMμ Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) (Φ.hinges hd)
        (fun z => (Zw z : ℂ)) hSb (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMG blk D hS Fs L γ δ layer base))
      (skelValF D hS L γ δ base roots tt layer selSk Fs fixS) := by
  have key := hasSum_skelVal_modesG_fix Φ RB hd hSb hL0 γ δ D layer tt selSk Zw hZ fam Box hexp hbox fixS hU
  refine key.congr_fun fun ξ => ?_
  rw [skelVal_modal_eq_outerValMG_fix Φ RB hd hSb hL0.ne' γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
    (fun s' => fam.m s' (ξ s')) selSk Zw hZ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1 fixS hU hW]

open scoped Classical in
/-- **No pins**: `hasSum_skelValF_outerValMμ` at `fixS = fun _ => none` is exactly the statement of
`Stage1WVine.hasSum_skelVal_outerValMG` (main's `skelVal`, main's `outerValM`). -/
theorem hasSum_skelValF_outerValMμ_none (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) (Φ.hinges hd) Zw hSb
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMG blk D hS Fs L γ δ layer base))
      (skelVal D hS L γ δ base roots tt layer selSk Fs) := by
  have h := hasSum_skelValF_outerValMμ Φ RB hd hSb hL0 γ δ D layer tt selSk Zw hZ fam Box hexp hbox
    (fun _ => none) (fun _ _ _ => rfl) (fun _ v h => absurd h (by simp))
  rw [skelValF_none] at h
  have hfix : fixMeasure (fun c : GBranch Gsb.tree => (fun _ : GBranch S.tree => (none : Option ℝ)) (Φ.br c)) =
      volume := fixMeasure_none
  simp only [hfix, outerValMμ_volume] at h
  exact h

end WaveTurbulence.Flower.MkSlots
