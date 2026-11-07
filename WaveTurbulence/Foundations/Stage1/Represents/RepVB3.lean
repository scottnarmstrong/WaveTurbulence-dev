/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB2
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: the skeleton term is the weighted sum of the per-mode terms

`modeG`: the skeleton integrand with the factor `ε` (for a slot family `Fs`).  `modeG_modal_eq_psi`: for a modal family it is
VINE-B♯'s `psiInt` along the time split; hence integrable with `∫‖·‖ ≤ ampBound · ∏ unitLb`.  `hasSum_skelTerm_modes`: at every
glued decoration, `skelTerm(slotFn) = Σ_ξ w_ξ skelTerm(modalFn_ξ)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineB WaveTurbulence.VineEstS3.FS WaveTurbulence.RegRed WaveTurbulence.RedSplice
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS4 MeasureTheory

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

open scoped Classical in
/-- The skeleton integrand at a decoration, with the sign factor. -/
noncomputable def modeG (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (κ : GenDecoration S d roots 0) (τ : GBranch S.tree → ℝ) : ℂ :=
  (epsDec S κ.1 : ℂ) * (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
    (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
      ∏ s, Fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) τ

open scoped Classical in
theorem skelTerm_eq_integral (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (selSk : GenDecoration S d roots 0 → Prop) (κ : GenDecoration S d roots 0) :
    skelTerm D hS L γ δ base roots tt layer selSk Fs κ =
      if selSk κ then ∫ τ, modeG Fs D hS L γ δ base tt layer κ τ else 0 := by
  unfold skelTerm modeG
  split_ifs
  · rw [integral_const_mul]
  · rfl

variable (Φ : SpliceShape blk Gsb)

open scoped Classical in
theorem modeG_eq_psi (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) (τ : GBranch S.tree → ℝ) :
    modeG (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer amp frq)
      D hS L γ δ base tt layer (Φ.glueDec hS hd hL base z κs) τ =
    Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs (Φ.timeSplit hd τ) := by
  have := Φ.integrand_glue hd hS hSb hL γ δ base D layer hLayer h tt amp frq z κs (Φ.timeSplit hd τ).1
    (Φ.timeSplit hd τ).2
  rw [show Φ.glueTime hd (Φ.timeSplit hd τ).1 (Φ.timeSplit hd τ).2 = τ from by
    rw [← Φ.timeSplit_symm hd]; exact (Φ.timeSplit hd).symm_apply_apply τ] at this
  exact this

theorem integrable_modeG (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Integrable (fun τ => modeG
      (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer amp frq)
      D hS L γ δ base tt layer (Φ.glueDec hS hd hL base z κs) τ) := by
  have hi := Φ.integrable_psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs
  have hmp := Φ.measurePreserving_timeSplit hd
  have := (hmp.integrable_comp_emb (Φ.timeSplit hd).measurableEmbedding).2 hi
  refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
  exact (modeG_eq_psi Φ hd hS hSb hL γ δ base D layer hLayer h tt amp frq z κs τ).symm

theorem integral_norm_modeG_le (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ∫ τ, ‖modeG
      (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer amp frq)
      D hS L γ δ base tt layer (Φ.glueDec hS hd hL base z κs) τ‖ ≤
      ampBound hSb L base amp z * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j) := by
  have hmp : MeasurePreserving (Φ.timeSplit hd) volume volume := by
    rw [Measure.volume_eq_prod]; exact Φ.measurePreserving_timeSplit hd
  have e : ∫ τ, ‖modeG
      (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer amp frq)
      D hS L γ δ base tt layer (Φ.glueDec hS hd hL base z κs) τ‖ =
      ∫ p, ‖Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs p‖ := by
    rw [← hmp.integral_comp' (fun p => ‖Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs p‖)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [modeG_eq_psi Φ hd hS hSb hL γ δ base D layer hLayer h tt amp frq z κs τ]
  rw [e, Measure.volume_eq_prod]
  have hQ := SpliceShape.measurableSet_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hv := SpliceShape.volume_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hgi : Integrable ((SpliceShape.boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
      (fun _ => ampBound hSb L base amp z * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j)))
      ((volume : Measure (GBranch Gsb.tree → ℝ)).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    (integrable_indicator_iff hQ).2 (integrableOn_const (by rw [hv]; exact ENNReal.one_ne_top))
  refine (integral_mono (Φ.integrable_psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs).norm hgi
    fun p => Φ.norm_psiInt_le hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs p).trans_eq ?_
  rw [integral_indicator_const _ hQ, Measure.real, hv]
  simp

end WaveTurbulence.Represents
