/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fiber2
import Mathlib.Tactic

/-!
# VINE-B♯: the glued term of the skeleton sum

`term_glue`: the summand of `skelVal` at a glued decoration is the integral of `psiInt` over `(τ', (τ_j))`
(change of variables by the measure preserving time split `timeSplit`), with the selection weight `Zw z`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem integrable_psiInt (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Integrable (Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs)
      ((volume : Measure (GBranch Gsb.tree → ℝ)).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
  have hQ := measurableSet_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hv := volume_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hg : Integrable ((boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
      (fun _ => ampBound hSb L base amp z * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j)))
      ((volume : Measure (GBranch Gsb.tree → ℝ)).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    (integrable_indicator_iff hQ).2 (integrableOn_const (by rw [hv]; exact ENNReal.one_ne_top))
  exact hg.mono' (Φ.measurable_psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => Φ.norm_psiInt_le hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs p)

theorem resDec_glueDec (hS : S.IsPlain) (hd : Disj blk) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Φ.resDec hS hd (Φ.glueDec hS hd hL base z κs) = z := by
  apply Subtype.ext
  funext y
  show (Φ.glueDec hS hd hL base z κs).1 (Φ.node y) = z.1 y
  rw [Φ.glueDec_val, Φ.glue_ret _ _ (Φ.ret_node y), Φ.ext_node]

/-- **The glued term.** -/
theorem term_glue (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) [DecidablePred selSk] (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    (if selSk (Φ.glueDec hS hd hL base z κs) then
      (epsDec S (Φ.glueDec hS hd hL base z κs).1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
        (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
          (fun τ => phaseProd L γ δ S (cosetDecoration S L base (Φ.glueDec hS hd hL base z κs).1) τ *
            ∏ s, Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer
              amp frq s (slotTs hS tt τ s)
              (base + latticePoint L ((Φ.glueDec hS hd hL base z κs).1 (slotNode hS s)))) τ else 0) =
    (Zw z : ℂ) * ∫ p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))),
      Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs p := by
  have hZz := hZ (Φ.glueDec hS hd hL base z κs)
  rw [Φ.resDec_glueDec hS hd hL base z κs] at hZz
  by_cases hs : selSk (Φ.glueDec hS hd hL base z κs)
  · rw [if_pos hs] at hZz ⊢
    rw [← hZz]
    simp only [Complex.ofReal_one, one_mul]
    rw [← integral_const_mul]
    have hmp := (Φ.measurePreserving_timeSplit hd).symm (Φ.timeSplit hd)
    rw [← hmp.integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [Φ.timeSplit_symm hd]
    exact Φ.integrand_glue hd hS hSb hL γ δ base D layer hLayer h tt amp frq z κs p.1 p.2
  · rw [if_neg hs] at hZz ⊢
    rw [← hZz]
    simp

end SpliceShape

end WaveTurbulence.VineB
