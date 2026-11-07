/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Main3
import Mathlib.Tactic

/-!
# VINE-B♯: the per-mode identity for a general `SpliceShape` (the sum over decorations)
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

open scoped Classical in
theorem skelTerm_glue (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    skelTerm D hS L γ δ base roots tt layer selSk
      (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer amp frq)
      (Φ.glueDec hS hd hL base z κs) =
    (Zw z : ℂ) * ∫ p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))),
      Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs p :=
  Φ.term_glue hd hS hSb hL γ δ base D layer hLayer h tt amp frq selSk Zw hZ z κs

open scoped Classical in
theorem norm_skelTerm_glue_le (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0)
    (γ δ : ℝ) (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖skelTerm D hS L γ δ base roots tt layer selSk
      (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer amp frq)
      (Φ.glueDec hS hd hL base z κs)‖ ≤
      ampBound hSb L base amp z * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j) := by
  rw [Φ.skelTerm_glue hd hS hSb hL γ δ base D layer hLayer h tt amp frq selSk Zw hZ z κs, norm_mul]
  have hZz := hZ (Φ.glueDec hS hd hL base z κs)
  rw [Φ.resDec_glueDec hS hd hL base z κs] at hZz
  have h1 : ‖(Zw z : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, ← hZz]
    split_ifs <;> simp
  calc _ ≤ 1 * _ := mul_le_mul h1 (Φ.norm_integral_psiInt_le hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs)
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end SpliceShape

end WaveTurbulence.VineB
