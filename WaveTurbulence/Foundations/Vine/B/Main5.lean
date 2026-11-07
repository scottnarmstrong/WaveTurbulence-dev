/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Main5b
import Mathlib.Tactic

/-!
# VINE-B♯: the per-mode identity for a general `SpliceShape` (the theorem)
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

theorem const_split (Φ : SpliceShape blk Gsb) (hd : Disj blk) (L γ δ : ℝ) :
    (coupling d L γ δ : ℂ) ^ S.order * S.zeta = ((coupling d L γ δ : ℂ) ^ Gsb.order * Gsb.zeta) *
      ∏ j, unitConst (d := d) blk L γ δ j := by
  rw [Φ.order_split hd, Φ.zeta_split hd, pow_add]
  unfold unitConst
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

open scoped Classical in
/-- **The per-mode single-state factorization** (VINE-B♯, general splice shape). -/
theorem skelVal_modal_eq_outerValM (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0)
    (γ δ : ℝ) (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z) :
    skelVal D hS L γ δ base roots tt layer selSk
      (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer amp frq) =
    outerValM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) (Φ.hinges hd) Zw hSb
      amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelM blk D hS L γ δ h layer hLayer base) := by
  have hs := Φ.tsum_skelTerm hd hS hSb hL γ δ base D layer hLayer h tt amp frq selSk Zw hZ hF hsum
  have hC := const_split (d := d) Φ hd L γ δ
  rw [skelVal_eq, hs, hC]
  unfold outerValM
  simp_rw [Φ.outer_term_eq hd D hS hSb L γ δ base h layer hLayer tt amp frq Zw]
  rw [tsum_mul_left]
  ring

end SpliceShape

end WaveTurbulence.VineB
