/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB5
public import WaveTurbulence.Foundations.Stage1.Represents.RepH4
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: `skelVal` as a mode series

`hasSum_skelVal_modes`: with the true slot kernels `slotFn`, the skeleton expression `skelVal` is the sum over the joint
modes `ξ` of the weighted modal skeleton expressions (to which VINE-B♯'s per-mode identity applies).  The interchange of
the mode sum with the decoration sum is dominated by `w_ξ · kBound_ξ`, with `Σ_z ampBound_ξ(z) ≤ ((⌊2L⌋₊+2)^d)^{#pairs}`
uniform in `ξ` (`tsum_ampBound_mode_le`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineB WaveTurbulence.VineEstS3.FS WaveTurbulence.RegRed WaveTurbulence.RedSplice
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS4 MeasureTheory

theorem lbConst_nonneg {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (R : CLRegionData G U a b) : 0 ≤ lbConst D hG L γ δ F layer hLayer base R := by
  unfold lbConst
  refine mul_nonneg (Finset.prod_nonneg fun p _ => tsum_nonneg fun x => ?_) (Finset.prod_nonneg fun v _ => ?_)
  · unfold pairBound majSum
    exact mul_nonneg (by positivity) (tsum_nonneg fun ρ => Finset.prod_nonneg fun ℓ _ => abs_nonneg _)
  · unfold chainBound
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun ℓ _ => tsum_nonneg fun n => abs_nonneg _)

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

theorem tsum_kBound_le (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d)
    (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (hsm : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z) (N : ℝ)
    (hN : ∑' z : GenDecoration Gsb d roots 0, ampBound hSb L base amp z ≤ N) :
    ∑' p, Φ.kBound hSb L γ δ base D hS layer hLayer h (roots := roots) amp p ≤
      N * ∏ j, lbConst D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j)) := by
  have hkbs := Φ.summable_kBound hS hSb hL γ δ base D layer hLayer h (roots := roots) amp hF hsm
  have hfib := fun z => Φ.summable_fib_kBound hS hSb hL γ δ base D layer hLayer h (roots := roots) amp hF z
  have hΛ0 : 0 ≤ ∏ j, lbConst D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j)) :=
    Finset.prod_nonneg fun j _ => lbConst_nonneg _ _ _ _ _ _ _ _ _ _
  rw [hkbs.tsum_sigma' hfib]
  calc _ ≤ ∑' z : GenDecoration Gsb d roots 0, ampBound hSb L base amp z *
          ∏ j, lbConst D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j)) :=
        Summable.tsum_le_tsum (fun z => Φ.tsum_fib_kBound_le hS hSb hL γ δ base D layer hLayer h amp hF z)
          hkbs.sigma (hsm.mul_right _)
    _ = (∑' z, ampBound hSb L base amp z) * ∏ j, lbConst D hS L γ δ (unitProfile blk h j) layer hLayer base
          (regionOf (blk j)) := tsum_mul_right
    _ ≤ N * _ := mul_le_mul_of_nonneg_right hN hΛ0

end WaveTurbulence.Represents
