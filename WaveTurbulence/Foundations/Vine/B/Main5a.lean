/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Main4
import Mathlib.Tactic

/-!
# VINE-B♯: the domination of the glued terms over `Σ z, Π_j Dec_j`
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

/-- The domination of the glued terms. -/
noncomputable def kBound (hSb : Gsb.IsPlain) (L γ δ : ℝ) (base : Mom d) (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (p : Σ z : GenDecoration Gsb d roots 0, ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) : ℝ :=
  ampBound hSb L base amp p.1 * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (p.2 j)

theorem kBound_nonneg (hSb : Gsb.IsPlain) (L γ δ : ℝ) (base : Mom d) (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (p : Σ z : GenDecoration Gsb d roots 0, ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    0 ≤ Φ.kBound hSb L γ δ base D hS layer hLayer h amp p :=
  mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => unitLb_nonneg _ _ _ _ _ _ _ _ _ _ _)

theorem summable_fib_kBound (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d)
    (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0) :
    Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      Φ.kBound hSb L γ δ base D hS layer hLayer h amp ⟨z, κs⟩ := by
  have hs := (summable_pi_prod_dep (fun j (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      unitLb (blk := blk) D hS L γ δ h layer hLayer base j κ)
      (fun j κ => unitLb_nonneg _ _ _ _ _ _ _ _ _ _ _)
      (fun j => (summable_tsum_localBound (γ := γ) (δ := δ) (hLayer := hLayer) (blk j).isBlock
        (regionOf (blk j)) (hF j) hL _).1)).1
  exact hs.mul_left (ampBound hSb L base amp z)

theorem tsum_fib_kBound_le (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d)
    (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0) :
    ∑' κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      Φ.kBound hSb L γ δ base D hS layer hLayer h amp ⟨z, κs⟩ ≤
      ampBound hSb L base amp z *
        ∏ j, lbConst D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j)) := by
  have hsm := fun j (β : Fin 4 → Mom d) => (summable_tsum_localBound (γ := γ) (δ := δ) (hLayer := hLayer)
    (blk j).isBlock (regionOf (blk j)) (hF j) hL β)
  have e : ∑' κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      Φ.kBound hSb L γ δ base D hS layer hLayer h amp ⟨z, κs⟩ =
      ampBound hSb L base amp z * ∑' κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
        ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j) := by
    rw [← tsum_mul_left]
    rfl
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (ampBound_nonneg _ _ _ _ _)
  have hs := summable_pi_prod_dep (fun j (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
    unitLb (blk := blk) D hS L γ δ h layer hLayer base j κ)
    (fun j κ => unitLb_nonneg _ _ _ _ _ _ _ _ _ _ _) (fun j => (hsm j _).1)
  refine hs.2.trans ?_
  exact Finset.prod_le_prod₀ (fun j _ => tsum_nonneg fun κ => unitLb_nonneg _ _ _ _ _ _ _ _ _ _ _)
    fun j _ => (hsm j _).2

theorem summable_kBound (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d)
    (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z) :
    Summable (Φ.kBound hSb L γ δ base D hS layer hLayer h (roots := roots) amp) := by
  rw [summable_sigma_of_nonneg (Φ.kBound_nonneg hSb L γ δ base D hS layer hLayer h amp)]
  refine ⟨Φ.summable_fib_kBound hS hSb hL γ δ base D layer hLayer h amp hF, ?_⟩
  exact Summable.of_nonneg_of_le (fun z => tsum_nonneg fun κs => Φ.kBound_nonneg hSb L γ δ base D hS layer hLayer h amp _)
    (fun z => Φ.tsum_fib_kBound_le hS hSb hL γ δ base D layer hLayer h amp hF z)
    (hsum.mul_right (∏ j, lbConst D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j))))

end SpliceShape

end WaveTurbulence.VineB
