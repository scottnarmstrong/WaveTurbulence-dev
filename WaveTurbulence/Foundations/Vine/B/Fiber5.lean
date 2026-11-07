/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fiber4
import Mathlib.Tactic

/-!
# VINE-B♯: the sum over the local decorations of the units

`fiber_sum`: `Σ'_κ ∫ psiInt = ∫_{τ'} ε̃ 1_{openSb} sbInt Π_j (recJ_j · Σ'_{κ_j} unitI_j)`: the pointwise bound
`norm_fibInt_le`, the interchange of `Σ'` and `∫_{τ'}` (`integral_tsum_of_summable_integral_norm`), and the product
over the units (`tsum_pi_prod_complex`).
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

theorem norm_unitI_le (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖Φ.unitI D hS hSb L γ δ h layer hLayer base frq z τ' j κ‖ ≤
      unitLb (blk := blk) D hS L γ δ h layer hLayer base j κ :=
  norm_integral_gUnit_le (γ := γ) (hLayer := hLayer) (regionOf (blk j)) (hF j) _ _ _ κ

theorem norm_recJ (L γ δ : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration Gsb d roots 0)
    (τ' : GBranch Gsb.tree → ℝ) (j : J) : ‖Φ.recJ L γ δ base z τ' j‖ = 1 := norm_recExp _ _ _ _ _ _

theorem norm_fibInt_le (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) (τ' : GBranch Gsb.tree → ℝ) :
    ‖Φ.fibInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs τ'‖ ≤
      (boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
        (fun _ => ampBound hSb L base amp z * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j)) τ' := by
  unfold fibInt
  by_cases hp : τ' ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (openSb_subset_box _ _ hp)]
    have h1 : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_splicedEpsilon_le _ _ _
    have h2 : ‖Φ.sbInt hS hSb L γ δ base tt amp frq z τ'‖ ≤ ampBound hSb L base amp z := by
      unfold sbInt ampBound
      rw [norm_mul, norm_mul, norm_phaseProd_le, norm_routedPhase, norm_prod]
      simp
    have h3 : ∏ j, ‖Φ.recJ L γ δ base z τ' j * Φ.unitI D hS hSb L γ δ h layer hLayer base frq z τ' j (κs j)‖ ≤
        ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j) := by
      refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
      rw [norm_mul, Φ.norm_recJ, one_mul]
      exact Φ.norm_unitI_le D hS hSb L γ δ h layer hLayer base frq hF z τ' j (κs j)
    rw [norm_mul, norm_mul, norm_prod]
    calc _ ≤ 1 * (ampBound hSb L base amp z * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j)) :=
          mul_le_mul h1 (mul_le_mul h2 h3 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
            (ampBound_nonneg _ _ _ _ _)) (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
            zero_le_one
      _ = _ := one_mul _
  · rw [Set.indicator_of_notMem hp]
    simp only [mul_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => mul_nonneg (ampBound_nonneg _ _ _ _ _)
      (Finset.prod_nonneg fun j _ => unitLb_nonneg _ _ _ _ _ _ _ _ _ _ _)) _

theorem integrable_fibInt (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Integrable (Φ.fibInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs) := by
  have := (Φ.integrable_psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs).integral_prod_left
  have hfun : (fun τ' => ∫ τs : (∀ j, CLInternalTime (regionOf (blk j))),
      Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs (τ', τs)) =
      Φ.fibInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs :=
    funext fun τ' => Φ.inner_psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs τ'
  rwa [hfun] at this

end SpliceShape

end WaveTurbulence.VineB
