/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH16
public import WaveTurbulence.Foundations.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.Stage1.Represents.RepMom2
public import WaveTurbulence.Foundations.Stage1.Represents.RepOuterM
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D: the sum over the outer slot modes

`repIntC_modes`: a countable weighted sum `Σ_ξ W_ξ val_ξ` of per-mode `RepIntC` representations (`repIntC_mode`) is a
`RepIntC` representation of mass `Bt` as soon as the weighted masses `Σ_ξ ‖W_ξ‖ B_ξ` are `≤ Bt` (computed in `ℝ≥0∞`, where
`tsum_modes_moment` pays the modulation losses).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence WaveTurbulence.LGSpine
open scoped ENNReal

variable {P : WTParams} {R : ℕ} {π : Stage1Piece P R} {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
  {roots : Fin (2 * R) → (Fin P.d → ℤ)}

theorem repIntC_modes (hS : π.Gsb.IsPlain) (hL : 0 < P.L) {ι : Type} [Countable ι] (W : ι → ℂ) (val : ι → ℂ)
    (B : ι → ℝ) (hB0 : ∀ ξ, 0 ≤ B ξ) (h : ∀ ξ, RepIntC π tt base roots (val ξ) (B ξ)) (Bt : ℝ) (hBt : 0 ≤ Bt)
    (hsum : ∑' ξ, ENNReal.ofReal (‖W ξ‖ * B ξ) ≤ ENNReal.ofReal Bt) :
    RepIntC π tt base roots (∑' ξ, W ξ * val ξ) Bt := by
  have hne : ∑' ξ, ENNReal.ofReal (‖W ξ‖ * B ξ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  have hs : Summable fun ξ => ‖W ξ‖ * B ξ :=
    (ENNReal.summable_toReal hne).congr fun ξ => ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (hB0 ξ))
  obtain ⟨-, hr⟩ := RepIntC.tsum hS hL (fun ξ => W ξ * val ξ) (fun ξ => ‖W ξ‖ * B ξ) hs
    (fun ξ => (h ξ).smul (W ξ))
  refine hr.mono ?_
  have h1 : ENNReal.ofReal (∑' ξ, ‖W ξ‖ * B ξ) = ∑' ξ, ENNReal.ofReal (‖W ξ‖ * B ξ) :=
    ENNReal.ofReal_tsum_of_nonneg (fun ξ => mul_nonneg (norm_nonneg _) (hB0 ξ)) hs
  exact (ENNReal.ofReal_le_ofReal_iff hBt).1 (h1 ▸ hsum)

open WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS TTree Reg Reg.Skeleton in
/-- The weighted masses of the modes: weight `Π_s w_s(ξ_s)`, mass `Kc Π_j (1 + |λ_j(ξ)|)^c`. -/
theorem modes_mass_le {w : ℕ} {G : Garden w} {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) {Λ : ReplacementSlot G → Type}
    (W : ∀ s, Λ s → ℝ) (hW : ∀ s l, 0 ≤ W s l) (m : ∀ s, Λ s → Fin 2 → ℤ) {c θ : ℝ} (hc : 0 ≤ c)
    (hc1 : c ≤ 1) (hcθ : 2 * c ≤ θ) (μ : ReplacementSlot G → ℝ≥0∞)
    (hμ : ∀ s, ∑' l, maxBracketPow θ (half (m s l)) * ENNReal.ofReal (W s l) ≤ μ s) (Kc : ℝ) (hKc : 0 ≤ Kc) :
    ∑' ξ : ∀ s, Λ s, ENNReal.ofReal (‖(((∏ s, W s (ξ s) : ℝ)) : ℂ)‖ *
      (Kc * ∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)) ≤
      ENNReal.ofReal Kc * ∏ s, (9 * μ s) := by
  have h := tsum_modes_moment route W hW m hc hc1 hcθ μ hμ
  calc _ = ∑' ξ : ∀ s, Λ s, ENNReal.ofReal Kc * ENNReal.ofReal ((∏ s, W s (ξ s)) *
        ∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) := by
        refine tsum_congr fun ξ => ?_
        have hp : 0 ≤ ∏ s, W s (ξ s) := Finset.prod_nonneg fun s _ => hW s _
        rw [← ENNReal.ofReal_mul hKc, Complex.norm_real, Real.norm_of_nonneg hp]
        congr 1; ring
    _ = ENNReal.ofReal Kc * ∑' ξ : ∀ s, Λ s, ENNReal.ofReal ((∏ s, W s (ξ s)) *
        ∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) := ENNReal.tsum_mul_left
    _ ≤ _ := by gcongr

end WaveTurbulence.Represents
