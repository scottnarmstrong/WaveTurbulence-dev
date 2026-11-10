/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedExpand2
public import WaveTurbulence.Foundations.VineEst.VineEstS3.DecayX
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSNorm

/-! # Mode families of clocked weights: the majorant data (engine step EXP)

`ClockedModes` packages Fourier-series coefficients `c ρ m` of the clocked weights with their
`S^{30d, N_ρ}` bounds `∑_m ⟨m/2⟩^θ ‖c ρ m‖_S ≤ b ρ < ⊤`; from it the pointwise majorant
`‖c ρ m k‖ ≤ S ρ m · Dec ρ k` with summable `S ρ` is derived.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.NormBridgeScratch
  Finset MeasureTheory
open scoped ENNReal

variable {d : ℕ} (D : SumintDatum d)

/-- The spatial weight order of a row: `30d` for `𝒦`-rows, `0` for `ℒ`-rows. -/
def rowOrder : Row D → ℕ := Sum.elim (fun _ => 30 * d) (fun _ => 0)

/-- Fourier-series coefficients of the clocked weights with their spatial-norm bounds. -/
structure ClockedModes (θ : ℝ) where
  c : Row D → (Fin 2 → ℤ) → Mom d → ℂ
  b : Row D → ℝ≥0∞
  b_ne_top : ∀ ρ, b ρ ≠ ⊤
  fs_bound : ∀ ρ, ∑' m : Fin 2 → ℤ, maxBracketPow θ (half m) * SNorm (30 * d) (rowOrder D ρ) (c ρ m) ≤ b ρ

variable {D}

theorem le_SNorm (Λ₁ Λ₂ : ℕ) (f : Mom d → ℂ) (k : Mom d) :
    ENNReal.ofReal (jbr k ^ Λ₂ * ‖f k‖) ≤ SNorm Λ₁ Λ₂ f := by
  classical
  unfold SNorm
  split_ifs
  · refine le_iSup_of_le (0 : Fin d → ℕ) (le_iSup_of_le (by simp) (le_iSup_of_le k ?_))
    rw [iterPartial_zero]
  · exact le_top

namespace ClockedModes
variable {θ : ℝ} (M : ClockedModes D θ)

theorem snorm_ne_top (hθ : 0 ≤ θ) (ρ : Row D) (m : Fin 2 → ℤ) : SNorm (30 * d) (rowOrder D ρ) (M.c ρ m) ≠ ⊤ := by
  have h1 : maxBracketPow θ (half m) * SNorm (30 * d) (rowOrder D ρ) (M.c ρ m) ≤ M.b ρ :=
    (ENNReal.le_tsum m).trans (M.fs_bound ρ)
  have h2 : SNorm (30 * d) (rowOrder D ρ) (M.c ρ m) ≤ maxBracketPow θ (half m) *
      SNorm (30 * d) (rowOrder D ρ) (M.c ρ m) :=
    le_mul_of_one_le_left bot_le (FS.one_le_maxBracketPow hθ _)
  exact ne_top_of_le_ne_top (M.b_ne_top ρ) (h2.trans h1)

/-- The size of a mode coefficient. -/
noncomputable def S (ρ : Row D) (m : Fin 2 → ℤ) : ℝ := (SNorm (30 * d) (rowOrder D ρ) (M.c ρ m)).toReal

theorem S_nonneg (ρ : Row D) (m : Fin 2 → ℤ) : 0 ≤ M.S ρ m := ENNReal.toReal_nonneg

theorem summable_S (hθ : 0 ≤ θ) (ρ : Row D) : Summable (M.S ρ) := by
  refine ENNReal.summable_toReal ?_
  refine ne_top_of_le_ne_top (M.b_ne_top ρ) ?_
  refine le_trans (ENNReal.tsum_le_tsum fun m => ?_) (M.fs_bound ρ)
  exact le_mul_of_one_le_left bot_le (FS.one_le_maxBracketPow hθ _)

theorem norm_le (hθ : 0 ≤ θ) (ρ : Row D) (m : Fin 2 → ℤ) (k : Mom d) :
    ‖M.c ρ m k‖ ≤ M.S ρ m * decayWt D (30 * d) ρ k := by
  have h1 := le_SNorm (30 * d) (rowOrder D ρ) (M.c ρ m) k
  have hS : ENNReal.ofReal (M.S ρ m) = SNorm (30 * d) (rowOrder D ρ) (M.c ρ m) :=
    ENNReal.ofReal_toReal (M.snorm_ne_top hθ ρ m)
  rw [← hS] at h1
  have h2 : jbr k ^ rowOrder D ρ * ‖M.c ρ m k‖ ≤ M.S ρ m :=
    (ENNReal.ofReal_le_ofReal_iff (M.S_nonneg ρ m)).1 h1
  have hj : 0 < jbr k ^ rowOrder D ρ := pow_pos (Real.sqrt_pos.2 (by positivity)) _
  cases ρ with
  | inl v =>
    simp only [decayWt, Sum.elim_inl, rowOrder] at h2 ⊢
    rw [← div_eq_mul_inv]
    have hj' : 0 < jbr k ^ (30 * d) := hj
    rw [le_div_iff₀ hj']
    linarith
  | inr v =>
    simp only [decayWt, Sum.elim_inr, rowOrder, pow_zero, one_mul, mul_one] at h2 ⊢
    exact h2

end ClockedModes

end WaveTurbulence.VineEstS3.Eng
