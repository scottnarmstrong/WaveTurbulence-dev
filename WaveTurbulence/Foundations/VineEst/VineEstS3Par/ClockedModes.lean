/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockedExpand2
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.DecayX
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSNorm

/-! # Mode families of clocked weights: the majorant data (engine step EXP)

`ClockedModes` packages Fourier-series coefficients `c ρ m` of the clocked weights with their
`S^{30d, N_ρ}` bounds `∑_m ⟨m/2⟩^θ ‖c ρ m‖_S ≤ b ρ < ⊤`; from it the pointwise majorant
`‖c ρ m k‖ ≤ S ρ m · Dec ρ k` with summable `S ρ` is derived.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.NormBridgeScratch
  Finset MeasureTheory
open scoped ENNReal

variable {d : ℕ} (D : SumintPar.SumintDatum d)

/-- The spatial weight order of a row: the decay `wDec` for `𝒦`-rows, `0` for `ℒ`-rows. -/
def rowOrder : Row D → ℕ := Sum.elim (fun _ => D.wDec) (fun _ => 0)

/-- Fourier-series coefficients of the clocked weights (functions of `r` and of the momentum) with their spatial-norm
bounds, the supremum over `r` being taken INSIDE the mode sum (the `sumint` bound is uniform in `r` for a fixed
mode family).  The `ℒ` rows do not depend on `r`. -/
structure ClockedModes (θ : ℝ) where
  c : Row D → (Fin 2 → ℤ) → Mom d → Mom d → ℂ
  c_indep : ∀ (v : D.S.VIdx) (m : Fin 2 → ℤ) (r r' k : Mom d), c (Sum.inr v) m r k = c (Sum.inr v) m r' k
  b : Row D → ℝ≥0∞
  b_ne_top : ∀ ρ, b ρ ≠ ⊤
  fs_bound : ∀ ρ, ∑' m : Fin 2 → ℤ, maxBracketPow θ (half m) *
    (⨆ r : Mom d, SNorm D.wN (rowOrder D ρ) (c ρ m r)) ≤ b ρ

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

theorem one_le_mbp (hθ : 0 ≤ θ) {r : ℕ} (lam : Fin r → ℝ) : 1 ≤ maxBracketPow θ lam :=
  WaveTurbulence.VineEstS3.FS.one_le_maxBracketPow hθ lam

/-- The `r`-uniform spatial norm of a mode coefficient. -/
noncomputable def sn (ρ : Row D) (m : Fin 2 → ℤ) : ℝ≥0∞ := ⨆ r : Mom d, SNorm D.wN (rowOrder D ρ) (M.c ρ m r)

theorem sn_ne_top (hθ : 0 ≤ θ) (ρ : Row D) (m : Fin 2 → ℤ) : M.sn ρ m ≠ ⊤ := by
  have h1 : maxBracketPow θ (half m) * M.sn ρ m ≤ M.b ρ := (ENNReal.le_tsum m).trans (M.fs_bound ρ)
  have h2 : M.sn ρ m ≤ maxBracketPow θ (half m) * M.sn ρ m :=
    le_mul_of_one_le_left bot_le (WaveTurbulence.VineEstS3.FS.one_le_maxBracketPow hθ _)
  exact ne_top_of_le_ne_top (M.b_ne_top ρ) (h2.trans h1)

/-- The size of a mode coefficient. -/
noncomputable def S (ρ : Row D) (m : Fin 2 → ℤ) : ℝ := (M.sn ρ m).toReal

theorem S_nonneg (ρ : Row D) (m : Fin 2 → ℤ) : 0 ≤ M.S ρ m := ENNReal.toReal_nonneg

theorem summable_S (hθ : 0 ≤ θ) (ρ : Row D) : Summable (M.S ρ) := by
  refine ENNReal.summable_toReal ?_
  refine ne_top_of_le_ne_top (M.b_ne_top ρ) ?_
  refine le_trans (ENNReal.tsum_le_tsum fun m => ?_) (M.fs_bound ρ)
  exact le_mul_of_one_le_left bot_le (WaveTurbulence.VineEstS3.FS.one_le_maxBracketPow hθ _)

theorem norm_le (hθ : 0 ≤ θ) (ρ : Row D) (m : Fin 2 → ℤ) (r k : Mom d) :
    ‖M.c ρ m r k‖ ≤ M.S ρ m * decayWt D D.wDec ρ k := by
  have h1 := le_SNorm D.wN (rowOrder D ρ) (M.c ρ m r) k
  have hS : ENNReal.ofReal (M.S ρ m) = M.sn ρ m := ENNReal.ofReal_toReal (M.sn_ne_top hθ ρ m)
  have h1' : ENNReal.ofReal (jbr k ^ rowOrder D ρ * ‖M.c ρ m r k‖) ≤ ENNReal.ofReal (M.S ρ m) := by
    rw [hS]
    exact h1.trans (le_iSup (fun r' => SNorm D.wN (rowOrder D ρ) (M.c ρ m r')) r)
  have h2 : jbr k ^ rowOrder D ρ * ‖M.c ρ m r k‖ ≤ M.S ρ m :=
    (ENNReal.ofReal_le_ofReal_iff (M.S_nonneg ρ m)).1 h1'
  have hj : 0 < jbr k ^ rowOrder D ρ := pow_pos (Real.sqrt_pos.2 (by positivity)) _
  cases ρ with
  | inl v =>
    simp only [decayWt, Sum.elim_inl, rowOrder] at h2 ⊢
    rw [← div_eq_mul_inv]
    have hj' : 0 < jbr k ^ D.wDec := hj
    rw [le_div_iff₀ hj']
    linarith
  | inr v =>
    simp only [decayWt, Sum.elim_inr, rowOrder, pow_zero, one_mul, mul_one] at h2 ⊢
    exact h2

end ClockedModes

end WaveTurbulence.VineEstS3Par.Eng
