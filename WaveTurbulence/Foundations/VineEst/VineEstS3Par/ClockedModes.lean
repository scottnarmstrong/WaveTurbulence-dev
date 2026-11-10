/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockedExpand
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

end ClockedModes

end WaveTurbulence.VineEstS3Par.Eng
