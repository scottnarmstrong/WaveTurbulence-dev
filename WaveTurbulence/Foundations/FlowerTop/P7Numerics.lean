/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.LogAbsorption
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Export
public import WaveTurbulence.Foundations.Spine.NonregularPrefixTools

/-! Discharge P7's dimension, width and logarithmic loss side conditions. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open FlowerP7 LGSpine Filter

/-- The source prefix range gives gamma <= d. -/
theorem gamma_le_dim (P : WTParams) (hd : 1 ≤ P.d) (hγ : P.γ < 1) : P.γ ≤ P.d := by
  have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  linarith

/-- P7's width lower bound is supplied by the existing LG log threshold. -/
theorem p7_one_le_R (P : WTParams) (hd : 1 ≤ P.d) (hlog : 1 ≤ Real.log P.L) (p : ℕ) :
    1 ≤ P.R (p + 1) := one_le_R P hlog hd (p + 1)

/-- The exact hE loss is eventually absorbed, with Cr fixed before L. -/
theorem eventually_p7_loss (P : WTParams) (hd : 1 ≤ P.d) (p : ℕ) (Cr : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      (12 * 2 ^ 12 * (1 + Cr) ^ 3 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * Kd P.d ^ 6) *
        Real.log L ^ (12 * logExp P) ≤ L ^ ((100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1)) := by
  have he : (0 : ℝ) < (100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1) := by
    have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
    linarith
  exact (eventually_constant_log_pow_le _ (12 * logExp P) he).mono fun _ h => h.2

/-- One late threshold works for every stage, without changing earlier constant dependencies. -/
theorem eventually_p7_loss_all (P : WTParams) (hd : 1 ≤ P.d) (Cr : Fin P.D → ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ p : Fin P.D,
      (12 * 2 ^ 12 * (1 + Cr p) ^ 3 * 3 ^ (4 * (P.Lambda (p.1 + 1) : ℝ)) * Kd P.d ^ 6) *
        Real.log L ^ (12 * logExp P) ≤ L ^ ((100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1)) := by
  exact Filter.eventually_all.mpr fun p => eventually_p7_loss P hd p.1 (Cr p)

end WaveTurbulence.FlowerTop
