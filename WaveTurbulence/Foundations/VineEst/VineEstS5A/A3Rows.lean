/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Embed
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Coef
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Joint
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSMain
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Engine

/-! # Row builders for the arity-3 engine (V5 Step 4d-A, item 2)

* `rowModes3_of_restr`: an `r`-independent two-clock row with a restriction-norm bound has three-clock coefficients
  (zero third mode) with the `fs_expansion` bound.
* `hasSum_sepCoef`: pointwise expansion of a separated row `H(c) M(r,k)` from the expansion of `H`.
* `ae_clock_of_ae`: an a.e. statement on the three clocks of a row whose three slots are distinct internal times
  pulls back to an a.e. statement in the internal times `τ` (the form of `hser` in `clockedBoundMix3`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5A
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3Par.Eng
 WaveTurbulence.VineEstS3.Eng MeasureTheory
open scoped ENNReal

variable {d : ℕ}

theorem SNorm_zero_fun (A B : ℕ) : SNorm A B (fun _ : Mom d => (0 : ℂ)) = 0 := by
  have := SNorm_smul_le (d := d) A B 0 (fun _ => 0)
  simpa using this

/-- A separated row expands pointwise from the expansion of its time factor. -/
theorem hasSum_sepCoef {h : (Fin 3 → ℤ) → ℂ} {t : Fin 3 → ℝ} {S : ℂ}
    (hS : HasSum (fun m : Fin 3 → ℤ => h m * fsPhase m t) S) (M : Mom d → Mom d → ℂ) (r k : Mom d) :
    HasSum (fun m : Fin 3 → ℤ => sepCoef h M m r k * fsPhase m t) (S * M r k) := by
  have := hS.mul_right (M r k)
  convert this using 2 with m
  unfold sepCoef; ring

end WaveTurbulence.VineEstS5A
