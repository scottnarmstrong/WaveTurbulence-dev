/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SchwartzCosetSummability
public import WaveTurbulence.Foundations.Spine.SourceSeparation

/-! # Summability of the inputs `F_r = φ(δr) + R_r` on every shifted lattice (Step 3, continuity of the kernels) -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.LGSpine

theorem summable_inputsF_of_InputRemainder (P : WTParams) (R : ℕ → Mom P.d → ℝ) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    {r : ℕ} (hR : InputRemainder P (R r) r) (k : Mom P.d) :
    Summable (fun n : Fin P.d → ℤ => |inputsF P R r (k + latticePoint P.L n)|) := by
  have hφ := summable_abs_schwartz_coset hL (P.φ (P.δ * r)) k
  have hrem := summable_abs_coset_of_SNormR (A := 40 * P.d) (B := 40 * P.d) hL (by omega)
    (Real.rpow_nonneg (by linarith : 0 ≤ P.L) _) (R r) hR k
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => abs_add_le _ _) (hφ.add hrem)

end WaveTurbulence.VineEstS3
