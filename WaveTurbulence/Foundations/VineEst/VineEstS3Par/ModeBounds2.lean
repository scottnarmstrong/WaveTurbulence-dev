/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ModeBounds

/-! # The per-mode weight (engine step ASM)

`2^{θ_a} ⟨ν_m/2⟩^{θ_a} (maxPar D_m)^{η⁶} ≤ C₀ C^{|Row|} (maxPar D)^{η⁶} ∏_ρ ⟨m_ρ/2⟩^{6η⁶}` for `θ_a = 2η⁸ ≤ 2η⁶`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS Finset
open scoped ENNReal

variable {d : ℕ} (D : SumintPar.SumintDatum d)


theorem rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (s : ℝ) : (x ^ n) ^ s = (x ^ s) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

end WaveTurbulence.VineEstS3Par.Eng
