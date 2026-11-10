/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Layered.ParamFinite
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# Momentum regularity of inverse time-Fourier integrals

For a frequency function `Ĝ(λ, k)` (`λ ∈ ℝ^r`, `k ∈ ℝ^d`) that is `C^N` in `k` for every `λ`, strongly
measurable in `λ`, and whose weighted iterated `k`-derivatives are dominated by integrable functions
`S_j(λ)` of the frequency, `w(k) ‖D^j_k Ĝ(λ, k)‖ ≤ S_j(λ)` with a weight `w ≥ 1`, the inverse
time-Fourier integral

`g(t, k) = ∫ Ĝ(λ, k) e^{2πi⟨λ, t⟩} dλ`

is `C^N` in `k` (`contDiff_invTimeFourier`), and its weighted iterated derivatives are bounded by the
integrals of the dominating functions (`weight_mul_norm_iteratedFDeriv_invTimeFourier_le`). This is the
momentum part of the point trace of TARGET's weighted Fourier norms `𝔛^{θ,Λ₁,Λ₂}` (TARGET (normX),
L581): the supremum over `k` sits inside the frequency integral.
-/

public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace WaveTurbulence.Layered

variable {r d : ℕ}

theorem iteratedFDeriv_const_mul_param {N : ℕ} {h : Mom d → ℂ} (hh : ContDiff ℝ N h) (c : ℂ)
    {j : ℕ} (hj : j ≤ N) (k : Mom d) :
    iteratedFDeriv ℝ j (fun k => h k * c) k = c • iteratedFDeriv ℝ j h k := by
  have : (fun k => h k * c) = fun k => c • h k := by funext k; rw [smul_eq_mul, mul_comm]
  rw [this]
  exact iteratedFDeriv_const_smul_apply' (hh.contDiffAt.of_le (by exact_mod_cast hj))

variable {N : ℕ} {Ghat : (Fin r → ℝ) → Mom d → ℂ}

end WaveTurbulence.Layered
