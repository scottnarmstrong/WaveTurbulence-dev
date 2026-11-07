/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.TimeFS
public import WaveTurbulence.Foundations.Sumint.TimeBridge

/-! # W6, vector-variable version (`𝔛^{θ,0,0}`, no momentum derivatives): the vine kernel `K̃^U`

For `F : (Fin r → ℝ) → V → ℂ` with `V` an arbitrary type of vector variables (for `K̃^U`: `r = 3` times
`(t_{u1}, t_{u21}, t_{u22})` and `V = (Mom d)^4`, the momenta `(k_{u1}, k_{u11}, k_{u21}, k_{u22})`), the
`XNorm00Restr` bound gives a superposition `∑_m w_m a_m(v) e^{πi m·t}` with sup-bounded amplitudes
`|a_m(v)| ≤ 1` (TARGET L1961: `K̃^{U_j}` "with each vector variable restricted to a unit ball").
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.Fourier MeasureTheory
open scoped ENNReal

variable {r : ℕ} {V : Type*}

/-- The Fourier-series coefficient of an extension `G`, for vector variable `v`. -/
noncomputable def coeff00 (q : Fin r → ℝ) (G : (Fin r → ℝ) → V → ℂ) (m : Fin r → ℤ) (v : V) : ℂ :=
  ∫ lam, kern q m lam * timeFT G lam v

theorem hasSum_coeff00 {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin r → ℝ) {B : Set (Fin r → ℝ)} (hB : B ⊆ cell q)
    {G f : (Fin r → ℝ) → V → ℂ} {v : V} (hGf : ∀ t ∈ B, G t v = f t v)
    (hfc : Continuous fun t => f t v) (hG : XNorm00 θ G < ⊤) {t : Fin r → ℝ}
    (ht : t ∈ closure (interior B)) :
    HasSum (fun m : Fin r → ℤ => coeff00 q G m v * fsPhase m t) (f t v) := by
  have hgn : timeFourierNorm θ (fun s => G s v) < ⊤ := by
    refine lt_of_le_of_lt ((timeFourierNorm_slice_le_mixedFourierNorm00 θ G v).trans_eq ?_) hG
    exact (NormBridgeScratch.XNorm00_eq_mixedFourierNorm00 θ G).symm
  have := hasSum_coeff_slice hθ q hB hgn hGf hfc ht
  simpa only [coeff00, NormBridgeScratch.timeFT_eq_timeFourier] using this

end WaveTurbulence.RepAnalytic
