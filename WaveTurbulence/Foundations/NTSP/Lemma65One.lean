/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.FullSum

/-!
# DH23 Lemma 6.5 (1)

`∫_ℝ |∫∫ χ₀((x-a)/λ) χ₀((y-b)/λ) Φ(s,x,y) e(ξ·x + ζ·y + s⟨x,y⟩) dx dy| ds ≲ D λ^{2d}` uniformly
in `(ξ, ζ, a, b)` (DH23 L1019–L1022): the stationary-phase bound `D λ^{2d} ⟨s⟩^{-d}` is integrable
for `d ≥ 2`. The `s`-integral is the Lebesgue integral of the modulus (`∫⁻`), so no measurability
in `s` is required of `Φ`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-- `∫_ℝ ⟨s⟩^{-d} ds`, `⟨s⟩ = 1 + |s|`. -/
@[expose] def sInt (d : ℕ) : ℝ := ∫ s : ℝ, ((1 + |s|) ^ d)⁻¹

theorem integrable_inv_one_add_abs_pow (hd : 2 ≤ d) :
    Integrable (fun s : ℝ => ((1 + |s|) ^ d)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := d)
    (by rw [Module.finrank_self]; exact_mod_cast (by omega : 1 < d))
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem sInt_nonneg (d : ℕ) : 0 ≤ sInt d := integral_nonneg fun _ => by positivity

theorem lintegral_le_of_le_inv_pow (hd : 2 ≤ d) {f : ℝ → ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ s, f s ≤ ENNReal.ofReal (C * ((1 + |s|) ^ d)⁻¹)) :
    ∫⁻ s, f s ≤ ENNReal.ofReal (C * sInt d) := by
  calc ∫⁻ s, f s ≤ ∫⁻ s, ENNReal.ofReal (C * ((1 + |s|) ^ d)⁻¹) := lintegral_mono hf
    _ = ENNReal.ofReal (∫ s, C * ((1 + |s|) ^ d)⁻¹) :=
        (ofReal_integral_eq_lintegral_ofReal ((integrable_inv_one_add_abs_pow hd).const_mul C)
          (Filter.Eventually.of_forall fun s => by positivity)).symm
    _ = ENNReal.ofReal (C * sInt d) := by rw [integral_const_mul, sInt]

/-- **DH23 Lemma 6.5 (1)** (`NTSP`, L1019–L1022). For `d ≥ 2`, `λ ≥ 1` and `Φ(s, ·, ·)`
satisfying the derivative bounds (NTphibounds) through order `10d` with constant `D` (for every
`s`), uniformly in `(ξ, ζ, a, b)`:
`∫_ℝ |∫∫ χ₀((x-a)/λ) χ₀((y-b)/λ) Φ(s,x,y) e(ξ·x + ζ·y + s⟨x,y⟩) dx dy| ds ≤ C D λ^{2d}`. -/
theorem ntsp_one (d : ℕ) (hd : 2 ≤ d) : ∃ C : ℝ, ∀ (D lam : ℝ) (Φ : ℝ → Mom d → Mom d → ℂ),
    1 ≤ lam → (∀ s, NTBounds (10 * d) D (Φ s)) → ∀ a b ξ ζ : Mom d,
      ∫⁻ s, ‖ntIntegral lam (Φ s) a b ξ ζ s‖ₑ ≤ ENNReal.ofReal (C * D * lam ^ (2 * d)) := by
  refine ⟨termConst d (10 * d) * sInt d, fun D lam Φ hlam hΦ a b ξ ζ => ?_⟩
  have hD : 0 ≤ D := (hΦ 0).nonneg
  have hC : 0 ≤ termConst d (10 * d) * D * lam ^ (2 * d) := by
    have := termConst_nonneg d (10 * d)
    have : 0 ≤ lam := by linarith
    positivity
  refine (lintegral_le_of_le_inv_pow hd hC fun s => ?_).trans (le_of_eq ?_)
  · rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_ntIntegral_le_stat (by omega) (hΦ s) hlam a b ξ ζ s)
  · congr 1
    ring

end WaveTurbulence.NTSP
