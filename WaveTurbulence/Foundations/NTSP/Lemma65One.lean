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

end WaveTurbulence.NTSP
