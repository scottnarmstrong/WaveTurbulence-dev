/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpatialInputBounds
/-! Real input regularity and uniform finite-order bounds from the literal source remainder premise. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

theorem contDiff_real_of_SNormR_bound {d A B : ℕ} (hA : A ≠ 0) (f : Mom d → ℝ)
    (C : ℝ) (h : SNormR A B f ≤ ENNReal.ofReal C) : ContDiff ℝ A f := by
  have hc := contDiff_of_SNorm_bound hA (fun x => (f x : ℂ)) C h
  have hr := Complex.reCLM.contDiff.comp hc
  change ContDiff ℝ A (fun x => (f x : ℂ).re) at hr
  simpa only [Complex.ofReal_re] using hr

theorem exists_inputsF_high_bounds (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (hδ : 0 ≤ P.δ) (htime : P.τstar = (P.D : ℝ) * P.δ)
    (hsol : IsWKESolution P.φin P.τstar P.φ)
    {p A B : ℕ} (hp : p < P.D) (hA0 : A ≠ 0)
    (hA : A ≤ P.Lambda p) (hB : B ≤ P.Lambda p)
    (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p) :
    ∃ C : NNReal, 1 ≤ C ∧ ∀ r ≤ p,
      ContDiff ℝ A (inputsF P R r) ∧ SNormR A B (inputsF P R r) ≤ ENNReal.ofReal (C : ℝ) := by
  obtain ⟨Cφ, hCφ, hbφ⟩ := exists_uniform_SNormR hsol.1 A B
  have hφ : ∀ r ≤ p, SNormR A B (P.φ (P.δ * r)) ≤ ENNReal.ofReal Cφ := by
    intro r hr
    apply hbφ
    refine ⟨mul_nonneg hδ (Nat.cast_nonneg r), ?_⟩
    rw [htime]
    have hrD : (r : ℝ) ≤ P.D := by exact_mod_cast hr.trans hp.le
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hrD hδ
  have hb := inputsF_SNormR_bound P hd hL hp hA hB R hR Cφ (by linarith) hφ
  let C : NNReal := ⟨Cφ + 1, by linarith⟩
  refine ⟨C, ?_, ?_⟩
  · change (1 : ℝ) ≤ Cφ + 1
    linarith
  · intro r hr
    exact ⟨contDiff_real_of_SNormR_bound hA0 _ _ (hb r hr), hb r hr⟩

end WaveTurbulence.LGSpine
