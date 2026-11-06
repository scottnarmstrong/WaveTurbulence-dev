/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ParameterExponentBounds
public import WaveTurbulence.Foundations.Spine.UniformHighCostAbsorption
/-! Parameter thresholds for coherent spatial estimates, in the source dependency order. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set

 theorem exists_delta_sqrt_threshold {B : ℝ} (hB : 0 < B) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioc (0 : ℝ) δ₀, δ ≤ 1 ∧ B * δ ≤ Real.sqrt δ := by
  refine ⟨min 1 ((B⁻¹) ^ 2), by positivity, ?_⟩
  intro δ hδ
  exact ⟨hδ.2.trans (min_le_left _ _),
    scaled_delta_le_sqrt hB hδ.1.le (hδ.2.trans (min_le_right _ _))⟩

 theorem theta_step_lt (P : WTParams) (hη : 0 < P.η) (p : ℕ) : P.theta (p + 1) < P.theta p := by
  have hpow : 0 < ((2 : ℝ)⁻¹) ^ p := pow_pos (by norm_num) _
  have hη20 : 0 < P.η ^ 20 := pow_pos hη _
  have hmul : 0 < P.η ^ 20 * ((2 : ℝ)⁻¹) ^ p := mul_pos hη20 hpow
  unfold WTParams.theta
  rw [pow_succ ((2 : ℝ)⁻¹) p]
  nlinarith

 theorem eventually_fixed_cost_two_decays {H a c b : ℝ} (hH : 0 ≤ H) (hba : b < a) (hbc : b < c) :
    ∀ᶠ L : ℝ in atTop, H * (L ^ (-a) + L ^ (-c)) ≤ L ^ (-b) := by
  have ha := CountLemmas.eventually_monomial_log_le
    (a := -a) (b := -b) (C := 2 * H) (by linarith) (by positivity) 0
  have hc := CountLemmas.eventually_monomial_log_le
    (a := -c) (b := -b) (C := 2 * H) (by linarith) (by positivity) 0
  filter_upwards [ha, hc] with L h₁ h₂
  simp only [pow_zero, mul_one] at h₁ h₂
  linarith

/-- A single final large-L threshold pays the fixed high cost at every stage. -/
theorem eventually_uniform_coherent_decay (P : WTParams) (hη : 0 < P.η)
    {a H : ℝ} (ha : 2 * P.η ^ 20 < a) (hH : 0 ≤ H) :
    ∀ᶠ L : ℝ in atTop, ∀ p < P.D,
      H * (L ^ (-a) + L ^ (-P.theta p)) ≤
        L ^ (-((4 * P.theta (p + 1) + P.theta p) / 5)) := by
  have hp (p : Fin P.D) : ∀ᶠ L : ℝ in atTop,
      H * (L ^ (-a) + L ^ (-P.theta p.1)) ≤
        L ^ (-((4 * P.theta (p.1 + 1) + P.theta p.1) / 5)) := by
    apply eventually_fixed_cost_two_decays hH
    · have h₀ := theta_le_two_eta_pow P p.1
      have h₁ := theta_le_two_eta_pow P (p.1 + 1)
      linarith
    · have hstep := theta_step_lt P hη p.1
      linarith
  have hh := Filter.eventually_all.mpr hp
  filter_upwards [hh] with L hL
  intro p hp
  exact hL ⟨p, hp⟩

end WaveTurbulence.LGSpine
