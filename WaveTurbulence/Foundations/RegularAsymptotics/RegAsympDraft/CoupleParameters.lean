/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform small-eta and large-lattice parameter choices for the exact RA1 contract -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Filter Set

/-- A single eta range supplies all source estimates and the final rate
weakening, depending only on dimension and gamma. -/
theorem exists_couple_eta_range {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0:ℝ) 1) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc (0:ℝ) η₀,
      η ≤ 1/20 ∧ η ≤ ((d:ℝ)-1)*(1-γ) ∧ η ≤ γ ∧ 2*η ≤ Real.sqrt η := by
  have hd' : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hD : 0 < ((d:ℝ)-1)*(1-γ) := mul_pos (by linarith) (sub_pos.mpr hγ.2)
  refine ⟨min (1/20) (min (((d:ℝ)-1)*(1-γ)) γ),lt_min (by norm_num) (lt_min hD hγ.1),?_⟩
  intro η hη
  have hsmall : η ≤ 1/20 := hη.2.trans (min_le_left _ _)
  refine ⟨hsmall,hη.2.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hη.2.trans ((min_le_right _ _).trans (min_le_right _ _)),?_⟩
  have hs := Real.sq_sqrt hη.1.le
  have hsn := Real.sqrt_nonneg η
  nlinarith only [hη.1,hsmall,hs,hsn]

/-- For every fixed positive step size the physical NT lower-scale
condition holds eventually, without restricting the order exponent. -/
theorem exists_physical_delta_threshold {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → L^(-(η/2)) ≤ 2*δ := by
  have he : ∀ᶠ L : ℝ in atTop, L^(-(η/2)) < 2*δ :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < η/2)).eventually (eventually_lt_nhds (by positivity : (0:ℝ)<2*δ))
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp he
  exact ⟨L₀,fun L hL => (hL₀ L hL).le⟩

end WaveTurbulence.RegAsymp
