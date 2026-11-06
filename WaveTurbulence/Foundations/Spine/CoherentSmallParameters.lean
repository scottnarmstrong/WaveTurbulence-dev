/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentDeltaThreshold
public import WaveTurbulence.Foundations.Spine.PrefixConjunction
/-! Source-order choices of the small parameters, preserving any already combined input prefix. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

structure CoherentSmallParameters (P : WTParams) : Prop where
  eta_pos : 0 < P.η
  eta_le : P.η ≤ 1 / 2
  exponent_reserve : 2 * P.η ^ 20 < P.gamma1 - Real.sqrt P.η
  nu_le : P.ν ≤ 1 / 16
  delta_pos : 0 < P.δ
  delta_le : P.δ ≤ 1
  low_delta : 64 * ((12 ^ 9 : ℕ) : ℝ) * P.C₁ ^ 4 * P.δ ≤ Real.sqrt P.δ
  tail_delta : (P.C₁ + P.C₁ ^ 2) * (((((12 ^ 9) * 4 : ℕ) : ℝ) * 8 * P.C₁ ^ 2) *
    (2 * P.C₁ ^ 2 * P.δ)) ≤ Real.sqrt P.δ * Real.exp (-1)
  taylor_delta : P.C₁ * P.δ ≤ Real.sqrt P.δ * Real.exp (-1)
  large_L : 2 ≤ P.L

theorem prefix_with_coherent_small_parameters {Q : WTParams → Prop} (hQ : WTPrefix Q) :
    WTPrefix (fun P => Q P ∧ CoherentSmallParameters P) := by
  intro d hd γ hγ
  obtain ⟨ηQ, hηQ, hQ⟩ := hQ d hd γ hγ
  let a := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ)))
  have ha : 0 < a := by
    dsimp only [a]
    apply lt_min (by linarith [hγ.1])
    apply lt_min (by norm_num)
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact mul_pos (by linarith) (by linarith [hγ.2])
  obtain ⟨ηa, hηa, hea⟩ := exists_eta_exponent_reserve ha
  refine ⟨min ηQ (min (1 / 2) ηa), by positivity, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  have hηQ' : η ≤ ηQ := hη.2.trans (min_le_left _ _)
  have hηhalf : η ≤ 1 / 2 := hη.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηa' : η ≤ ηa := hη.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hreserve := hea η ⟨hη.1, hηa'⟩
  obtain ⟨C₁, hC₁, νQ, hνQ, hQ⟩ := hQ η ⟨hη.1, hηQ'⟩ φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, min νQ (1 / 16), by positivity, ?_⟩
  intro ν hν
  obtain ⟨δQ, hδQ, hQ⟩ := hQ ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨δa, hδa, hsmall⟩ := exists_coherent_delta_threshold hC₁
  refine ⟨min δQ δa, by positivity, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hQ⟩ := hQ δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD htime
  have hs := hsmall δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  refine ⟨hQ L hL, hη.1, hηhalf, ?_, hν.2.trans (min_le_right _ _), hδ.1, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hL₀.trans hL⟩
  change 2 * η ^ 20 < a - Real.sqrt η
  linarith [hreserve.1, hreserve.2]

end WaveTurbulence.LGSpine
