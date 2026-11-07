/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLogWindows
import Mathlib.Tactic

/-! # Pair gains used by the good reinsertion operations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Filter CountLemmas Set

/-- Fixed coefficients and any fixed logarithmic power fit in a strict
power gap. The threshold does not depend on spatial or energy centers. -/
theorem appb_log_coefficient_eventual (C δ a b : ℝ) (m : ℕ) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop, C*δ⁻¹*(1+Real.log L)^m*L^a ≤ L^b := by
  have hε : 0 < (b-a)/2 := by linarith only [hab]
  have hg := growth_mul ((appb_growth_log_natpow m hε).const_mul_left (C*δ⁻¹))
    (growth_rpow a) (c := a+(b-a)/2) (by ring_nf; exact le_rfl)
  exact growth_eventually_le hg (by linarith only [hab])

/-- The opposite-sign, large internal-gap pair count needed after good
reinsertion, with a raw saving of 31 gamma0/48. -/
theorem appb_negative_pair_good_gain (d : ℕ) (hd : 0 < d) (δ γ : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ w a b : Mom d, ∀ nk : Fin d → ℤ, ∀ β : ℝ,
      L^(-γ+2*min γ (1-γ)/3) ≤ ‖latticePoint L nk‖ →
      ((appbCosetPairSet L w a b nk β (appbWidth δ γ m L) (-1)).ncard : ℝ) ≤
        L^((d : ℝ)-γ-31*min γ (1-γ)/48) := by
  have hg0 := lt_min hγ.1 (sub_pos.mpr hγ.2)
  have hη : 2*min γ (1-γ)/3 ≤ 1-γ := by linarith only [hg0,min_le_right γ (1-γ)]
  have hcomp := appb_log_coefficient_eventual (3^(d-1)*((d : ℝ)+1)) δ
    ((d : ℝ)-γ-2*min γ (1-γ)/3) ((d : ℝ)-γ-31*min γ (1-γ)/48) m
    (by linarith only [hg0])
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp (hcomp.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨L₀,?_⟩
  intro L hL w a b nk β hgap
  obtain ⟨hbound,hL1⟩ := hL₀ L hL
  exact (appb_coset_negative_pair_log_window_bound hd hL1 hδ hη m w a b nk β hgap).trans hbound

/-- The same-sign pair count has an even larger gamma0 gain, so it obeys
the same uniform raw good bound. -/
theorem appb_positive_pair_good_gain (d : ℕ) (hd : 2 ≤ d) (δ γ : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ w a b : Mom d, ∀ nk : Fin d → ℤ, ∀ β : ℝ,
      ((appbCosetPairSet L w a b nk β (appbWidth δ γ m L) 1).ncard : ℝ) ≤
        L^((d : ℝ)-γ-31*min γ (1-γ)/48) := by
  have hg0 := lt_min hγ.1 (sub_pos.mpr hγ.2)
  have hcomp := appb_log_coefficient_eventual (2*3^(d-2)*(6*Real.pi+1284002)) δ
    ((d : ℝ)-γ-min γ (1-γ)) ((d : ℝ)-γ-31*min γ (1-γ)/48) m
    (by linarith only [hg0])
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp (hcomp.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨L₀,?_⟩
  intro L hL w a b nk β
  obtain ⟨hbound,hL1⟩ := hL₀ L hL
  exact (appb_coset_positive_pair_log_window_bound hd hL1 hδ hγ.2.le m w a b nk β).trans hbound

end WaveTurbulence.Mole
