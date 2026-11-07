/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCoupledTripleRadius
public import WaveTurbulence.Foundations.FinalCount.AppBPairGoodGain
import Mathlib.Tactic

/-! # A strict good power saving for radius-two coupled triple fibers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset Filter CountLemmas

theorem appb_coupled_triple_good_gain (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ a b c : Mom d, ∀ nv : Fin d → ℤ, ∀ α β : ℝ, ∀ ζsel : Fin 3,
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖latticePoint L q.1-a‖ ≤ 2 ∧ ‖latticePoint L q.2.1-b‖ ≤ 2 ∧
        ‖latticePoint L q.2.2-c‖ ≤ 2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)-α| ≤ appbWidth δ γ m L ∧
        |inner ℝ (![latticePoint L q.1-latticePoint L nv,
          latticePoint L q.1+latticePoint L q.2.1-latticePoint L nv,
          latticePoint L q.1+latticePoint L q.2.1-latticePoint L nv-latticePoint L q.2.2] ζsel)
            (latticePoint L q.2.2)-β| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
  obtain ⟨C,L₀,hC,hbase⟩ := appb_coupled_triple_radius_two_log_bound d hd γ hγ
  have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  have hcoef := appb_log_coefficient_eventual (C*δ⁻¹) δ
    (3*((d : ℝ)-γ)-min γ (1-γ)) (3*((d : ℝ)-γ)-3*min γ (1-γ)/4) (2*m)
    (by linarith only [hg0])
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp (hcoef.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max L₀ L₁,?_⟩
  intro L hL a b c nv α β ζsel s hs
  obtain ⟨hbound,hL1⟩ := hL₁ L ((le_max_right _ _).trans hL)
  have hb := hbase L ((le_max_left _ _).trans hL) hL1 δ hδ m a b c nv α β ζsel s hs
  refine hb.trans (?_ : C*δ⁻¹^2*(1+Real.log L)^(2*m)*L^(3*((d : ℝ)-γ)-min γ (1-γ)) ≤ _)
  convert hbound using 1 <;> ring

end WaveTurbulence.Mole
