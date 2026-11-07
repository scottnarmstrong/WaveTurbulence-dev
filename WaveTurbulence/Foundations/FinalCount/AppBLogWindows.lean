/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairGrowth
public import WaveTurbulence.Foundations.FinalCount.AppBCosetPairs
public import WaveTurbulence.Foundations.FinalCount.AppBCosetTriples
import Mathlib.Tactic

/-! # Basic counting estimates with polynomial logarithmic windows -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set CountLemmas

noncomputable def appbEffectiveDelta (δ L : ℝ) (m : ℕ) : ℝ := δ/(1+Real.log L)^m

theorem appbEffectiveDelta_mem {δ L : ℝ} (hδ : δ ∈ Ioc (0 : ℝ) 1) (hL : 1 ≤ L) (m : ℕ) :
    appbEffectiveDelta δ L m ∈ Ioc (0 : ℝ) 1 := by
  have hlog := Real.log_nonneg hL
  have hpow : 1 ≤ (1+Real.log L)^m := one_le_pow₀ (by linarith only [hlog])
  constructor
  · exact div_pos hδ.1 (zero_lt_one.trans_le hpow)
  · exact (div_le_one (zero_lt_one.trans_le hpow)).mpr (hδ.2.trans hpow)

theorem appbEffectiveDelta_inv (δ L : ℝ) (m : ℕ) :
    (appbEffectiveDelta δ L m)⁻¹ = δ⁻¹*(1+Real.log L)^m := by
  unfold appbEffectiveDelta
  rw [inv_div]
  ring

theorem appb_coset_triple_log_window_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ ∈ Ioo (0 : ℝ) 1,
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, 1 ≤ L → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ m : ℕ,
    ∀ w a b c : Mom d, ∀ nk : Fin d → ℤ, ∀ β : ℝ,
      (appbCosetTripleSet L w a b c nk β (appbWidth δ γ m L)).Finite ∧
      ((appbCosetTripleSet L w a b c nk β (appbWidth δ γ m L)).ncard : ℝ) ≤
        C*δ⁻¹*(1+Real.log L)^m*L^(2*((d : ℝ)-γ)) := by
  intro d hd γ hγ
  obtain ⟨C,L₀,h⟩ := appb_coset_triple_bound d hd γ hγ
  refine ⟨C,L₀,?_⟩
  intro L hL hL1 δ hδ m w a b c nk β
  have hb := h L hL (appbEffectiveDelta δ L m) (appbEffectiveDelta_mem hδ hL1 m) w a b c nk β
  simpa only [appbEffectiveDelta_inv,appbWidth,mul_assoc] using hb

theorem appb_coset_positive_pair_log_window_bound {d : ℕ} (hd : 2 ≤ d) {L δ γ : ℝ}
    (hL : 1 ≤ L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ≤ 1) (m : ℕ)
    (w a b : Mom d) (nk : Fin d → ℤ) (β : ℝ) :
    ((appbCosetPairSet L w a b nk β (appbWidth δ γ m L) 1).ncard : ℝ) ≤
      (2*3^(d-2)*(6*Real.pi+1284002))*δ⁻¹*(1+Real.log L)^m*
        L^((d : ℝ)-γ-min γ (1-γ)) := by
  have hb := appb_coset_positive_pair_bound hd hL (appbEffectiveDelta_mem hδ hL m) hγ w a b nk β
  simpa only [appbEffectiveDelta_inv,appbWidth,mul_assoc] using hb

theorem appb_coset_negative_pair_log_window_bound {d : ℕ} (hd : 0 < d) {L δ γ η : ℝ}
    (hL : 1 ≤ L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hη : η ≤ 1-γ) (m : ℕ)
    (w a b : Mom d) (nk : Fin d → ℤ) (β : ℝ)
    (hgap : L^(-γ+η) ≤ ‖latticePoint L nk‖) :
    ((appbCosetPairSet L w a b nk β (appbWidth δ γ m L) (-1)).ncard : ℝ) ≤
      (3^(d-1)*((d : ℝ)+1))*δ⁻¹*(1+Real.log L)^m*L^((d : ℝ)-γ-η) := by
  have hb := appb_coset_negative_pair_large_bound hd hL (appbEffectiveDelta_mem hδ hL m) hη w a b nk β hgap
  simpa only [appbEffectiveDelta_inv,appbWidth,mul_assoc] using hb

end WaveTurbulence.Mole
