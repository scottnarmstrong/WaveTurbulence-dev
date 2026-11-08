/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.Flower.FiltNT.Crude

/-! # FILT-NT exports (D5c): `FiltPoleFourier` and `FiltCrudeNormalizedSum`, as stated in `ProtDefs` -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence.ApproxNT

namespace WaveTurbulence.Flower.FiltNT

/-- The frozen cutoff `WaveTurbulence.chi0` used by `ProtDefs` is `Fourier.chi0` (as main's `FC23.frozen_chi0_eq`). -/
theorem frozen_chi0_eq' (x : ℝ) : WaveTurbulence.chi0 x = Fourier.chi0 x := by
  unfold WaveTurbulence.chi0 Fourier.chi0
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, Real.smoothTransition.one_of_one_le (x := 2 + 2 * x) (by linarith), mul_one]
  · rw [abs_of_nonpos hx, Real.smoothTransition.one_of_one_le (x := 2 - 2 * x) (by linarith), one_mul]
    ring_nf

theorem gS_eq_frozen (S : ℝ) :
    (fun u : ℝ => ((Fourier.chiInfinity u / u * WaveTurbulence.chi0 (u / S) : ℝ) : ℂ)) = gS S := by
  funext u
  simp only [gS, frozen_chi0_eq']

/-- **D5c, o82 Prop 2.1**: the scale-uniform Fourier decay of the filtered pole. -/
theorem filtPoleFourier : ProtDefs.FiltPoleFourier := by
  intro d hd
  obtain ⟨K, hK0, hK⟩ := filtPole_bound d hd
  refine ⟨K, hK0, fun S hS σ => ?_⟩
  rw [gS_eq_frozen]
  exact hK S hS σ

/-- `ProtDefs.filtProfile` is `filtProf`. -/
theorem filtProfile_eq {n : ℕ} (J : Finset (Fin n)) (S : Fin n → ℝ)
    (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) : ProtDefs.filtProfile J S Ψ = filtProf J S Ψ := by
  funext Ω
  simp only [ProtDefs.filtProfile, filtProf, gS, frozen_chi0_eq']

/-- **D5c FILT-NT, o82 Thm 10.1 (10.5)**: main's `crude_normalized_sum` for the filtered profile.
(`ProtDefs` now writes the smooth hypothesis `ContDiff ℝ (⊤ : ℕ∞) Ψ`, as main does; wt-orch fixed the analytic `⊤`
that D5c reported.) -/
theorem filtCrudeNormalizedSum : ProtDefs.FiltCrudeNormalizedSum := by
  intro d hd γ η hγ hη0 hη1 hηd hηγ C₀ hC₀
  obtain ⟨Kp, hKp, hb⟩ := filtPole_bound d (by omega)
  obtain ⟨C, hC, h⟩ := filt_crude_normalized_sum hd Kp hKp hb hγ hη0 hη1 hηd hηγ hC₀
  refine ⟨C, hC, fun A => ?_⟩
  obtain ⟨L₀, hL₀⟩ := h A
  refine ⟨L₀, fun L hL δ hδ hδ1 n hn hlog H hH lt _ xs ys hxs hys a b lam hlam W hWc hWs hW J S hS Ψ hΨ hD => ?_⟩
  rw [filtProfile_eq]
  exact hL₀ L hL δ hδ hδ1 n hn hlog H hH lt xs ys hxs hys a b lam hlam W hWc hWs hW J S hS Ψ
    hΨ hD

end WaveTurbulence.Flower.FiltNT
