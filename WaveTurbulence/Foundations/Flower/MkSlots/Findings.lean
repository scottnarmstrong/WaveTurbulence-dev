/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Bounds

/-! # B3s MK-SLOTS: formal witnesses for the findings on `MarkedClassRepresentsMK`

* **F-B3s-1.** `chiD = -u·χ₀'(u)` exceeds `1` somewhere (`exists_one_lt_abs_chiD`, by the mean value theorem on
  `[1/2, 1]`, where `χ₀` drops from `1` to `0`). `ClassPieceOK.sel_spec` asks the filter of a residual selected vertex
  to be exactly `chiD`, while `PieceRestB3s.filt_ok` (verbatim from `SoundMKFull`) asks every filter to be bounded by
  `1`. Hence (before ruling R179) every `ClassPieceOK` had `selR = ∅`: no residual selected vertex can be
  declared, and the mass `selMassMK … ∅` then demands the gain `R_j^{-1/18}` for every selected tree, including trees
  whose selected stem vertex is an atom of `G_sb` (where Stage 1′ has no time integration that could produce it; the
  gain comes from the C-side analysis of a residual selection, o73 P 20.1 = D7). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.MkSlots
open WaveTurbulence.Flower.MkDefs

/-- `χ₀ = 1` at `1/2` and `χ₀ = 0` at `1`, so by the mean value theorem `χ₀' = -2` at some `u ∈ (1/2, 1)`, where
`chiD u = 2u > 1`. -/
theorem exists_one_lt_abs_chiD : ∃ u : ℝ, 1 < |chiD u| := by
  have hc : ContDiff ℝ 1 Fourier.chi0 := Fourier.chi0_contDiff
  have hcont : ContinuousOn Fourier.chi0 (Icc (1 / 2 : ℝ) 1) := hc.continuous.continuousOn
  have hdiff : DifferentiableOn ℝ Fourier.chi0 (Ioo (1 / 2 : ℝ) 1) :=
    (hc.differentiable one_ne_zero).differentiableOn
  obtain ⟨u, hu, hder⟩ := exists_deriv_eq_slope Fourier.chi0 (by norm_num : (1 / 2 : ℝ) < 1) hcont hdiff
  have h1 : Fourier.chi0 (1 / 2) = 1 := Fourier.chi0_eq_one (by norm_num [abs_of_pos])
  have h0 : Fourier.chi0 1 = 0 := Fourier.chi0_eq_zero (by norm_num)
  rw [h1, h0] at hder
  refine ⟨u, ?_⟩
  have hD : chiD u = 2 * u := by
    unfold chiD
    rw [chi0_eq_fourier, hder]
    norm_num
    ring
  rw [hD, abs_of_pos (by linarith [hu.1])]
  linarith [hu.1]

end WaveTurbulence.Flower.MkSlots
