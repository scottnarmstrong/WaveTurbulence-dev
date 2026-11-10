/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltNT.Cell
public import WaveTurbulence.Foundations.ApproxNT.Conclusion1

/-! # FILT-NT: DH23 Prop 6.4 conclusion (1) for the filtered profile

Main's `ApproxNT.approxnt_conclusion1` with `resProfile J Ψ₁` replaced by `filtProf J S Ψ₁`, uniformly in the filter
scales `S_j ≥ 1`. The proof is main's, with the truncated-profile cell identification dropped (the filtered profile
needs no truncation) and the cell estimate `exists_filt_cell_bound`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset WithLp WaveTurbulence.ApproxNT
open scoped FourierTransform ContDiff ENNReal

namespace WaveTurbulence.Flower.FiltNT

variable {d n : ℕ}

theorem continuous_filtProf {ι : Type} [Fintype ι] [DecidableEq ι] (J : Finset ι) (S : ι → ℝ)
    {Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ} (hΨ : Continuous Ψ₁) : Continuous (filtProf J S Ψ₁) := by
  refine (continuous_finsetProd _ fun j _ => ?_).mul (hΨ.comp ?_)
  · exact (continuous_gS _).comp (continuous_apply j)
  · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply (i : ι))


end WaveTurbulence.Flower.FiltNT
