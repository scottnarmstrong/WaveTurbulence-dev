/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceTimeFactors
public import WaveTurbulence.Foundations.SumintPar.CaseCAmplitude
public import WaveTurbulence.Foundations.SumintPar.BilinearParameterContinuity
public import WaveTurbulence.Foundations.SumintPar.CubicParameterContinuity

/-!
# Genuine compact-box integrability of source time factors

Their linear modulations depend continuously on the outer times.
Joint parameter continuity of the finite lattice sums gives continuous
local source factors; the case-(c) multiplier is continuous in its
proof range 1-3η≥0.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- The actual linear source sum is continuous in its one local input time. -/
theorem continuous_linearTimeSum {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (i : Fin D.S.I) : Continuous (linearTimeSum D L γ δ p ν r t i) := by
  unfold linearTimeSum
  apply (LemLin.continuous_linearLatticeSum (by positivity : 0 < 4*L) _).comp
  fun_prop

/-- The actual pair source sum is continuous jointly in its two local input times. -/
theorem continuous_pairTimeSum {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : Continuous (pairTimeSum D L γ δ p ν r t a) := by
  unfold pairTimeSum
  exact continuous_bilinearLatticeSum_parameters (by positivity : 0 < 4*L) _ _ _ _ _
    (by fun_prop) (by fun_prop) (by fun_prop)

/-- The actual normal sum is continuous jointly in its three local input times. -/
theorem continuous_normalTimeSum {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) : Continuous (normalTimeSum D L γ δ p ν r t i) := by
  unfold normalTimeSum
  exact continuous_cubicLatticeSum_parameters (by positivity : 0 < 4*L) _ _ _ _ _ _ _ _ _
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-- The source case-(c) amplitude is continuous in the actual nonnegative-exponent proof range. -/
theorem continuous_pairGapAmplitude {d : ℕ} (D : SumintDatum d) (η : ℝ)
    (hη : 0 ≤ 1-3*η) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) :
    Continuous (pairGapAmplitude D η a) := by
  classical
  unfold pairGapAmplitude
  split_ifs
  · apply Continuous.rpow_const
    · fun_prop
    · intro z
      exact Or.inr hη
  · exact continuous_const

end WaveTurbulence.SumintPar
