/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceTimeFactors
public import WaveTurbulence.Foundations.SumintPar.LinearShortWindow

/-!
# The linear time-window bounds for the actual source factor

The fourfold Fourier modulation turns the source half scale into
`4 * sourceHalfScale`. Both the cancellation and trivial branches apply
to this literal factor on the enlarged input interval.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set WithLp

namespace WaveTurbulence.SumintPar

/-- The literal source linear frequency in the landed affine-flow form. -/
theorem source_linear_frequency {d : ℕ} (ν r : Mom d) (c s t : ℝ) :
    (4:ℝ) • (ν+(c*(s-t)) • r) = ((4*c)*(s-t)) • r+(4:ℝ) • ν := by
  rw [smul_add,smul_smul]
  have he : 4*(c*(s-t)) = (4*c)*(s-t) := by ring
  rw [he,add_comm]

/-- TARGET sumint's actual distinguished linear factor, cancellation branch. -/
theorem integral_linearTimeSum_le_cancellation {d : ℕ} (D : SumintDatum d)
    {L : ℝ} (hL : 1 ≤ 4*L) (γ δ : ℝ) (hc : 0 < sourceHalfScale L γ δ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (hr : r ≠ 0)
    (t : ℝ) (i : Fin D.S.I) {a b : ℝ} (hab : a ≤ b)
    (hshort : ((4*sourceHalfScale L γ δ)*(b-a))*‖r‖ ≤ 4*L) :
    (∫ s in Icc a b, ‖linearTimeSum D L γ δ p ν r t i s‖) ≤
      (4*sourceHalfScale L γ δ)⁻¹ *
        (LemLin.linearCancellationConstant d*(4*L)^d/‖r‖) := by
  unfold linearTimeSum
  simp_rw [source_linear_frequency]
  exact linear_short_window hL (by positivity) hab _ r _ hr hshort t

/-- The same source factor, trivial branch, with exact enlarged interval length. -/
theorem integral_linearTimeSum_le_trivial {d : ℕ} (D : SumintDatum d)
    {L : ℝ} (hL : 1 ≤ 4*L) (γ δ : ℝ) (hc : 0 < sourceHalfScale L γ δ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (t : ℝ) (i : Fin D.S.I) {a b : ℝ} (hab : a ≤ b) :
    (∫ s in Icc a b, ‖linearTimeSum D L γ δ p ν r t i s‖) ≤
      (b-a)*(3:ℝ)^d*(4*L)^d := by
  unfold linearTimeSum
  simp_rw [source_linear_frequency]
  exact linear_trivial_window hL (by positivity) hab _ r _ t

end WaveTurbulence.SumintPar
