/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceTimeFactors

/-!
# The literal outer-time pair modulations

These names expose the source pair's fixed centres, positive quadratic
time scale and two continuous outer-time frequencies. They identify the
actual source factor with the general physical pair-window estimates.
-/

@[expose] public section
set_option autoImplicit false

open WithLp

namespace WaveTurbulence.SumintPar

/-- First source pair modulation as a function of its outer time. -/
@[expose] noncomputable def pairOuterFrequencyX {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (s : ℝ) : Mom d :=
  (4:ℝ) • (ν (D.S.xSlot a.1 a.2)+(sourceHalfScale L γ δ*(s-t)*(D.ζc a.1 a.2 0:ℝ)) • r)

/-- Second source pair modulation as a function of its outer time. -/
@[expose] noncomputable def pairOuterFrequencyY {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (s : ℝ) : Mom d :=
  (4:ℝ) • (ν (D.S.ySlot a.1 a.2)+(sourceHalfScale L γ δ*(s-t)*(D.ζc a.1 a.2 1:ℝ)) • r)

/-- Both source modulations are continuous, as required in the full strip estimates. -/
theorem continuous_pairOuterFrequencyX {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : Continuous (pairOuterFrequencyX D L γ δ ν r t a) := by
  unfold pairOuterFrequencyX
  fun_prop

/-- Continuity of the second literal modulation. -/
theorem continuous_pairOuterFrequencyY {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : Continuous (pairOuterFrequencyY D L γ δ ν r t a) := by
  unfold pairOuterFrequencyY
  fun_prop

/-- Exact source-factor identification in the physical strip-estimate convention. -/
theorem pairTimeSum_eq_physical_bilinear {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (z : ℝ × ℝ) :
    pairTimeSum D L γ δ p ν r t a z =
      WeylSums.bilinearLatticeSum (4*L) ((16*sourceHalfScale L γ δ)*(z.1-z.2))
        ((1/4:ℝ) • toLp 2 (p (D.S.xSlot a.1 a.2))) ((1/4:ℝ) • toLp 2 (p (D.S.ySlot a.1 a.2)))
        (pairOuterFrequencyX D L γ δ ν r t a z.1) (pairOuterFrequencyY D L γ δ ν r t a z.1) := by
  unfold pairTimeSum pairOuterFrequencyX pairOuterFrequencyY
  rw [show 16*(sourceHalfScale L γ δ*(z.1-z.2)) = (16*sourceHalfScale L γ δ)*(z.1-z.2) by ring]

end WaveTurbulence.SumintPar
