/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceTimeFactors
public import WaveTurbulence.Foundations.Sumint.BilinearReversedPairWindow

/-!
# The ordinary pair-window estimate for the literal source factor

Uniformity of the landed bilinear estimate includes the affine
outer-time modulations occurring in TARGET sumint. The constant is
chosen before the source delta, datum and centres.
-/

public section

open MeasureTheory Set WithLp

namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 2: ordinary cancellation for an actual source pair. -/
theorem exists_source_pair_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηγ : η ≤ 2*((d:ℝ)-1)*(1-γ)) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ 4*L →
      ∀ (D : SumintDatum d) (δ : ℝ), 0 < sourceHalfScale L γ δ →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
        (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (l u v w : ℝ), l ≤ u → v ≤ w →
      (∀ s ∈ Icc v w,
        -(T₀*(4*L)^(2*γ)) ≤ (16*sourceHalfScale L γ δ)*(l-s) ∧
        (16*sourceHalfScale L γ δ)*(u-s) ≤ T₀*(4*L)^(2*γ)) →
      (∫ s in Icc v w, ∫ s' in Icc l u, ‖pairTimeSum D L γ δ p ν r t a (s,s')‖) ≤
        (w-v)*(16*sourceHalfScale L γ δ)⁻¹*C*(4*L)^(2*d) := by
  obtain ⟨C,L₀,hC,hL₀,hbound⟩ :=
    exists_bilinear_reversed_pair_window_bound d hd γ hγ η hη hηγ T₀ hT₀
  refine ⟨C,L₀,hC,hL₀,?_⟩
  intro L hL D δ hc p ν r t a l u v w hlu hvw hwin
  have he (s s' : ℝ) :
      16*(sourceHalfScale L γ δ*(s-s')) = (16*sourceHalfScale L γ δ)*(s-s') := by ring
  unfold pairTimeSum
  simp_rw [he]
  exact hbound (4*L) hL _ _ _ _ (16*sourceHalfScale L γ δ) l u v w
    (by positivity) hlu hvw hwin

end WaveTurbulence.Sumint
