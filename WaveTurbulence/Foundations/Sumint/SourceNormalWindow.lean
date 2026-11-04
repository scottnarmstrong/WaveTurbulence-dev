/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceTimeFactors
public import WaveTurbulence.Foundations.Sumint.CubicTripleWindow

/-!
# Ordinary normal cancellation for the actual source factor

The source's third time fixes all three linear modulations. The two
quadratic times then range over a rectangle at scale sixteen times the
source half scale. Both normal forms are included uniformly.
-/

public section

open MeasureTheory Set WithLp

namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 2: the literal normal factor, keeping both contributions. -/
theorem exists_source_normal_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ Cs Cm L₀ : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ L₀ ∧
      ∀ L : ℝ, L₀ ≤ 4*L → ∀ (D : SumintDatum d) (δ : ℝ),
      0 < sourceHalfScale L γ δ →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
        (i : {i : Fin D.S.I // D.S.nor i = true}) (a b l u v w : ℝ),
      a ≤ b → l ≤ u → v ≤ w →
      (∀ s ∈ Icc v w,
        (-(T₀*(4*L)^(2*γ)) ≤ (16*sourceHalfScale L γ δ)*(a-s) ∧
          (16*sourceHalfScale L γ δ)*(b-s) ≤ T₀*(4*L)^(2*γ)) ∧
        (-(T₀*(4*L)^(2*γ)) ≤ (16*sourceHalfScale L γ δ)*(l-s) ∧
          (16*sourceHalfScale L γ δ)*(u-s) ≤ T₀*(4*L)^(2*γ))) →
      (∫ s in Icc v w, ∫ s₀ in Icc a b, ∫ s₁ in Icc l u,
        ‖normalTimeSum D L γ δ p ν r t i ![s₀,s₁,s]‖) ≤
      (w-v)*(16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹ *
        (Cs*(4*L)^(3*d)+Cm*(4*L)^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log (4*L)) := by
  obtain ⟨Cs,Cm,L₀,hCs,hCm,hL₀,hbound⟩ :=
    exists_cubic_triple_window_bound d hd γ hγ T₀ hT₀
  refine ⟨Cs,Cm,L₀,hCs,hCm,hL₀,?_⟩
  intro L hL D δ hc p ν r t i a b l u v w hab hlu hvw hwin
  have he (s s' : ℝ) :
      16*(sourceHalfScale L γ δ*(s-s')) = (16*sourceHalfScale L γ δ)*(s-s') := by ring
  unfold normalTimeSum
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  simp_rw [he]
  exact hbound (4*L) hL (D.Λsel i.1) _ _ _ _ _ _
    (16*sourceHalfScale L γ δ) a b l u v w (by positivity) hab hlu hvw hwin

end WaveTurbulence.Sumint
