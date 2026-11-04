/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceTimeFactors
public import WaveTurbulence.Foundations.Sumint.BilinearFractionalAffineWindow

/-!
# The literal case-(c) pair window

The source exponent is `p = 1 - 3η`; keeping a general exponent in
`[0,1]` exposes the precise small-region gain. The large-region term
retains its Weyl reserve and maximum physical gap factor.
-/

public section

open MeasureTheory Set WithLp

namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 2: the actual pair with its fractional time-gap multiplier. -/
theorem exists_source_fractional_pair_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ Cs Cm L₀ : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ L₀ ∧
      ∀ L : ℝ, L₀ ≤ 4*L → ∀ (D : SumintDatum d) (δ : ℝ),
      0 < sourceHalfScale L γ δ →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
        (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ρ l u v w : ℝ),
      0 ≤ ρ → ρ ≤ 1 → l ≤ u → v ≤ w →
      (∀ s ∈ Icc v w,
        -(T₀*(4*L)^(2*γ)) ≤ (16*sourceHalfScale L γ δ)*(l-s) ∧
        (16*sourceHalfScale L γ δ)*(u-s) ≤ T₀*(4*L)^(2*γ)) →
      (∫ s in Icc v w, ∫ s' in Icc l u,
        |s-s'|^ρ*‖pairTimeSum D L γ δ p ν r t a (s,s')‖) ≤
      (w-v)*(16*sourceHalfScale L γ δ)⁻¹ *
        ((16*sourceHalfScale L γ δ)^(-ρ)*Cs*(4*L)^(2*d) +
        (T₀*(4*L)^(2*γ)/(16*sourceHalfScale L γ δ))^ρ *
          Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by
  obtain ⟨Cs,Cm,L₀,hCs,hCm,hL₀,hbound⟩ :=
    exists_bilinear_fractional_affine_window_bound d hd γ hγ η hη T₀ hT₀
  refine ⟨Cs,Cm,L₀,hCs,hCm,hL₀,?_⟩
  intro L hL D δ hc p ν r t a ρ l u v w hρ hρ1 hlu hvw hwin
  let c := 16*sourceHalfScale L γ δ
  let B := c⁻¹*(c^(-ρ)*Cs*(4*L)^(2*d) +
    (T₀*(4*L)^(2*γ)/c)^ρ*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η))
  have hb : ∀ᵐ s ∂volume.restrict (Icc v w),
      (∫ s' in Icc l u, |s-s'|^ρ*‖pairTimeSum D L γ δ p ν r t a (s,s')‖) ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have he (s' : ℝ) : 16*(sourceHalfScale L γ δ*(s-s')) = c*(s-s') := by dsimp [c]; ring
    unfold pairTimeSum
    simp_rw [he]
    exact hbound (4*L) hL _ _ _ _ c ρ l u s (by dsimp [c]; positivity)
      hρ hρ1 hlu (hwin s hs).1 (hwin s hs).2
  calc
    _ ≤ ∫ _s in Icc v w, B := integral_mono_of_nonneg
      (ae_of_all _ (fun s => integral_nonneg (fun s' =>
        mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (norm_nonneg _))))
      (integrable_const B) hb
    _ = _ := by
      rw [integral_const]
      simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hvw),smul_eq_mul]
      dsimp [B,c]
      ring

end WaveTurbulence.Sumint
