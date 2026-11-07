/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourcePairWindow
public import WaveTurbulence.Foundations.SumintPar.SourceWindowGeometry
public import WaveTurbulence.Foundations.SumintPar.SourceScalePowers

/-!
# Ordinary source pair cancellation with the exact final scale

The standing relation τstar=Dsteps*δ puts every enlarged pair window
inside a fixed Weyl window. Thus its constant is chosen before δ and
Dsteps, and the resulting source scale is δ⁻¹ L^{2(d-γ)}.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- TARGET sumint Step 2: ordinary pair cancellation, uniform in every source datum and local cell. -/
theorem exists_source_normalized_pair_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηγ : η ≤ 2*((d:ℝ)-1)*(1-γ)) (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ C R : ℝ, 1 ≤ C ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
        (a : Σ i : Fin D.S.I, Fin (D.S.m i)), h ∈ Icc (0:ℝ) 1 →
      D.q (.inl ⟨a.1,a.2.succ⟩) < N → D.q (.inr (.inl a)) < N →
      (∫ s in Icc ((D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)-c-h)
          ((D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)+1-c+h),
        ∫ s' in Icc ((D.q (.inr (.inl a)):ℝ)-c-h)
          ((D.q (.inr (.inl a)):ℝ)+1-c+h), ‖pairTimeSum D L γ δ p ν r t a (s,s')‖) ≤
      C*δ⁻¹*L^(2*((d:ℝ)-γ)) := by
  let T₀ := 8*(τstar+2)
  have hT₀ : 0 < T₀ := by dsimp [T₀]; positivity
  obtain ⟨C,R,hC,hR,hbound⟩ := exists_source_pair_window_bound d hd γ hγ η hη hηγ T₀ hT₀
  refine ⟨max 1 (3*C*4^(2*d)),R,le_max_left _ _,hR,?_⟩
  intro L hL D δ N hδ hτ p ν r t c h a hh hq hp
  have hL1 : 1 ≤ L := by linarith [hR.trans hL]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hscale : 0 < sourceHalfScale L γ δ := by
    unfold sourceHalfScale
    exact div_pos (mul_pos hδ.1 (Real.rpow_pos_of_pos hLp _)) (by norm_num)
  have hwin := source_enlarged_window_endpoints (c := c) hq hp hLp.le hγ.1.le hδ.1.le hδ.2 hτ hh.1 hh.2
  have hlu : ((D.q (.inr (.inl a)):ℝ)-c-h) ≤ ((D.q (.inr (.inl a)):ℝ)+1-c+h) := by linarith [hh.1]
  have hvw : ((D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)-c-h) ≤
      ((D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)+1-c+h) := by linarith [hh.1]
  have hb := hbound L (by linarith : R ≤ 4*L) D δ hscale p ν r t a
    ((D.q (.inr (.inl a)):ℝ)-c-h) ((D.q (.inr (.inl a)):ℝ)+1-c+h)
    ((D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)-c-h) ((D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)+1-c+h)
    hlu hvw hwin
  have hs := source_scale_inv_mul_nat_pow hLp (by norm_num : (0:ℝ) < 16) hδ.1
    (by norm_num : (0:ℝ) ≤ 4) γ (2*d)
  have hinv : ((16:ℝ)/2)⁻¹ = 1/8 := by norm_num
  have hexp : ((2*d:ℕ):ℝ)-2*γ = 2*((d:ℝ)-γ) := by push_cast; ring
  rw [hinv,hexp] at hs
  let Z := (16*sourceHalfScale L γ δ)⁻¹*C*(4*L)^(2*d)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hlen : ((D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)+1-c+h)-
      ((D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)-c-h) ≤ 3 := by linarith [hh.2]
  have hK : 3*C*(1/8:ℝ)*4^(2*d) ≤ max 1 (3*C*4^(2*d)) := by
    have hn : 0 ≤ 3*C*4^(2*d) := by positivity
    exact (show 3*C*(1/8:ℝ)*4^(2*d) ≤ 3*C*4^(2*d) by nlinarith only [hn]).trans (le_max_right _ _)
  calc
    _ ≤ (((D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)+1-c+h)-
        ((D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)-c-h))*Z := hb.trans_eq (by dsimp [Z]; ring)
    _ ≤ 3*Z := mul_le_mul_of_nonneg_right hlen hZ
    _ = (3*C*(1/8:ℝ)*4^(2*d))*δ⁻¹*L^(2*((d:ℝ)-γ)) := by
      dsimp [Z]
      have he : (16*sourceHalfScale L γ δ)⁻¹*C*(4*L)^(2*d) =
          C*((16*sourceHalfScale L γ δ)⁻¹*(4*L)^(2*d)) := by ring
      rw [he,hs]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (inv_nonneg.mpr hδ.1.le))
      (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.SumintPar
