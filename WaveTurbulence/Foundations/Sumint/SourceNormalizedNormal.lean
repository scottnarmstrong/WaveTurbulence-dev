/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceNormalWindow
public import WaveTurbulence.Foundations.Sumint.SourceWindowGeometry
public import WaveTurbulence.Foundations.Sumint.CubicRescaleBound

/-!
# Normal source factors with both normalized contributions retained

The constants are chosen before δ and Dsteps. The two powers are
3d-4γ and 3d-3γ-2γ₀, the latter with a logarithm. Their distinction is
needed when pairing the normal factor with its linear input.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 2: the exact ordinary normal source window at the normalized scale. -/
theorem exists_source_normalized_normal_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ C R : ℝ, 1 ≤ C ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
        (i : {i : Fin D.S.I // D.S.nor i = true}), h ∈ Icc (0:ℝ) 1 →
      D.q (.inr (.inr ⟨i,0⟩)) < N → D.q (.inr (.inr ⟨i,1⟩)) < N → D.q (.inr (.inr ⟨i,2⟩)) < N →
      (∫ s₂ in Icc ((D.q (.inr (.inr ⟨i,2⟩)):ℝ)-c-h)
          ((D.q (.inr (.inr ⟨i,2⟩)):ℝ)+1-c+h),
        ∫ s₀ in Icc ((D.q (.inr (.inr ⟨i,0⟩)):ℝ)-c-h)
          ((D.q (.inr (.inr ⟨i,0⟩)):ℝ)+1-c+h),
          ∫ s₁ in Icc ((D.q (.inr (.inr ⟨i,1⟩)):ℝ)-c-h)
            ((D.q (.inr (.inr ⟨i,1⟩)):ℝ)+1-c+h),
            ‖normalTimeSum D L γ δ p ν r t i ![s₀,s₁,s₂]‖) ≤
      C*δ^(-2:ℝ)*(L^(3*(d:ℝ)-4*γ)+
        L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L) := by
  let T₀ := 8*(τstar+2)
  have hT₀ : 0 < T₀ := by dsimp [T₀]; positivity
  obtain ⟨Cs,Cm,R,hCs,hCm,hR,hbound⟩ := exists_source_normal_window_bound d hd γ hγ T₀ hT₀
  refine ⟨cubicRescaleConstant d γ Cs Cm,R,one_le_cubicRescaleConstant d γ hCs hCm,hR,?_⟩
  intro L hL D δ N hδ hτ p ν r t c h i hh hq0 hq1 hq2
  have hL2 : 2 ≤ L := hR.trans hL
  have hLp : 0 < L := by linarith only [hL2]
  have hscale : 0 < sourceHalfScale L γ δ := by
    unfold sourceHalfScale
    exact div_pos (mul_pos hδ.1 (Real.rpow_pos_of_pos hLp _)) (by norm_num)
  have hw0 := source_enlarged_window_endpoints (c := c) hq2 hq0
    hLp.le hγ.1.le hδ.1.le hδ.2 hτ hh.1 hh.2
  have hw1 := source_enlarged_window_endpoints (c := c) hq2 hq1
    hLp.le hγ.1.le hδ.1.le hδ.2 hτ hh.1 hh.2
  have hord (q : ℕ) : (q:ℝ)-c-h ≤ (q:ℝ)+1-c+h := by linarith [hh.1]
  have hb := hbound L (by linarith : R ≤ 4*L) D δ hscale p ν r t i
    ((D.q (.inr (.inr ⟨i,0⟩)):ℝ)-c-h) ((D.q (.inr (.inr ⟨i,0⟩)):ℝ)+1-c+h)
    ((D.q (.inr (.inr ⟨i,1⟩)):ℝ)-c-h) ((D.q (.inr (.inr ⟨i,1⟩)):ℝ)+1-c+h)
    ((D.q (.inr (.inr ⟨i,2⟩)):ℝ)-c-h) ((D.q (.inr (.inr ⟨i,2⟩)):ℝ)+1-c+h)
    (hord _) (hord _) (hord _) (fun s hs => ⟨hw0 s hs,hw1 s hs⟩)
  exact hb.trans (cubic_source_rescale_le d γ hCs hCm hL2 hδ.1 (by linarith [hh.2]))

end WaveTurbulence.Sumint
