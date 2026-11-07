/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorMasses
public import WaveTurbulence.Foundations.SumintPar.SourceMassWindows
public import WaveTurbulence.Foundations.SumintPar.SourceWindowGeometry
public import WaveTurbulence.Foundations.SumintPar.OrderedPairClasses
public import WaveTurbulence.Foundations.SumintPar.SourceTimeContinuity
public import WaveTurbulence.Foundations.SumintPar.SourceFractionalPairWindow
public import WaveTurbulence.Foundations.SumintPar.PairBoxIntegral

/-!
# The exact case-(c) first-pair mass

The literal exponent 1-3η is kept throughout the native-box integral.
The small-region fractional scale power and the large-region Weyl
reserve remain separate, with constants chosen before δ and Dsteps.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- TARGET sumint case (c): the actual fractional pair mass in its exact nonnegative form. -/
theorem exists_case_c_orderedPairMass_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : η ∈ Ioc (0:ℝ) (1/3))
    (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ Cs Cm R : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ A : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
        (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)), h ∈ Icc (0:ℝ) 1 → caseCPair D a →
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) u a ≤
        ENNReal.ofReal ((1+2*h)*(16*sourceHalfScale L γ δ)⁻¹ *
          ((16*sourceHalfScale L γ δ)^(-(1-3*η))*Cs*(4*L)^(2*d) +
          ((8*(τstar+2))*(4*L)^(2*γ)/(16*sourceHalfScale L γ δ))^(1-3*η) *
            Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η))) := by
  let T₀ := 8*(τstar+2)
  have hT₀ : 0 < T₀ := by dsimp [T₀]; positivity
  obtain ⟨Cs,Cm,R,hCs,hCm,hR,hbound⟩ :=
    exists_source_fractional_pair_window_bound d hd γ hγ η hη.1 T₀ hT₀
  refine ⟨Cs,Cm,R,hCs,hCm,hR,?_⟩
  intro L hL D δ N hδ hτ A hD p ν r t c h u a hh hc
  have hLp : 0 < L := by linarith [hR.trans hL]
  have hscale : 0 < sourceHalfScale L γ δ := by
    unfold sourceHalfScale
    exact div_pos (mul_pos hδ.1 (Real.rpow_pos_of_pos hLp _)) (by norm_num)
  have hρ : 0 ≤ 1-3*η := by linarith [hη.2]
  have hρ1 : 1-3*η ≤ 1 := by linarith [hη.1]
  have hwin := source_enlarged_window_endpoints (c := c)
    (admissible_time_label_lt D hD (.inl ⟨a.1,a.2.succ⟩))
    (admissible_time_label_lt D hD (.inr (.inl a)))
    hLp.le hγ.1.le hδ.1.le hδ.2 hτ hh.1 hh.2
  let F := fun z : ℝ × ℝ => |z.1-z.2|^(1-3*η)*‖pairTimeSum D L γ δ p ν r t a z‖
  have hF : Continuous F := by
    apply Continuous.mul _ (continuous_pairTimeSum D hLp γ δ p ν r t a).norm
    exact (continuous_abs.comp (continuous_fst.sub continuous_snd)).rpow_const (fun _ => Or.inr hρ)
  have hFn (z : ℝ × ℝ) : 0 ≤ F z := mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (norm_nonneg _)
  unfold orderedPairMass
  simp_rw [orderedPairNorm_eq_case_c D L γ δ η p ν r t u a hc]
  have he := ofReal_integral_pair_Icc F hF hFn
    (enlargedTimeLower D c h (.inl ⟨a.1,a.2.succ⟩)) (enlargedTimeUpper D c h (.inl ⟨a.1,a.2.succ⟩))
    (enlargedTimeLower D c h (.inr (.inl a))) (enlargedTimeUpper D c h (.inr (.inl a)))
  rw [← he]
  apply ENNReal.ofReal_le_ofReal
  have hb := hbound L (by linarith : R ≤ 4*L) D δ hscale p ν r t a (1-3*η)
    (enlargedTimeLower D c h (.inr (.inl a))) (enlargedTimeUpper D c h (.inr (.inl a)))
    (enlargedTimeLower D c h (.inl ⟨a.1,a.2.succ⟩)) (enlargedTimeUpper D c h (.inl ⟨a.1,a.2.succ⟩))
    hρ hρ1 (enlargedTimeLower_le_upper D c hh.1 _) (enlargedTimeLower_le_upper D c hh.1 _) hwin
  exact hb.trans_eq (by dsimp [enlargedTimeLower,enlargedTimeUpper,T₀]; ring)

end WaveTurbulence.SumintPar
