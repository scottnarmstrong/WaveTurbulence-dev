/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorMasses
public import WaveTurbulence.Foundations.SumintPar.SourceMassWindows
public import WaveTurbulence.Foundations.SumintPar.SourceWindowGeometry
public import WaveTurbulence.Foundations.SumintPar.SourcePairFrequencies
public import WaveTurbulence.Foundations.SumintPar.OrderedPairClasses
public import WaveTurbulence.Foundations.SumintPar.BadPairPhysicalWindow
public import WaveTurbulence.Foundations.SumintPar.PairBoxIntegral

/-!
# The exact case-(a) first-pair mass

The source ordering strip is retained in the stationary region and
discarded only in the Weyl region. The two powers of the physical time
scale remain separate, so each contribution can use its proper linear
branch. The estimate is uniform in the distinguished middle time.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal WithLp

namespace WaveTurbulence.SumintPar

/-- TARGET sumint case (a): the actual ordered pair mass with both contributions retained. -/
theorem exists_case_a_orderedPairMass_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ Cs Cm R : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ A : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
        (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)), h ∈ Icc (0:ℝ) 1 → caseAPair D a →
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) u a ≤
        ENNReal.ofReal ((16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d)/(16*sourceHalfScale L γ δ))+
          (1+2*h)*(16*sourceHalfScale L γ δ)⁻¹*Cm*
            (4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by
  let T₀ := 8*(τstar+2)
  have hT₀ : 0 < T₀ := by dsimp [T₀]; positivity
  obtain ⟨Cs,Cm,R,hCs,hCm,hR,hbound⟩ :=
    exists_bilinear_physical_ordering_window_bound d hd γ hγ η hη T₀ hT₀
  refine ⟨Cs,Cm,R,hCs,hCm,hR,?_⟩
  intro L hL D δ N hδ hτ A hD p ν r t c h u a hh ha
  have hLp : 0 < L := by linarith [hR.trans hL]
  have hscale : 0 < 16*sourceHalfScale L γ δ := by
    unfold sourceHalfScale
    have hp := Real.rpow_pos_of_pos hLp (2*γ)
    exact mul_pos (by norm_num) (div_pos (mul_pos hδ.1 hp) (by norm_num))
  have hwin := source_enlarged_window_endpoints (c := c)
    (admissible_time_label_lt D hD (.inl ⟨a.1,a.2.succ⟩))
    (admissible_time_label_lt D hD (.inr (.inl a)))
    hLp.le hγ.1.le hδ.1.le hδ.2 hτ hh.1 hh.2
  have hm : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (orderedPairNorm D L γ δ η p ν r t u a z)) :=
    ENNReal.measurable_ofReal.comp ((measurable_orderedPairNorm D hLp γ δ η p ν r t a).comp
      ((measurable_const (a := u)).prodMk measurable_id))
  unfold orderedPairMass
  rw [lintegral_pair_Icc _ hm]
  have hz (z : ℝ × ℝ) : ENNReal.ofReal (orderedPairNorm D L γ δ η p ν r t u a z) =
      if |z.1-u a.1| ≤ |z.1-z.2| then ‖pairTimeSum D L γ δ p ν r t a z‖ₑ else 0 := by
    rw [orderedPairNorm_eq_case_a D L γ δ η p ν r t u a ha]
    split_ifs
    · rw [ofReal_norm]
    · exact ENNReal.ofReal_zero
  simp_rw [hz,pairTimeSum_eq_physical_bilinear]
  have hb := hbound (4*L) (by linarith : R ≤ 4*L)
    ((1/4:ℝ) • toLp 2 (p (D.S.xSlot a.1 a.2))) ((1/4:ℝ) • toLp 2 (p (D.S.ySlot a.1 a.2)))
    (pairOuterFrequencyX D L γ δ ν r t a) (pairOuterFrequencyY D L γ δ ν r t a)
    (continuous_pairOuterFrequencyX D L γ δ ν r t a) (continuous_pairOuterFrequencyY D L γ δ ν r t a)
    (16*sourceHalfScale L γ δ)
    (enlargedTimeLower D c h (.inr (.inl a))) (enlargedTimeUpper D c h (.inr (.inl a)))
    (enlargedTimeLower D c h (.inl ⟨a.1,a.2.succ⟩)) (enlargedTimeUpper D c h (.inl ⟨a.1,a.2.succ⟩))
    (u a.1) hscale (enlargedTimeLower_le_upper D c hh.1 _) (enlargedTimeLower_le_upper D c hh.1 _) hwin
  exact hb.trans_eq (by congr 1; dsimp [enlargedTimeLower,enlargedTimeUpper]; ring)

end WaveTurbulence.SumintPar
