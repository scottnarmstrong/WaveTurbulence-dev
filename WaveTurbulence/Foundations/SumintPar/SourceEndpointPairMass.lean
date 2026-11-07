/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceMassWindows
public import WaveTurbulence.Foundations.SumintPar.SourceWindowGeometry
public import WaveTurbulence.Foundations.SumintPar.SourcePairFrequencies
public import WaveTurbulence.Foundations.SumintPar.SourceTimeContinuity
public import WaveTurbulence.Foundations.SumintPar.BilinearEndpointStripWindow
public import WaveTurbulence.Foundations.SumintPar.PairBoxIntegral

/-!
# The actual source pair mass on an enlarged endpoint strip

The endpoint is arbitrary. Its two source choices are used later when
pair labels are different. Both the small-region width gain and the
large-region Weyl reserve are retained in the native box measure.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal WithLp

namespace WaveTurbulence.SumintPar

/-- The actual pair mass restricted to a single enlarged endpoint strip. -/
@[expose] noncomputable def endpointPairMass {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (lo hi : D.S.TVar → ℝ) (h e : ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : ℝ≥0∞ :=
  ∫⁻ z in Icc (lo (.inl ⟨a.1,a.2.succ⟩),lo (.inr (.inl a)))
    (hi (.inl ⟨a.1,a.2.succ⟩),hi (.inr (.inl a))),
      if |z.1-e| ≤ 2*h+|z.1-z.2| then ‖pairTimeSum D L γ δ p ν r t a z‖ₑ else 0

/-- The actual endpoint-strip integrand is measurable in both pair times. -/
theorem measurable_endpointPairMass_integrand {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t h e : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) :
    Measurable (fun z : ℝ × ℝ => if |z.1-e| ≤ 2*h+|z.1-z.2| then
      ‖pairTimeSum D L γ δ p ν r t a z‖ₑ else 0) := by
  have hl : Measurable (fun z : ℝ × ℝ => |z.1-e|) := by fun_prop
  have hr : Measurable (fun z : ℝ × ℝ => 2*h+|z.1-z.2|) := by fun_prop
  exact Measurable.ite (measurableSet_le hl hr)
    (continuous_pairTimeSum D hL γ δ p ν r t a).measurable.enorm measurable_const

/-- The physical endpoint-strip estimate for the exact source pair mass. -/
theorem exists_endpointPairMass_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ Cs Cm R : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ A : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h e : ℝ)
        (a : Σ i : Fin D.S.I, Fin (D.S.m i)), h ∈ Icc (0:ℝ) 1 →
      endpointPairMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) h e a ≤
        ENNReal.ofReal ((16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d)*(4*h+2/(16*sourceHalfScale L γ δ)))+
          (1+2*h)*(16*sourceHalfScale L γ δ)⁻¹*Cm*
            (4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by
  let T₀ := 8*(τstar+2)
  have hT₀ : 0 < T₀ := by dsimp [T₀]; positivity
  obtain ⟨Cs,Cm,R,hCs,hCm,hR,hbound⟩ :=
    exists_bilinear_physical_endpoint_strip_window_bound d hd γ hγ η hη T₀ hT₀
  refine ⟨Cs,Cm,R,hCs,hCm,hR,?_⟩
  intro L hL D δ N hδ hτ A hD p ν r t c h e a hh
  have hLp : 0 < L := by linarith [hR.trans hL]
  have hscale : 0 < 16*sourceHalfScale L γ δ := by
    unfold sourceHalfScale
    exact mul_pos (by norm_num) (div_pos (mul_pos hδ.1 (Real.rpow_pos_of_pos hLp _)) (by norm_num))
  have hwin := source_enlarged_window_endpoints (c := c)
    (admissible_time_label_lt D hD (.inl ⟨a.1,a.2.succ⟩)) (admissible_time_label_lt D hD (.inr (.inl a)))
    hLp.le hγ.1.le hδ.1.le hδ.2 hτ hh.1 hh.2
  unfold endpointPairMass
  rw [lintegral_pair_Icc _ (measurable_endpointPairMass_integrand D hLp γ δ p ν r t h e a)]
  simp_rw [pairTimeSum_eq_physical_bilinear]
  have hb := hbound (4*L) (by linarith : R ≤ 4*L)
    ((1/4:ℝ) • toLp 2 (p (D.S.xSlot a.1 a.2))) ((1/4:ℝ) • toLp 2 (p (D.S.ySlot a.1 a.2)))
    (pairOuterFrequencyX D L γ δ ν r t a) (pairOuterFrequencyY D L γ δ ν r t a)
    (continuous_pairOuterFrequencyX D L γ δ ν r t a) (continuous_pairOuterFrequencyY D L γ δ ν r t a)
    (16*sourceHalfScale L γ δ) h
    (enlargedTimeLower D c h (.inr (.inl a))) (enlargedTimeUpper D c h (.inr (.inl a)))
    (enlargedTimeLower D c h (.inl ⟨a.1,a.2.succ⟩)) (enlargedTimeUpper D c h (.inl ⟨a.1,a.2.succ⟩))
    e hscale hh.1 (enlargedTimeLower_le_upper D c hh.1 _) (enlargedTimeLower_le_upper D c hh.1 _) hwin
  exact hb.trans_eq (by congr 1; dsimp [enlargedTimeLower,enlargedTimeUpper]; ring)

end WaveTurbulence.SumintPar
