/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceMassWindows
public import WaveTurbulence.Foundations.SumintPar.SourceWindowGeometry
public import WaveTurbulence.Foundations.SumintPar.SourceNormalFrequencies
public import WaveTurbulence.Foundations.SumintPar.SourceTimeContinuity
public import WaveTurbulence.Foundations.SumintPar.TripleTimeBox
public import WaveTurbulence.Foundations.SumintPar.CubicPhysicalEndpointWindow

/-!
# The exact normal source mass on an enlarged endpoint strip

The native three-time box is converted to the outer-third-time order.
Its inner pair measure is kept intact when applying the physical cubic
strip estimate. Both contributions remain separate and uniform in the
chosen source endpoint.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal WithLp

namespace WaveTurbulence.SumintPar

/-- The actual normal mass restricted to an endpoint strip in its third time. -/
@[expose] noncomputable def endpointNormalMass {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (lo hi : D.S.TVar → ℝ) (h e : ℝ) (i : {i : Fin D.S.I // D.S.nor i = true}) : ℝ≥0∞ :=
  ∫⁻ z in Icc (fun j => lo (.inr (.inr ⟨i,j⟩))) (fun j => hi (.inr (.inr ⟨i,j⟩))),
    if |z 2-e| ≤ 2*h+(|z 0-z 2|+|z 1-z 2|) then ‖normalTimeSum D L γ δ p ν r t i z‖ₑ else 0

/-- The source normal endpoint-strip integrand is measurable in its three native times. -/
theorem measurable_endpointNormalMass_integrand {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t h e : ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) :
    Measurable (fun z : Fin 3 → ℝ => if |z 2-e| ≤ 2*h+(|z 0-z 2|+|z 1-z 2|) then
      ‖normalTimeSum D L γ δ p ν r t i z‖ₑ else 0) := by
  have hl : Measurable (fun z : Fin 3 → ℝ => |z 2-e|) := by fun_prop
  have hr : Measurable (fun z : Fin 3 → ℝ => 2*h+(|z 0-z 2|+|z 1-z 2|)) := by fun_prop
  exact Measurable.ite (measurableSet_le hl hr)
    (continuous_normalTimeSum D hL γ δ p ν r t i).measurable.enorm measurable_const

/-- The physical half-moment/Weyl estimate applies to the literal native normal source mass. -/
theorem exists_endpointNormalMass_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ Cs Cm R : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ A η : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h e : ℝ)
        (i : {i : Fin D.S.I // D.S.nor i = true}), h ∈ Icc (0:ℝ) 1 →
      endpointNormalMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) h e i ≤
        ENNReal.ofReal ((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹ *
          (Cs*(4*L)^(3*d)*(Real.sqrt h+(16*sourceHalfScale L γ δ)^(-(1/2:ℝ)))+
            (1+2*h)*Cm*(4*L)^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log (4*L))) := by
  let T₀ := 8*(τstar+2)
  have hT₀ : 0 < T₀ := by dsimp [T₀]; positivity
  obtain ⟨Cs,Cm,R,hCs,hCm,hR,hbound⟩ := exists_cubic_physical_endpoint_window_bound d hd γ hγ T₀ hT₀
  refine ⟨Cs,Cm,R,hCs,hCm,hR,?_⟩
  intro L hL D δ N hδ hτ A η hD p ν r t c h e i hh
  have hLp : 0 < L := by linarith [hR.trans hL]
  have hscale : 0 < 16*sourceHalfScale L γ δ := by
    unfold sourceHalfScale
    exact mul_pos (by norm_num) (div_pos (mul_pos hδ.1 (Real.rpow_pos_of_pos hLp _)) (by norm_num))
  have hw0 := source_enlarged_window_endpoints (c := c)
    (admissible_time_label_lt D hD (.inr (.inr ⟨i,2⟩))) (admissible_time_label_lt D hD (.inr (.inr ⟨i,0⟩)))
    hLp.le hγ.1.le hδ.1.le hδ.2 hτ hh.1 hh.2
  have hw1 := source_enlarged_window_endpoints (c := c)
    (admissible_time_label_lt D hD (.inr (.inr ⟨i,2⟩))) (admissible_time_label_lt D hD (.inr (.inr ⟨i,1⟩)))
    hLp.le hγ.1.le hδ.1.le hδ.2 hτ hh.1 hh.2
  unfold endpointNormalMass
  rw [lintegral_triple_time_box _ (measurable_endpointNormalMass_integrand D hLp γ δ p ν r t h e i)]
  change (∫⁻ s₂ in Icc (enlargedTimeLower D c h (.inr (.inr ⟨i,2⟩)))
      (enlargedTimeUpper D c h (.inr (.inr ⟨i,2⟩))),
    ∫⁻ s₀ in Icc (enlargedTimeLower D c h (.inr (.inr ⟨i,0⟩)))
      (enlargedTimeUpper D c h (.inr (.inr ⟨i,0⟩))),
    ∫⁻ s₁ in Icc (enlargedTimeLower D c h (.inr (.inr ⟨i,1⟩)))
      (enlargedTimeUpper D c h (.inr (.inr ⟨i,1⟩))),
      if |s₂-e| ≤ 2*h+(|s₀-s₂|+|s₁-s₂|) then
        ‖normalTimeSum D L γ δ p ν r t i ![s₀,s₁,s₂]‖ₑ else 0) ≤ _
  have hp (s₂ : ℝ) : Measurable (fun z : ℝ × ℝ =>
      if |s₂-e| ≤ 2*h+(|z.1-s₂|+|z.2-s₂|) then
        ‖normalTimeSum D L γ δ p ν r t i ![z.1,z.2,s₂]‖ₑ else 0) := by
    have hr : Measurable (fun z : ℝ × ℝ => 2*h+(|z.1-s₂|+|z.2-s₂|)) := by fun_prop
    have hv : Measurable (fun z : ℝ × ℝ => ![z.1,z.2,s₂]) := by fun_prop
    exact Measurable.ite (measurableSet_le (measurable_const (a := |s₂-e|)) hr)
      ((continuous_normalTimeSum D hLp γ δ p ν r t i).measurable.comp hv).enorm measurable_const
  have he (s₂ : ℝ) := lintegral_pair_Icc _ (hp s₂)
    (enlargedTimeLower D c h (.inr (.inr ⟨i,0⟩))) (enlargedTimeUpper D c h (.inr (.inr ⟨i,0⟩)))
    (enlargedTimeLower D c h (.inr (.inr ⟨i,1⟩))) (enlargedTimeUpper D c h (.inr (.inr ⟨i,1⟩)))
  simp_rw [← he]
  have hb := hbound (4*L) (by linarith : R ≤ 4*L) (D.Λsel i.1)
    ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 0))) ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 1)))
    ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 2)))
    (normalOuterFrequency D L γ δ ν r t i 0) (normalOuterFrequency D L γ δ ν r t i 1)
    (normalOuterFrequency D L γ δ ν r t i 2)
    (continuous_normalOuterFrequency D L γ δ ν r t i 0) (continuous_normalOuterFrequency D L γ δ ν r t i 1)
    (continuous_normalOuterFrequency D L γ δ ν r t i 2) (16*sourceHalfScale L γ δ) h
    (enlargedTimeLower D c h (.inr (.inr ⟨i,0⟩))) (enlargedTimeUpper D c h (.inr (.inr ⟨i,0⟩)))
    (enlargedTimeLower D c h (.inr (.inr ⟨i,1⟩))) (enlargedTimeUpper D c h (.inr (.inr ⟨i,1⟩)))
    (enlargedTimeLower D c h (.inr (.inr ⟨i,2⟩))) (enlargedTimeUpper D c h (.inr (.inr ⟨i,2⟩)))
    e (coreTimeSign D i.1 0) (coreTimeSign D i.1 1) (coreTimeSign_eq D i.1 0) (coreTimeSign_eq D i.1 1)
    hscale hh.1 (enlargedTimeLower_le_upper D c hh.1 _) (enlargedTimeLower_le_upper D c hh.1 _)
    (enlargedTimeLower_le_upper D c hh.1 _) (by dsimp [enlargedTimeLower,enlargedTimeUpper]; linarith [hh.2])
    (fun s hs => ⟨hw0 s hs,hw1 s hs⟩)
  apply le_trans ?_ (hb.trans_eq (by congr 1; dsimp [enlargedTimeLower,enlargedTimeUpper]; ring))
  apply le_of_eq
  apply lintegral_congr
  intro s₂
  apply lintegral_congr
  intro z
  congr 1
  exact congrArg (fun w : ℂ => ‖w‖ₑ) (normalTimeSum_eq_physical_cubic D L γ δ p ν r t i ![z.1,z.2,s₂])


end WaveTurbulence.SumintPar
