/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFirstPairEnvelope
public import WaveTurbulence.Foundations.SumintPar.SourceCaseAMass
public import WaveTurbulence.Foundations.SumintPar.SourceCaseCMass

/-!
# The actual first bad pairs satisfy fixed-coefficient envelopes

The enlarged interval length is at most three. In case (c) the ratio
of the physical Weyl window to the source time scale is independent
of L. Thus both literal ordered masses fit the envelope already paired
with the actual distinguished linear mass.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- The actual case-(a) first pair satisfies the stationary/Weyl envelope with p=1. -/
theorem exists_case_a_firstPairEnvelope (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ Cs Cm R : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ A : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
        (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)), h ∈ Icc (0:ℝ) 1 → caseAPair D a →
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) u a ≤
        ENNReal.ofReal (firstPairEnvelope d L γ δ η 1 Cs Cm 1) := by
  obtain ⟨Cs,Cm,R,hCs,hCm,hR,hbound⟩ := exists_case_a_orderedPairMass_bound d hd γ hγ η hη τstar hτstar
  refine ⟨Cs,3*Cm,R,hCs,mul_nonneg (by norm_num) hCm,hR,?_⟩
  intro L hL D δ N hδ hτ A hD p ν r t c h u a hh ha
  apply (hbound L hL D δ N hδ hτ A hD p ν r t c h u a hh ha).trans
  apply ENNReal.ofReal_le_ofReal
  have hLp : 0 < L := by linarith [hR.trans hL]
  have hδp : 0 < δ := hδ.1
  have hc : 0 < 16*sourceHalfScale L γ δ := by unfold sourceHalfScale; positivity
  have hm0 : 0 ≤ (16*sourceHalfScale L γ δ)⁻¹*Cm*
      (4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η) := by positivity
  have hlen : 1+2*h ≤ 3 := by linarith [hh.2]
  calc
    _ = (16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d)/(16*sourceHalfScale L γ δ))+
        (1+2*h)*((16*sourceHalfScale L γ δ)⁻¹*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by ring
    _ ≤ (16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d)/(16*sourceHalfScale L γ δ))+
        3*((16*sourceHalfScale L γ δ)⁻¹*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hlen hm0)
    _ = _ := by unfold firstPairEnvelope; rw [Real.rpow_neg_one,div_eq_mul_inv]; ring

/-- The actual case-(c) first pair satisfies an envelope whose coefficient is fixed as L varies. -/
theorem exists_case_c_firstPairEnvelope (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : η ∈ Ioc (0:ℝ) (1/3))
    (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ Cs Cm R : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ A : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
        (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)), h ∈ Icc (0:ℝ) 1 → caseCPair D a →
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) u a ≤
        ENNReal.ofReal (firstPairEnvelope d L γ δ η (1-3*η) Cs Cm
          ((8*(τstar+2)*4^(2*γ)/(8*δ))^(1-3*η))) := by
  obtain ⟨Cs,Cm,R,hCs,hCm,hR,hbound⟩ := exists_case_c_orderedPairMass_bound d hd γ hγ η hη τstar hτstar
  refine ⟨3*Cs,3*Cm,R,mul_nonneg (by norm_num) hCs,mul_nonneg (by norm_num) hCm,hR,?_⟩
  intro L hL D δ N hδ hτ A hD p ν r t c h u a hh ha
  apply (hbound L hL D δ N hδ hτ A hD p ν r t c h u a hh ha).trans
  apply ENNReal.ofReal_le_ofReal
  have hLp : 0 < L := by linarith [hR.trans hL]
  have hδp : 0 < δ := hδ.1
  have hc : 0 < 16*sourceHalfScale L γ δ := by unfold sourceHalfScale; positivity
  rw [source_fractional_window_ratio hLp hδp]
  have hlen : 1+2*h ≤ 3 := by linarith [hh.2]
  have hm0 : 0 ≤ (16*sourceHalfScale L γ δ)⁻¹*
      ((16*sourceHalfScale L γ δ)^(-(1-3*η))*Cs*(4*L)^(2*d)+
        (8*(τstar+2)*4^(2*γ)/(8*δ))^(1-3*η)*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by positivity
  calc
    _ = (1+2*h)*((16*sourceHalfScale L γ δ)⁻¹*
        ((16*sourceHalfScale L γ δ)^(-(1-3*η))*Cs*(4*L)^(2*d)+
        (8*(τstar+2)*4^(2*γ)/(8*δ))^(1-3*η)*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η))) := by ring
    _ ≤ 3*((16*sourceHalfScale L γ δ)⁻¹*
        ((16*sourceHalfScale L γ δ)^(-(1-3*η))*Cs*(4*L)^(2*d)+
        (8*(τstar+2)*4^(2*γ)/(8*δ))^(1-3*η)*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η))) :=
      mul_le_mul_of_nonneg_right hlen hm0
    _ = _ := by unfold firstPairEnvelope; ring

end WaveTurbulence.SumintPar
