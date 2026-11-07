/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceLinearMass
public import WaveTurbulence.Foundations.SumintPar.SourceIncoherentNormalMass
public import WaveTurbulence.Foundations.SumintPar.CubicEndpointPower

/-!
# The actual low-gamma normal block gains beta/20 on an incoherent cell

The enlarged width is L to the minus beta. A discrepant time label
forces the normal endpoint strip; its half-moment estimate is paired
with the actual distinguished linear mass. The threshold is independent
of the datum and the number of normal blocks.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- TARGET sumint Step 2: the actual low-gamma incoherent normal block has a beta/20 gain. -/
theorem exists_low_gamma_source_normal_incoherence_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioc (0:ℝ) (1/2)) (τstar : ℝ) (hτstar : 0 < τstar)
    (β : ℝ) (hβ : 0 < β) (hβγ : β < 20*γ) :
    ∀ δ : ℝ, δ ∈ Ioc (0:ℝ) 1 → ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (N : ℕ), τstar = (N:ℝ)*δ →
      ∀ A η : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c : ℝ)
        (i : {i : Fin D.S.I // D.S.nor i = true}),
      ¬ (D.q (.inr (.inr ⟨i,0⟩)) = D.q (.inr (.inr ⟨i,1⟩)) ∧
        D.q (.inr (.inr ⟨i,1⟩)) = D.q (.inr (.inr ⟨i,2⟩))) →
      linearFactorMass D L γ δ p ν r t c (L^(-β)) i.1 *
        normalFactorMass D L γ δ p ν r t (enlargedTimeLower D c (L^(-β)))
          (enlargedTimeUpper D c (L^(-β))) i ≤
      ENNReal.ofReal (L^(4*((d:ℝ)-γ)-β/20)) := by
  obtain ⟨Cs,Cm,R,hCs,hCm,hR,hbound⟩ := exists_incoherent_normalFactorMass_bound d hd γ
    ⟨hγ.1,by linarith [hγ.2]⟩ τstar hτstar
  intro δ hδ
  obtain ⟨R',hR',hnum⟩ := exists_low_gamma_cubic_endpoint_power_bound d hγ β hβ hβγ
    Cs Cm (3*(12:ℝ)^d) δ hCs hCm (by positivity) hδ.1
  refine ⟨max R R',hR.trans (le_max_left _ _),?_⟩
  intro L hL D N hτ A η hD p ν r t c i hq
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLR' : R' ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith [hR.trans hLR]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hh : L^(-β) ∈ Icc (0:ℝ) 1 :=
    ⟨Real.rpow_nonneg hLp.le _,Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith only [hβ])⟩
  have hl := linearFactorMass_le_trivial D hL1 hδ.1 γ p ν r t c hh i.1
  have hn := hbound L hLR D δ N hδ hτ A η hD p ν r t c (L^(-β)) i hh hq
  calc
    _ ≤ ENNReal.ofReal (3*(12:ℝ)^d*L^(d:ℝ))*
        ENNReal.ofReal ((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹ *
          (Cs*(4*L)^(3*d)*(Real.sqrt (L^(-β))+(16*sourceHalfScale L γ δ)^(-(1/2:ℝ)))+
            (1+2*L^(-β))*Cm*(4*L)^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log (4*L))) := mul_le_mul' hl hn
    _ = ENNReal.ofReal ((3*(12:ℝ)^d)*L^(d:ℝ)*
        ((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹ *
          (Cs*(4*L)^(3*d)*(Real.sqrt (L^(-β))+(16*sourceHalfScale L γ δ)^(-(1/2:ℝ)))+
            (1+2*L^(-β))*Cm*(4*L)^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log (4*L)))) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 3*(12:ℝ)^d*L^(d:ℝ))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hnum L hLR')

end WaveTurbulence.SumintPar
