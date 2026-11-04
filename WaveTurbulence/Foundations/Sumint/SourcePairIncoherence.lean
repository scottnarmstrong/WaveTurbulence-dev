/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceIncoherentPairMass
public import WaveTurbulence.Foundations.Sumint.PairEndpointPower

/-!
# Actual ordered source pair masses with an incoherence gain

The case-(c) gap coefficient is absorbed using a threshold depending on
Dsteps, as permitted by the drafted prefix. The bound is uniform in
all source data, the distinguished times, and the number of pair factors.
It is a comparison bound; the stronger bad-block estimate is retained
separately when the first pair is also bad.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 2: every actual incoherent ordered pair gains beta/2. -/
theorem exists_source_ordered_pair_incoherence_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηsmall : η ≤ 1/3)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β)
    (hβγ : β/2 < 2*γ) (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) :
    ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c : ℝ)
        (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)),
      D.q (.inl ⟨a.1,a.2.succ⟩) ≠ D.q (.inr (.inl a)) →
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c (L^(-β)))
        (enlargedTimeUpper D c (L^(-β))) u a ≤
      ENNReal.ofReal (L^(2*((d:ℝ)-γ)-β/2)) := by
  obtain ⟨Cs,Cm,R,hCs,hCm,hR,hbound⟩ := exists_incoherent_plainPairMass_bound d hd γ hγ η hη τstar hτstar
  intro δ N hδ hτ
  let k := max 1 (((N:ℝ)+2)^(1-3*η))
  have hk : 0 ≤ k := zero_le_one.trans (le_max_left _ _)
  obtain ⟨R',hR',hnum⟩ := exists_pair_endpoint_power_bound d γ η β hβ hβγ hβη Cs Cm k δ hCs hCm hk hδ.1
  refine ⟨max R R',hR.trans (le_max_left _ _),?_⟩
  intro L hL D A hD p ν r t c u a hq
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLR' : R' ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith [hR.trans hLR]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hh : L^(-β) ∈ Icc (0:ℝ) 1 := ⟨Real.rpow_nonneg hLp.le _,
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith only [hβ])⟩
  have hg : pairGapBound D η N a ≤ k := by
    unfold pairGapBound
    split_ifs
    · exact le_max_right _ _
    · exact le_max_left _ _
  have hn := hbound L hLR D δ N hδ hτ A hD p ν r t c (L^(-β)) a hh hq
  calc
    _ ≤ ENNReal.ofReal (pairGapBound D η N a)*plainPairMass D L γ δ p ν r t
        (enlargedTimeLower D c (L^(-β))) (enlargedTimeUpper D c (L^(-β))) a :=
      orderedPairMass_le_gapBound_mul_plain D hD (by linarith only [hηsmall]) δ p ν r t c hh.2 u a
    _ ≤ ENNReal.ofReal k * ENNReal.ofReal
        ((16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d)*(4*L^(-β)+2/(16*sourceHalfScale L γ δ)))+
          (1+2*L^(-β))*(16*sourceHalfScale L γ δ)⁻¹*Cm*
            (4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hg) hn
    _ = ENNReal.ofReal (k*((16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d)*(4*L^(-β)+2/(16*sourceHalfScale L γ δ)))+
          (1+2*L^(-β))*(16*sourceHalfScale L γ δ)⁻¹*Cm*
            (4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η))) := (ENNReal.ofReal_mul hk).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hnum L hLR')

end WaveTurbulence.Sumint
