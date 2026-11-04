/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceBadPairEnvelopes
public import WaveTurbulence.Foundations.Sumint.SourceOrdinaryPairBound

/-!
# Uniform envelopes for all actual source pair masses

All five numerical coefficients are chosen before delta and Dsteps.
The first case-(a)/(c) pair keeps its stronger bad envelope and takes
the minimum with the incoherence comparison when its labels differ.
Every other pair uses ordinary cancellation with the exact indicator.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- The fixed pair envelope used before distinguished-time integration. -/
@[expose] noncomputable def sourcePairEnvelope {d : ℕ} (D : SumintDatum d)
    (L γ δ η β τstar C CsA CmA CsC CmC : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : ℝ≥0∞ :=
  if caseAPair D a then
    min (ENNReal.ofReal (firstPairEnvelope d L γ δ η 1 CsA CmA 1))
      (if pairIncoherent D a then ENNReal.ofReal (L^(2*((d:ℝ)-γ)-β/2)) else ⊤)
  else if caseCPair D a then
    min (ENNReal.ofReal (firstPairEnvelope d L γ δ η (1-3*η) CsC CmC
      ((8*(τstar+2)*4^(2*γ)/(8*δ))^(1-3*η))))
      (if pairIncoherent D a then ENNReal.ofReal (L^(2*((d:ℝ)-γ)-β/2)) else ⊤)
  else ENNReal.ofReal (C*δ⁻¹*L^(2*((d:ℝ)-γ)-(if pairIncoherent D a then β/2 else 0)))

/-- Every actual source pair satisfies its uniform envelope, with all coefficients before delta. -/
theorem exists_source_pair_envelopes (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηsmall : η ≤ 1/3)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β)
    (hβγ : β/2 < 2*γ) (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) :
    ∃ C CsA CmA CsC CmC : ℝ, 1 ≤ C ∧ 0 ≤ CsA ∧ 0 ≤ CmA ∧ 0 ≤ CsC ∧ 0 ≤ CmC ∧
      ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c : ℝ)
        (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)),
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c (L^(-β)))
        (enlargedTimeUpper D c (L^(-β))) u a ≤
      sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC a := by
  obtain ⟨C,hC,hordinary⟩ := exists_source_ordinary_pair_bound d hd γ hγ η hη hηsmall τstar hτstar
    β hβ hβγ hβη
  obtain ⟨CsA,CmA,RA,hCsA,hCmA,hRA,hA⟩ := exists_case_a_firstPairEnvelope d hd γ hγ η hη τstar hτstar
  obtain ⟨CsC,CmC,RC,hCsC,hCmC,hRC,hCpair⟩ := exists_case_c_firstPairEnvelope d hd γ hγ η ⟨hη,hηsmall⟩ τstar hτstar
  refine ⟨C,CsA,CmA,CsC,CmC,hC,hCsA,hCmA,hCsC,hCmC,?_⟩
  intro δ N hδ hτ
  obtain ⟨RO,hRO,hO⟩ := hordinary δ N hδ hτ
  obtain ⟨RI,hRI,hinc⟩ := exists_source_ordered_pair_incoherence_bound d hd γ hγ η hη hηsmall
    τstar hτstar β hβ hβγ hβη δ N hδ hτ
  refine ⟨max RA (max RC (max RO RI)),hRA.trans (le_max_left _ _),?_⟩
  intro L hL D A hD p ν r t c u a
  have hLRA : RA ≤ L := (le_max_left _ _).trans hL
  have hLRC : RC ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLRO : RO ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLRI : RI ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hL1 : 1 ≤ L := by linarith [hRA.trans hLRA]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hh : L^(-β) ∈ Icc (0:ℝ) 1 := ⟨Real.rpow_nonneg hLp.le _,
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith only [hβ])⟩
  have hI : orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c (L^(-β)))
      (enlargedTimeUpper D c (L^(-β))) u a ≤
      (if pairIncoherent D a then ENNReal.ofReal (L^(2*((d:ℝ)-γ)-β/2)) else ⊤) := by
    split_ifs with hq
    · exact hinc L hLRI D A hD p ν r t c u a hq
    · exact le_top
  by_cases ha : caseAPair D a
  · rw [sourcePairEnvelope,ite_eq_left ha]
    exact le_min (hA L hLRA D δ N hδ hτ A hD p ν r t c (L^(-β)) u a hh ha) hI
  · by_cases hc : caseCPair D a
    · rw [sourcePairEnvelope,ite_eq_right ha,ite_eq_left hc]
      exact le_min (hCpair L hLRC D δ N hδ hτ A hD p ν r t c (L^(-β)) u a hh hc) hI
    · rw [sourcePairEnvelope,ite_eq_right ha,ite_eq_right hc]
      exact hO L hLRO D A hD p ν r t c u a ha hc

end WaveTurbulence.Sumint
