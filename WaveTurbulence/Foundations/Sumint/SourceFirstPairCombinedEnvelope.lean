/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourcePairEnvelopes
public import WaveTurbulence.Foundations.Sumint.SourceBadLinearBounds
public import WaveTurbulence.Foundations.Sumint.FirstPairMinimum

/-!
# Actual distinguished masses times the uniform bad first-pair envelopes

Both the bad gain and the exact first-pair discrepancy indicator survive.
The uniform envelopes are inserted before integration, so this bound
applies directly to the block product of the actual static reduction.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- A first bad pair's uniform envelope retains the bad and incoherent gains together. -/
theorem exists_source_first_pair_combined_envelope_bound (d : ℕ) (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Ioo (0:ℝ) 1) (hη : η ≤ gammaBase γ) (hηsmall : η ≤ 1/24)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 ≤ β)
    (C CsA CmA CsC CmC δ : ℝ) (hCsA : 0 ≤ CsA) (hCmA : 0 ≤ CmA)
    (hCsC : 0 ≤ CsC) (hCmC : 0 ≤ CmC) (hδ : δ ∈ Ioc (0:ℝ) (1/16)) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d), γ+η ≤ 1 →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c : ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)), caseAPair D a ∨ caseCPair D a →
      linearFactorMass D L γ δ p ν r t c (L^(-β)) a.1 *
        sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC a ≤
      ENNReal.ofReal (L^(3*((d:ℝ)-γ)-gammaBase γ/4-(if pairIncoherent D a then β/20 else 0))) := by
  obtain ⟨RA,hRA,hA⟩ := exists_source_first_pair_envelope_linear_bound d hd hγ hη
    (by norm_num : (7/8:ℝ) ≤ 1) δ CsA CmA 1 hδ.1 hδ.2 hCsA hCmA (by norm_num)
  let K := (8*(τstar+2)*4^(2*γ)/(8*δ))^(1-3*η)
  have hδp : 0 < δ := hδ.1
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  obtain ⟨RC,hRC,hCpair⟩ := exists_source_first_pair_envelope_linear_bound d hd hγ hη
    (by linarith only [hηsmall] : (7/8:ℝ) ≤ 1-3*η) δ CsC CmC K hδ.1 hδ.2 hCsC hCmC hK
  obtain ⟨RD,hRD,hDlinear⟩ := exists_source_case_d_linear_bound d hγ δ hδ.1 hδ.2
  refine ⟨max RA (max RC RD),hRA.trans (le_max_left _ _),?_⟩
  intro L hL D hγη p ν r hr hrupper t c a ha
  have hLRA : RA ≤ L := (le_max_left _ _).trans hL
  have hLRC : RC ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLRD : RD ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : 1 ≤ L := by linarith [hRA.trans hLRA]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hh : L^(-β) ∈ Icc (0:ℝ) 1 := ⟨Real.rpow_nonneg hLp.le _,
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (neg_nonpos.mpr hβ)⟩
  let F := linearFactorMass D L γ δ p ν r t c (L^(-β)) a.1
  have hlinear : F ≤ ENNReal.ofReal (L^((d:ℝ)-γ+3*gammaBase γ/2)) :=
    hDlinear L hLRD D η hγη p ν r hr hrupper t c (L^(-β)) a.1 hh
  have hcombine (E : ℝ≥0∞) (he : F*E ≤ ENNReal.ofReal (L^(3*((d:ℝ)-γ)-gammaBase γ/2))) :
      F*min E (if pairIncoherent D a then ENNReal.ofReal (L^(2*((d:ℝ)-γ)-β/2)) else ⊤) ≤
      ENNReal.ofReal (L^(3*((d:ℝ)-γ)-gammaBase γ/4-(if pairIncoherent D a then β/20 else 0))) := by
    by_cases hq : pairIncoherent D a
    · rw [ite_eq_left hq,ite_eq_left hq]
      exact first_pair_minimum_bound d hL1 hγ he hlinear
    · rw [ite_eq_right hq,ite_eq_right hq,min_eq_left le_top,sub_zero]
      apply he.trans
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow_of_exponent_le hL1
      linarith only [gammaBase_pos hγ]
  rcases ha with ha | hc
  · rw [sourcePairEnvelope,ite_eq_left ha]
    exact hcombine _ (hA L hLRA D hγη p ν r hr hrupper t c (L^(-β)) a.1 hh)
  · have hna := not_caseAPair_of_caseCPair D a hc
    rw [sourcePairEnvelope,ite_eq_right hna,ite_eq_left hc]
    exact hcombine _ (hCpair L hLRC D hγη p ν r hr hrupper t c (L^(-β)) a.1 hh)

end WaveTurbulence.Sumint
