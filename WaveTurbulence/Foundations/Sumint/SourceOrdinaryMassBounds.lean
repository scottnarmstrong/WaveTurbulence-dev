/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceFactorMasses
public import WaveTurbulence.Foundations.Sumint.SourceMassWindows
public import WaveTurbulence.Foundations.Sumint.SourceNormalizedPair
public import WaveTurbulence.Foundations.Sumint.SourceNormalizedNormal
public import WaveTurbulence.Foundations.Sumint.SourceTimeContinuity
public import WaveTurbulence.Foundations.Sumint.PairBoxIntegral
public import WaveTurbulence.Foundations.Sumint.TripleTimeBox

/-!
# Ordinary numerical bounds for the exact source factor masses

The real window estimates are transferred to the native nonnegative
masses appearing in the source reduction. Every time label range is
extracted from the actual admissible datum. Constants precede δ and
Dsteps, matching the drafted prefix.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Every pair outside the first case-(a)/(c) positions has the ordinary source mass bound. -/
theorem exists_ordinary_orderedPairMass_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηγ : η ≤ 2*((d:ℝ)-1)*(1-γ)) (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ C R : ℝ, 1 ≤ C ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ A : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
        (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)), h ∈ Icc (0:ℝ) 1 →
      ¬ caseAPair D a → ¬ (D.S.nor a.1 = false ∧ D.badKind a.1 = 2 ∧ (a.2:ℕ) = 0) →
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) u a ≤
        ENNReal.ofReal (C*δ⁻¹*L^(2*((d:ℝ)-γ))) := by
  obtain ⟨C,R,hC,hR,hbound⟩ := exists_source_normalized_pair_bound d hd γ hγ η hη hηγ τstar hτstar
  refine ⟨C,R,hC,hR,?_⟩
  intro L hL D δ N hδ hτ A hD p ν r t c h u a hh hna hnc
  have hLp : 0 < L := by linarith [hR.trans hL]
  have hz (z : ℝ × ℝ) : orderedPairNorm D L γ δ η p ν r t u a z =
      ‖pairTimeSum D L γ δ p ν r t a z‖ := by
    unfold orderedPairNorm
    rw [ite_eq_right hna]
    unfold pairGapAmplitude
    rw [ite_eq_right hnc,one_mul]
  unfold orderedPairMass
  simp_rw [hz]
  have he := ofReal_integral_pair_Icc (fun z => ‖pairTimeSum D L γ δ p ν r t a z‖)
    (continuous_pairTimeSum D hLp γ δ p ν r t a).norm (fun _ => norm_nonneg _)
    (enlargedTimeLower D c h (.inl ⟨a.1,a.2.succ⟩))
    (enlargedTimeUpper D c h (.inl ⟨a.1,a.2.succ⟩))
    (enlargedTimeLower D c h (.inr (.inl a))) (enlargedTimeUpper D c h (.inr (.inl a)))
  rw [← he]
  exact ENNReal.ofReal_le_ofReal (hbound L hL D δ N hδ hτ p ν r t c h a hh
    (admissible_time_label_lt D hD _) (admissible_time_label_lt D hD _))

/-- The exact normal mass retains both normalized contributions, with constants chosen before δ. -/
theorem exists_normalFactorMass_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ C R : ℝ, 1 ≤ C ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ A η : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
        (i : {i : Fin D.S.I // D.S.nor i = true}), h ∈ Icc (0:ℝ) 1 →
      normalFactorMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) i ≤
        ENNReal.ofReal (C*δ^(-2:ℝ)*(L^(3*(d:ℝ)-4*γ)+
          L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L)) := by
  obtain ⟨C,R,hC,hR,hbound⟩ := exists_source_normalized_normal_bound d hd γ hγ τstar hτstar
  refine ⟨C,R,hC,hR,?_⟩
  intro L hL D δ N hδ hτ A η hD p ν r t c h i hh
  have hLp : 0 < L := by linarith [hR.trans hL]
  unfold normalFactorMass
  have he := ofReal_integral_triple_time_box (fun z => ‖normalTimeSum D L γ δ p ν r t i z‖)
    (continuous_normalTimeSum D hLp γ δ p ν r t i).norm (fun _ => norm_nonneg _)
    (fun j => enlargedTimeLower D c h (.inr (.inr ⟨i,j⟩)))
    (fun j => enlargedTimeUpper D c h (.inr (.inr ⟨i,j⟩)))
  rw [← he]
  exact ENNReal.ofReal_le_ofReal (hbound L hL D δ N hδ hτ p ν r t c h i hh
    (admissible_time_label_lt D hD _) (admissible_time_label_lt D hD _) (admissible_time_label_lt D hD _))

end WaveTurbulence.Sumint
