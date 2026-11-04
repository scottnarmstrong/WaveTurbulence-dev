/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceOrdinaryMassBounds
public import WaveTurbulence.Foundations.Sumint.SourcePairIncoherence

/-!
# Ordinary source pair masses with their exact discrepancy indicator

The constant is chosen before delta and Dsteps. Pairs outside the first
case-(a)/(c) positions use ordinary cancellation; discrepant labels also
retain beta/2. The same threshold works for every pair and distinguished
time vector in the source datum.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- The literal source pair-label discrepancy counted in M₀. -/
@[expose] def pairIncoherent {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : Prop :=
  D.q (.inl ⟨a.1,a.2.succ⟩) ≠ D.q (.inr (.inl a))

/-- TARGET sumint Step 2: ordinary actual ordered pair masses retain their incoherence count. -/
theorem exists_source_ordinary_pair_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηsmall : η ≤ 1/3)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β)
    (hβγ : β/2 < 2*γ) (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c : ℝ)
        (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)),
      ¬ caseAPair D a → ¬ caseCPair D a →
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c (L^(-β)))
        (enlargedTimeUpper D c (L^(-β))) u a ≤
      ENNReal.ofReal (C*δ⁻¹*L^(2*((d:ℝ)-γ)-(if pairIncoherent D a then β/2 else 0))) := by
  have hηweyl : η ≤ 2*((d:ℝ)-1)*(1-γ) := by linarith only [hβ,hβη]
  obtain ⟨C,R,hC,hR,hbound⟩ := exists_ordinary_orderedPairMass_bound d hd γ hγ η hη hηweyl τstar hτstar
  refine ⟨C,hC,?_⟩
  intro δ N hδ hτ
  obtain ⟨R',hR',hinc⟩ := exists_source_ordered_pair_incoherence_bound d hd γ hγ η hη hηsmall
    τstar hτstar β hβ hβγ hβη δ N hδ hτ
  refine ⟨max R R',hR.trans (le_max_left _ _),?_⟩
  intro L hL D A hD p ν r t c u a hna hnc
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLR' : R' ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith [hR.trans hLR]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  by_cases hq : pairIncoherent D a
  · rw [ite_eq_left hq]
    apply (hinc L hLR' D A hD p ν r t c u a hq).trans
    apply ENNReal.ofReal_le_ofReal
    have hδinv : 1 ≤ δ⁻¹ := by rw [← one_div,le_div_iff₀ hδ.1]; simpa using hδ.2
    have hcoeff : 1 ≤ C*δ⁻¹ := by nlinarith only [hC,hδinv]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff
      (Real.rpow_nonneg hLp.le (2*((d:ℝ)-γ)-β/2))
  · rw [ite_eq_right hq,sub_zero]
    exact hbound L hLR D δ N hδ hτ A hD p ν r t c (L^(-β)) u a
      ⟨Real.rpow_nonneg hLp.le _,Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith only [hβ])⟩ hna hnc

end WaveTurbulence.Sumint
