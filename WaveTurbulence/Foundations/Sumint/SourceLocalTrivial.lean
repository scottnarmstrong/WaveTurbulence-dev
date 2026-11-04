/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceFactorTrivial
public import WaveTurbulence.Foundations.Sumint.SourceCoreNormFactor
public import WaveTurbulence.Foundations.Sumint.PairMassDomination

/-!
# Uniform local source factor bounds on the actual enlarged windows

These counting estimates hold even when every local time is fixed. The
only nonunit gap amplitude is bounded by its physical source window.
-/

public section
open MeasureTheory Set
open scoped Classical
namespace WaveTurbulence.Sumint

/-- A local oscillatory factor has its uniform lattice counting bound. -/
theorem plainTimeNormFactor_le_count {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : FactorIdx D.S) (z : FactorCoordinate D.S a → ℝ) :
    plainTimeNormFactor D L γ δ p ν r t a z ≤ (8*L+1)^(d*factorArity D.S a) := by
  let u := (timeCoordinateGrouping D.S).symm (Pi.single a z)
  have he : timeCoordinateGrouping D.S u a = z := by
    simp [u]
  have hh := norm_tsum_sourceFactorTerm_le D hL γ δ p ν r t u a
  rw [norm_tsum_sourceFactorTerm_eq_plainTimeNormFactor,he] at hh
  exact hh

/-- The only possible nonunit physical gap is uniformly bounded by a fixed positive source constant. -/
theorem timeGapFactor_le_window {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hη : 0 ≤ 1-3*η)
    (c : ℝ) {h : ℝ} (hh : h ≤ 1) (a : FactorIdx D.S) (z : FactorCoordinate D.S a → ℝ)
    (hz : ∀ j, z j ∈ Icc (enlargedTimeLower D c h (factorCoordinateTime D.S ⟨a,j⟩))
      (enlargedTimeUpper D c h (factorCoordinateTime D.S ⟨a,j⟩))) :
    timeGapFactor D η a z ≤ max 1 (((N:ℝ)+2)^(1-3*η)) := by
  rcases a with i | (a | i)
  · exact le_max_left _ _
  · have hb := pairGapAmplitude_le_bound D hD hη c hh a (z 0,z 1)
      ⟨⟨(hz 0).1,(hz 1).1⟩,⟨(hz 0).2,(hz 1).2⟩⟩
    apply hb.trans
    unfold pairGapBound
    split_ifs
    · exact le_max_right _ _
    · exact le_max_left _ _
  · exact le_max_left _ _

/-- Every actual local factor has its physical gap constant times the exact input-count power. -/
theorem sourceTimeNormFactor_le_window_count {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hL : 0 < L) (hη : 0 ≤ 1-3*η)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c : ℝ)
    {h : ℝ} (hh : h ≤ 1) (a : FactorIdx D.S) (z : FactorCoordinate D.S a → ℝ)
    (hz : ∀ j, z j ∈ Icc (enlargedTimeLower D c h (factorCoordinateTime D.S ⟨a,j⟩))
      (enlargedTimeUpper D c h (factorCoordinateTime D.S ⟨a,j⟩))) :
    sourceTimeNormFactor D L γ δ η p ν r t a z ≤
      max 1 (((N:ℝ)+2)^(1-3*η))*(8*L+1)^(d*factorArity D.S a) := by
  apply mul_le_mul (timeGapFactor_le_window D hD hη c hh a z hz)
    (plainTimeNormFactor_le_count D hL γ δ p ν r t a z)
    (by unfold plainTimeNormFactor; split <;> exact norm_nonneg _)
    (le_trans zero_le_one (le_max_left _ _))

end WaveTurbulence.Sumint
