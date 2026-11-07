/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoreTrace
public import WaveTurbulence.Foundations.SumintPar.SelectedMarginalControl

/-!
# Genuine integrability and selected-coordinate support of endpoint inputs

Every selected coordinate retains its actual enlarged source interval.
For at most two coordinates and enlargement at most one, that support
has volume at most nine, as required by the selected Fourier L2 bound.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- The actual endpoint input zero extension is genuinely integrable. -/
theorem integrable_sourceExitInput {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (hη : η ≤ 1/3)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h : ℝ) (upper : Bool) (v : D.S.TVar) :
    Integrable (sourceExitInput D hI L γ δ η p ν r c h upper v) :=
  (integrableOn_sourceExitAmplitude D hI upper v _ (measurable_weightedCutoffInput D hL γ δ η p ν r) c h
    (integrableOn_weightedCutoffInput D hL γ δ η hη p ν r c h)).integrable_indicator
      (measurableSet_localInputTimeDomain D c h)

/-- Leaving any selected native source interval forces the actual endpoint input to vanish. -/
theorem sourceExitInput_eq_zero_of_selected_outside {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h : ℝ) (upper : Bool) (v : D.S.TVar) {k : ℕ} (sel : Fin k → D.S.TVar)
    (u : D.S.TVar → ℝ) (hu : ∃ j, u (sel j) ∉ Icc (enlargedTimeLower D c h (sel j))
      (enlargedTimeUpper D c h (sel j))) :
    sourceExitInput D hI L γ δ η p ν r c h upper v u = 0 := by
  obtain ⟨j,hj⟩ := hu
  apply Set.indicator_of_notMem
  intro hs
  exact hj ⟨hs.1.1 (sel j),hs.1.2 (sel j)⟩

/-- Every selected actual source interval box has volume at most nine for one or two selected times. -/
theorem volume_selected_source_box_le_nine {d : ℕ} (D : SumintDatum d) (c : ℝ) {h : ℝ}
    (hh : h ≤ 1) {k : ℕ} (hk : k ≤ 2) (sel : Fin k → D.S.TVar) :
    volume (Icc (fun j => enlargedTimeLower D c h (sel j))
      (fun j => enlargedTimeUpper D c h (sel j))) ≤ ENNReal.ofReal 9 := by
  rw [Real.volume_Icc_pi]
  calc
    _ ≤ ∏ _j : Fin k, ENNReal.ofReal 3 := by
      apply Finset.prod_le_prod
      intro j _
      apply ENNReal.ofReal_le_ofReal
      dsimp [enlargedTimeLower,enlargedTimeUpper]
      linarith only [hh]
    _ = ENNReal.ofReal ((3:ℝ)^k) := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 3)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      calc
        (3:ℝ)^k ≤ 3^2 := pow_le_pow_right₀ (by norm_num) hk
        _ = 9 := by norm_num)

end WaveTurbulence.SumintPar
