/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceLabelWeightPartition
public import WaveTurbulence.Foundations.SumintPar.SourceSummability

/-!
# Absolute source expression summability before label/lattice regrouping

The original phase integral has a common finite absolute bound. The
proved localized lattice mass supplies the full product summability.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.SumintPar

/-- The actual localization-label by lattice-input series is absolutely summable. -/
theorem summable_norm_sourceLabel_expression {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) {A L γ δ η : ℝ} {N : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hD : D.Admissible A L γ η N) (E : Fin 4 → Mom d)
    (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) (t : Fin 3 → ℝ) :
    Summable (fun q : SourceLocalizationLabel D hD × (D.S.VIdx → Fin d → ℤ) =>
      ‖localizedSourceWeight D L q.1.1 q.1.2.val E q.2 *
        (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η q.2 (E 0-E 1) (t 0) τ)‖) := by
  let C := ∫ τ in D.timeDom hI (t 0) (t 1) (t 2), ‖D.phase L γ δ η (fun _ => 0) 0 (t 0) τ‖
  have hmass : (∑' q : SourceLocalizationLabel D hD × (D.S.VIdx → Fin d → ℤ),
      ‖localizedSourceWeight D L q.1.1 q.1.2.val E q.2‖ₑ) < ⊤ := by
    rw [ENNReal.tsum_prod']
    have he := tsum_sourceLocalizationLabel D hD (fun a b =>
      ∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L a b E x‖ₑ)
    exact he.trans_lt (localized_source_weight_mass_lt_top hd D hA hL hD E hE)
  have hs := tsum_enorm_ne_top_iff_summable_norm.mp hmass.ne
  apply (hs.mul_right C).of_nonneg_of_le
  · intro q
    exact norm_nonneg _
  · intro q
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_source_phaseIntegral_le D hI L γ δ η q.2 (E 0-E 1)
      (t 0) (t 1) (t 2)) (norm_nonneg _)

/-- Absolute regrouping of localization labels recovers the exact unlocalized source expression. -/
theorem tsum_sourceLabel_expression {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) {A L γ δ η : ℝ} {N : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hD : D.Admissible A L γ η N) (E : Fin 4 → Mom d)
    (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) (t : Fin 3 → ℝ) :
    (∑' j : SourceLocalizationLabel D hD, ∑' x : D.S.VIdx → Fin d → ℤ,
      localizedSourceWeight D L j.1 j.2.val E x *
        (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x (E 0-E 1) (t 0) τ)) =
      ∑' x : D.S.VIdx → Fin d → ℤ,
        (∏ v, D.wK v (E 0 - E 1) (D.kVec L x E v)*D.wL v (D.ℓVec L x E v)) *
          (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x (E 0-E 1) (t 0) τ) := by
  have hs := (summable_norm_sourceLabel_expression (δ := δ) hd D hI hA hL hD E hE t).of_norm
  rw [← hs.tsum_comm]
  apply tsum_congr
  intro x
  rw [tsum_mul_right,tsum_sourceLabel_weight D hD E hE x]

end WaveTurbulence.SumintPar
