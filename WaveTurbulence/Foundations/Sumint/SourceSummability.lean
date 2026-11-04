/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.NormPartitionIdentity
public import WaveTurbulence.Foundations.Sumint.LocalizedLatticeMass

/-!
# Genuine absolute convergence of the original source lattice sum

The nonnegative cell partition, summed Fourier coefficient mass and fixed
cutoff support count prove absolute convergence before any oscillatory
estimate. The source time integrals have a common absolute bound because
the modulus of the phase is independent of the lattice and output momentum.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- The actual unlocalized source weight product has finite absolute lattice mass. -/
theorem source_weight_mass_lt_top {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hD : D.Admissible A L γ η Dsteps) (E : Fin 4 → Mom d)
    (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) :
    (∑' x : D.S.VIdx → Fin d → ℤ,
      ‖∏ v, D.wK v (D.kVec L x E v)*D.wL v (D.ℓVec L x E v)‖ₑ) < ⊤ := by
  calc
    _ = ∑' x : D.S.VIdx → Fin d → ℤ, ∑' a : D.S.VIdx → Fin d → ℤ,
        ∑ b ∈ sourceAlternativeLabels D hD a, ‖localizedSourceWeight D L a b E x‖ₑ := by
      apply tsum_congr
      intro x
      exact source_weight_enorm_partition D hD E hE x
    _ = ∑' a : D.S.VIdx → Fin d → ℤ, ∑ b ∈ sourceAlternativeLabels D hD a,
        ∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L a b E x‖ₑ := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro a
      exact tsum_finsetSum_ennreal _ _
    _ < ⊤ := localized_source_weight_mass_lt_top hd D hA hL hD E hE

/-- Absolute summability of the original source spatial weights. -/
theorem summable_norm_source_weight {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hD : D.Admissible A L γ η Dsteps) (E : Fin 4 → Mom d)
    (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) :
    Summable (fun x : D.S.VIdx → Fin d → ℤ =>
      ‖∏ v, D.wK v (D.kVec L x E v)*D.wL v (D.ℓVec L x E v)‖) :=
  tsum_enorm_ne_top_iff_summable_norm.mp (source_weight_mass_lt_top hd D hA hL hD E hE).ne

/-- The source phase is actually integrable on its original time polytope. -/
theorem integrableOn_phase_timeDom {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (hη : η ≤ 1/3) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d)
    (t t' t'' : ℝ) : IntegrableOn (D.phase L γ δ η x r t) (D.timeDom hI t t' t'') := by
  have hn : IntegrableOn (fun τ => ‖D.phase L γ δ η x r t τ‖) (inputTimeBox D) :=
    (continuous_norm_phase D L γ δ η hη x r t).integrableOn_Icc
  have hi : IntegrableOn (D.phase L γ δ η x r t) (inputTimeBox D) :=
    hn.mono' (measurable_phase D L γ δ η x r t).aestronglyMeasurable.restrict
      (ae_of_all _ (fun _ => le_rfl))
  exact hi.mono_set (timeDom_subset_inputTimeBox D hI t t' t'')

/-- A common finite absolute phase-integral bound, independent of every lattice input. -/
theorem norm_source_phaseIntegral_le {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t t' t'' : ℝ) :
    ‖∫ τ in D.timeDom hI t t' t'', D.phase L γ δ η x r t τ‖ ≤
      ∫ τ in D.timeDom hI t t' t'', ‖D.phase L γ δ η (fun _ => 0) 0 t τ‖ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  simp_rw [norm_phase]

/-- The lattice series in the exact draft expression is genuinely absolutely convergent. -/
theorem summable_source_expression_terms {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) {A L γ δ η : ℝ} {Dsteps : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hD : D.Admissible A L γ η Dsteps) (E : Fin 4 → Mom d)
    (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) (t t' t'' : ℝ) :
    Summable (fun x : D.S.VIdx → Fin d → ℤ =>
      (∏ v, D.wK v (D.kVec L x E v)*D.wL v (D.ℓVec L x E v)) *
        ∫ τ in D.timeDom hI t t' t'', D.phase L γ δ η x (E 0-E 1) t τ) := by
  let B := ∫ τ in D.timeDom hI t t' t'', ‖D.phase L γ δ η (fun _ => 0) 0 t τ‖
  apply ((summable_norm_source_weight hd D hA hL hD E hE).mul_right B).of_norm_bounded
  intro x
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_source_phaseIntegral_le D hI L γ δ η x (E 0-E 1) t t' t'')
    (norm_nonneg _)

end WaveTurbulence.Sumint
