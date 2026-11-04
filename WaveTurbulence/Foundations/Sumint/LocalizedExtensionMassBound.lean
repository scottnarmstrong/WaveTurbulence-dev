/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.LocalizedExtensionRegularity
public import WaveTurbulence.Foundations.Sumint.PhaseCellMassBound

/-!
# Absolute time mass under countable spatial localization

The constant is common to all localization labels and cutoff centers.
This coarse bound is used only to justify countable Fubini; the norm
estimate continues to use normalized spatial Fourier coefficient mass.
-/

public section
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Sumint

/-- Every actual localized extension has a common time-mass factor times its localized lattice weight mass. -/
theorem exists_localizedSourceExtension_mass_bound {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ)
      (E : Fin 4 → Mom d),
      (∫⁻ t, ‖localizedSourceExtension D hI N h L γ δ η a b p E t‖ₑ) ≤
        ENNReal.ofReal (‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card*C)*
          ∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L a b E x‖ₑ := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_phaseCellExtension_mass_bound D hI N h L γ δ η hη
  refine ⟨C,hC,?_⟩
  intro a b p E
  let R : ℝ := ‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card
  have hR : 0 ≤ R := by positivity
  have hQ (x : D.S.VIdx → Fin d → ℤ) :
      ‖((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (inputCutoff_product_bounds p (fun v => latticePoint L (x v))).1]
    exact (ENNReal.ofReal_le_ofReal (inputCutoff_product_bounds p (fun v => latticePoint L (x v))).2).trans_eq ENNReal.ofReal_one
  have hm (x : D.S.VIdx → Fin d → ℤ) :
      (∫⁻ t, ‖phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t‖ₑ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm
      (integrable_phaseCellExtension D hI N h L γ δ η hη x (E 0-E 1))]
    exact ENNReal.ofReal_le_ofReal (hbound x (E 0-E 1))
  have hpoint (t : Fin 3 → ℝ) : ‖localizedSourceExtension D hI N h L γ δ η a b p E t‖ₑ ≤
      ENNReal.ofReal R * ∑ x ∈ inputCutoffBox L p,
        ‖localizedSourceWeight D L a b E x‖ₑ*‖phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t‖ₑ := by
    rw [localizedSourceExtension_eq_sum hd D hI N h hL hη hD a b p E t,enorm_mul,
      ← ofReal_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR]
    apply mul_le_mul' le_rfl
    apply (enorm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x _
    rw [enorm_mul,enorm_mul]
    exact mul_le_mul' ((mul_le_mul' (hQ x) le_rfl).trans_eq (one_mul _)) le_rfl
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal R * ∑ x ∈ inputCutoffBox L p,
        ‖localizedSourceWeight D L a b E x‖ₑ*‖phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t‖ₑ :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal R * ∑ x ∈ inputCutoffBox L p,
        ‖localizedSourceWeight D L a b E x‖ₑ *
          (∫⁻ t, ‖phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t‖ₑ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro x _
        exact lintegral_const_mul' _ _ enorm_ne_top
      · intro x _
        exact measurable_const.mul (measurable_phaseCellExtension D hI N h L γ δ η x (E 0-E 1)).enorm
    _ ≤ ENNReal.ofReal R * ∑ x ∈ inputCutoffBox L p,
        ‖localizedSourceWeight D L a b E x‖ₑ*ENNReal.ofReal C := by
      apply mul_le_mul' le_rfl
      exact Finset.sum_le_sum (fun x _ => mul_le_mul' le_rfl (hm x))
    _ = ENNReal.ofReal (R*C)*∑ x ∈ inputCutoffBox L p, ‖localizedSourceWeight D L a b E x‖ₑ := by
      rw [← Finset.sum_mul,ENNReal.ofReal_mul hR]
      ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl (ENNReal.sum_le_tsum _)

end WaveTurbulence.Sumint
