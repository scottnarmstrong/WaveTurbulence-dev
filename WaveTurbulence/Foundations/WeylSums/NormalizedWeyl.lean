/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicStarScalar
public import WaveTurbulence.Foundations.WeylSums.WeylSupremumArcs

/-! # The normalized Weyl majorant and its zero-arc decomposition -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- Squared Weyl supremum with its trivial scale factored out. -/
@[expose] noncomputable def normalizedWeyl (M t : ℝ) : ℝ := weylSupremum M t^2/M

/-- The part supported away from the zero rational arc. -/
@[expose] noncomputable def nonzeroWeylPart (M : ℝ) : ℝ → ℝ :=
  {t : ℝ | 1/M < |t|}.indicator (normalizedWeyl M)

/-- The zero-rational part, complementary to `nonzeroWeylPart`. -/
@[expose] noncomputable def zeroWeylPart (M : ℝ) : ℝ → ℝ :=
  {t : ℝ | |t| ≤ 1/M}.indicator (normalizedWeyl M)

theorem normalizedWeyl_nonneg {M : ℝ} (hM : 0 < M) (t : ℝ) : 0 ≤ normalizedWeyl M t :=
  div_nonneg (sq_nonneg _) hM.le

theorem nonzeroWeylPart_nonneg {M : ℝ} (hM : 0 < M) (t : ℝ) : 0 ≤ nonzeroWeylPart M t :=
  indicator_nonneg (fun s _hs => normalizedWeyl_nonneg hM s) t

theorem zeroWeylPart_nonneg {M : ℝ} (hM : 0 < M) (t : ℝ) : 0 ≤ zeroWeylPart M t :=
  indicator_nonneg (fun s _hs => normalizedWeyl_nonneg hM s) t

theorem normalizedWeyl_pow_split (M t : ℝ) {d : ℕ} (hd : d ≠ 0) :
    normalizedWeyl M t^d = nonzeroWeylPart M t^d+zeroWeylPart M t^d := by
  by_cases ht : M⁻¹ < |t|
  · simp [nonzeroWeylPart,zeroWeylPart,Set.indicator,ht,not_le_of_gt ht,hd]
  · simp [nonzeroWeylPart,zeroWeylPart,Set.indicator,ht,le_of_not_gt ht,hd]

@[fun_prop] theorem measurable_normalizedWeyl {M : ℝ} (hM : 0 < M) : Measurable (normalizedWeyl M) :=
  (measurable_weylSupremum hM).pow_const 2 |>.div_const M

@[fun_prop] theorem measurable_nonzeroWeylPart {M : ℝ} (hM : 0 < M) : Measurable (nonzeroWeylPart M) :=
  (measurable_normalizedWeyl hM).indicator (by measurability)

@[fun_prop] theorem measurable_zeroWeylPart {M : ℝ} (hM : 0 < M) : Measurable (zeroWeylPart M) :=
  (measurable_normalizedWeyl hM).indicator (by measurability)

/-- The trivial Weyl bound follows directly from nonnegative cutoff mass. -/
theorem weylSupremum_le_five_mul {M : ℝ} (hM : 1 ≤ M) (t : ℝ) :
    weylSupremum M t ≤ 5*M := by
  have hMp : 0 < M := by linarith
  apply ciSup_le
  intro r
  have hh := norm_tsum_nonnegative_weight_le
    (fun n : ℤ => Fourier.chi0 ((n : ℝ)/M))
    (by simpa only [Function.support,sub_zero] using finite_scalar_cutoff hMp 0)
    (fun n => Fourier.chi0_nonneg _)
    (fun n => e (t*(n : ℝ)^2+r*n)) 1 (fun n => (norm_e _).le)
  have hh' : ‖smoothGaussSum weylCutoff M t r 0‖ ≤ ∑' n : ℤ, Fourier.chi0 ((n : ℝ)/M) := by
    simpa only [smoothGaussSum,Int.cast_zero,sub_zero,weylCutoff,one_mul] using hh
  exact hh'.trans (by simpa only [sub_zero] using tsum_translated_chi0_le hM 0)

/-- A uniform cap on the nonzero part, used above the available moment order. -/
theorem nonzeroWeylPart_le {M : ℝ} (hM : 1 ≤ M) (t : ℝ) : nonzeroWeylPart M t ≤ 25*M := by
  have hMp : 0 < M := by linarith
  have hh : normalizedWeyl M t ≤ 25*M := by
    rw [normalizedWeyl,div_le_iff₀ hMp]
    have hb := (sq_le_sq₀ (weylSupremum_nonneg hMp t) (by positivity : (0 : ℝ) ≤ 5*M)).mpr
      (weylSupremum_le_five_mul hM t)
    nlinarith only [hb]
  by_cases ht : M⁻¹ < |t|
  · simpa [nonzeroWeylPart,Set.indicator,ht] using hh
  · simp [nonzeroWeylPart,Set.indicator,ht,le_of_lt hMp]

end WaveTurbulence.WeylSums
