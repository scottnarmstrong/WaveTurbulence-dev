/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.NonstationaryPhase
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Bilinear stationary phase by a Fourier change of variables

TARGET L968; DH23 L1013ff. Integrating one variable produces the Fourier
transform of its amplitude at `-(ξ+s y)`. Its `L¹` norm after dilation is
`|s|^{-d}` times the original Fourier-L¹ norm, uniformly in all translations
and linear frequencies. No general stationary-phase theorem is used.
-/

public section

open MeasureTheory Module
open scoped FourierTransform SchwartzMap

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The bilinear oscillatory integral, with the paper's `2π` phase. -/
@[expose] noncomputable def bilinearPhaseIntegral (f g : V → ℂ)
    (a b ξ ζ : V) (s : ℝ) : ℂ :=
  ∫ y, ∫ x, Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
    (f (x - a) * g (y - b))

private theorem bilinear_inner_eq (f g : V → ℂ) (a b ξ ζ y : V) (s : ℝ) :
    (∫ x, Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
      (f (x - a) * g (y - b))) =
      g (y - b) * (Real.fourierChar (inner ℝ y ζ) •
        ∫ x, Real.fourierChar (inner ℝ x (ξ + s • y)) • f (x - a)) := by
  simp only [Circle.smul_def, smul_eq_mul]
  rw [← mul_assoc, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    have he : inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y =
        inner ℝ y ζ + inner ℝ x (ξ + s • y) := by
      rw [inner_add_right, real_inner_smul_right]
      ring
    rw [he, AddChar.map_add_eq_mul]
    simp only [Circle.coe_mul]
    ring

private theorem bilinear_inner_norm (f g : V → ℂ) (a b ξ ζ y : V) (s : ℝ) :
    ‖∫ x, Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
      (f (x - a) * g (y - b))‖ = ‖g (y - b)‖ * ‖𝓕 f (-(ξ + s • y))‖ := by
  rw [bilinear_inner_eq, norm_mul, Circle.norm_smul, norm_oscillatory_translate_eq]

/-- The uniform small-parameter bound for the bilinear integral. -/
theorem bilinearPhaseIntegral_norm_le (f g : 𝓢(V, ℂ)) (a b ξ ζ : V) (s : ℝ) :
    ‖bilinearPhaseIntegral f g a b ξ ζ s‖ ≤ (∫ x, ‖f x‖) * ∫ y, ‖g y‖ := by
  have hg : Integrable (fun y => ‖g (y - b)‖) := by
    simpa only [sub_eq_add_neg] using g.integrable.norm.comp_add_right (-b)
  have hb (y : V) :
      ‖∫ x, Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
        (f (x - a) * g (y - b))‖ ≤ (∫ x, ‖f x‖) * ‖g (y - b)‖ := by
    rw [bilinear_inner_norm]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (Real.norm_fourier_le_integral_norm (f : V → ℂ) (-(ξ + s • y))) (norm_nonneg _)
  apply (norm_integral_le_of_norm_le (hg.const_mul _) (ae_of_all _ hb)).trans_eq
  rw [integral_const_mul]
  simp_rw [sub_eq_add_neg]
  rw [integral_add_right_eq_self (fun z : V => ‖g z‖) (-b)]

/-- The uniform large-parameter bound; its constant is independent of all
translations and linear frequencies. -/
theorem bilinearPhaseIntegral_norm_le_fourier (f g : 𝓢(V, ℂ)) (a b ξ ζ : V)
    {s : ℝ} (hs : s ≠ 0) :
    ‖bilinearPhaseIntegral f g a b ξ ζ s‖ ≤
      (SchwartzMap.seminorm ℂ 0 0 g) * (|s| ^ finrank ℝ V)⁻¹ * ∫ η, ‖𝓕 f η‖ := by
  let B := SchwartzMap.seminorm ℂ 0 0 g
  have hh : Integrable (fun z : V => ‖𝓕 f (-(ξ + z))‖) := by
    simpa only [Function.comp_def] using ((𝓕 f).integrable.norm.comp_neg).comp_add_left ξ
  have henv : Integrable (fun y => B * ‖𝓕 f (-(ξ + s • y))‖) :=
    (hh.comp_smul hs).const_mul B
  have hb (y : V) :
      ‖∫ x, Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
        (f (x - a) * g (y - b))‖ ≤ B * ‖𝓕 f (-(ξ + s • y))‖ := by
    rw [bilinear_inner_norm]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ g _) (norm_nonneg _)
  apply (norm_integral_le_of_norm_le henv (ae_of_all _ hb)).trans_eq
  rw [integral_const_mul, Measure.integral_comp_smul (volume : Measure V)
    (fun z : V => ‖𝓕 f (-(ξ + z))‖) s]
  rw [integral_add_left_eq_self (fun z : V => ‖𝓕 f (-z)‖) ξ,
    integral_neg_eq_self (fun z : V => ‖𝓕 f z‖)]
  simp only [smul_eq_mul, abs_inv, abs_pow, mul_assoc, B]

/-- A fixed-amplitude constant for the bilinear stationary-phase estimate. -/
@[expose] noncomputable def bilinearPhaseConstant (f g : 𝓢(V, ℂ)) : ℝ :=
  (2 : ℝ) ^ (finrank ℝ V - 1) *
    ((∫ x, ‖f x‖) * (∫ y, ‖g y‖) +
      SchwartzMap.seminorm ℂ 0 0 g * ∫ η, ‖𝓕 f η‖)

/-- TARGET L968 and DH23 L1013ff: the bilinear stationary-phase bound,
uniform in all translations and linear frequencies. -/
theorem bilinear_stationary_phase (f g : 𝓢(V, ℂ)) (hd : 0 < finrank ℝ V)
    (a b ξ ζ : V) (s : ℝ) :
    ‖bilinearPhaseIntegral f g a b ξ ζ s‖ ≤
      bilinearPhaseConstant f g / Real.sqrt (1 + s ^ 2) ^ finrank ℝ V := by
  let u := ‖bilinearPhaseIntegral f g a b ξ ζ s‖
  let P := (∫ x, ‖f x‖) * (∫ y, ‖g y‖)
  let Q := SchwartzMap.seminorm ℂ 0 0 g * ∫ η, ‖𝓕 f η‖
  have hu : 0 ≤ u := norm_nonneg _
  have hP : u ≤ P := bilinearPhaseIntegral_norm_le f g a b ξ ζ s
  have hQ0 : 0 ≤ Q := mul_nonneg (apply_nonneg _ _) (integral_nonneg (fun _ => norm_nonneg _))
  have hQ : |s| ^ finrank ℝ V * u ≤ Q := by
    by_cases hs : s = 0
    · subst s
      simpa only [abs_zero, zero_pow hd.ne', zero_mul] using hQ0
    have hh := bilinearPhaseIntegral_norm_le_fourier f g a b ξ ζ hs
    have hp : |s| ^ finrank ℝ V ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr hs)
    calc
      _ ≤ |s| ^ finrank ℝ V *
          (SchwartzMap.seminorm ℂ 0 0 g * (|s| ^ finrank ℝ V)⁻¹ * ∫ η, ‖𝓕 f η‖) :=
        mul_le_mul_of_nonneg_left hh (pow_nonneg (abs_nonneg s) _)
      _ = Q := by dsimp [Q]; field_simp
  have hweight : (1 + |s|) ^ finrank ℝ V * u ≤
      (2 : ℝ) ^ (finrank ℝ V - 1) * (P + Q) := by
    calc
      _ ≤ (2 : ℝ) ^ (finrank ℝ V - 1) * ((1 + |s| ^ finrank ℝ V) * u) := by
        simpa only [one_pow, mul_assoc] using mul_le_mul_of_nonneg_right
          (add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg s) (finrank ℝ V)) hu
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith only [hP, hQ]
  have hbracket : Real.sqrt (1 + s ^ 2) ≤ 1 + |s| := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)
    have hn := Real.sqrt_nonneg (1 + s ^ 2)
    have ha := abs_nonneg s
    have hsa := sq_abs s
    nlinarith
  apply (le_div_iff₀ (pow_pos (Real.sqrt_pos.mpr (by positivity)) _)).mpr
  calc
    _ ≤ (1 + |s|) ^ finrank ℝ V * u := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.sqrt_nonneg _) hbracket _) hu
    _ ≤ _ := hweight

end WaveTurbulence.Fourier
