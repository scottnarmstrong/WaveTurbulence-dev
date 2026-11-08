/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CoupleExtension
public import WaveTurbulence.Foundations.Incoh.RootDensityEndpoints
public import WaveTurbulence.Foundations.Incoh.PhysicalInterpolation
public import WaveTurbulence.Foundations.Incoh.ConstantAbsorption

/-! # D5b-3 FILT-GATE: the `θ = 1/4` couple core (o82 Lemma 16.1, T1052–1057)

o82 Lemma 16.1 for an incoherent couple: the double primitive `S` has the source endpoint bounds (T1050)
`‖S‖₁ ≤ A`, `‖S‖_∞ ≤ A L^{2d}` with `A = (Cδ)^m L^{-(γ₁-2η)g}`, and its canonical cutoff extension has `X^{1/4}` norm
`≤ C A L^d`. Here the time-integration lemma is main's `Fourier.exists_cutoff_timeIntegral_bounds` (TARGET A.2)
taken at weight `1/4` (its range is `0 < η ≤ 1/3`): `‖ℐ_χ S‖_{X^{1/4}} ≤ C ‖S‖_{L^{7/4}}`, and main's physical
interpolation `‖S‖_{7/4} ≤ A (L^{2d})^{3/7} ≤ A L^d` (the paper interpolates to `L²` with the same `L^d`).

The cutoff constant `C` (it depends on `χ`, chosen after `D`) is absorbed into `L^{ηg}`, `g ≥ 1`, exactly as main's
`exists_coupleExtension_cutoffUniform_decay` does; the cell rate then has the `X^η` bound's shape times `L^{4d}`.

- `exists_cutoffDoubleIntegral_quarter_bound`, `exists_translated_quarter_bound`: the abstract core (any density).
- `quarter_cell_rate_le`: the rate algebra.
- `exists_coupleExtension_quarter_decay`: the cell bound for main's (unfiltered) couple extension; the filtered
  twin is the same proof over D5b-2's endpoint bounds. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.FiltGate
open WaveTurbulence.Incoh

/-- o82 Lemma 16.1, couple core: the cutoff double primitive of a density with `‖S‖₁ ≤ A` and `‖S‖_∞ ≤ A Λ`
(`Λ ≥ 1`) has `X^{1/4}` norm at most `C A Λ^{1/2}`. -/
theorem exists_cutoffDoubleIntegral_quarter_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : (Fin 2 → ℝ) → ℂ, AEStronglyMeasurable F volume →
      ∀ A Λ : ℝ≥0∞, 1 ≤ Λ → eLpNorm F 1 volume ≤ A → (∀ t, ‖F t‖ₑ ≤ A * Λ) →
      Fourier.timeFourierNorm (1 / 4) (Fourier.cutoffDoubleIntegral χ F) ≤
        ENNReal.ofReal C * (A * Λ ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, hC, htime, -⟩ :=
    Fourier.exists_cutoff_timeIntegral_bounds (η := 1 / 4) (by norm_num) (by norm_num) hχ hcχ
  refine ⟨C, hC, fun F hF A Λ hΛ h1 hinf => (htime F).trans (mul_le_mul' le_rfl ?_)⟩
  have hp : (1 : ℝ) ≤ 1 + 3 * (1 / 4) := by norm_num
  refine (eLpNorm_le_of_one_and_scaled_pointwise hF hp h1
    (Filter.Eventually.of_forall hinf)).trans (mul_le_mul' le_rfl ?_)
  exact ENNReal.rpow_le_rpow_of_exponent_le hΛ (by norm_num)

/-- The core for the canonical extension in physical clocks: the local density is `S(· + b)`, the extension is
evaluated at `t - b`. -/
theorem exists_translated_quarter_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (Fin 2 → ℝ) → ℂ) (b : Fin 2 → ℝ), AEStronglyMeasurable F volume →
      ∀ A Λ : ℝ≥0∞, 1 ≤ Λ → eLpNorm F 1 volume ≤ A → (∀ t, ‖F t‖ₑ ≤ A * Λ) →
      Fourier.timeFourierNorm (1 / 4)
          (fun t => Fourier.cutoffDoubleIntegral χ (fun s => F (s + b)) (t - b)) ≤
        ENNReal.ofReal C * (A * Λ ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := exists_cutoffDoubleIntegral_quarter_bound hχ hcχ
  refine ⟨C, hC, fun F b hF A Λ hΛ h1 hinf => ?_⟩
  have hmp : MeasurePreserving (fun t : Fin 2 → ℝ => t + b) volume volume :=
    measurePreserving_add_right volume b
  have heq : (fun t => Fourier.cutoffDoubleIntegral χ (fun s => F (s + b)) (t - b)) =
      fun t => Fourier.cutoffDoubleIntegral χ (fun s => F (s + b)) (t + -b) := by
    funext t
    rw [sub_eq_add_neg]
  rw [heq, Fourier.timeFourierNorm_translate]
  refine h _ (hF.comp_measurePreserving hmp) A Λ hΛ ?_ (fun t => hinf _)
  rw [eLpNorm_comp_measurePreserving hF hmp]
  exact h1

/-- The rate algebra of the `θ = 1/4` cell bound: `C · A · (L^{2d})^{1/2}` with `A = X L^{-(γ₁-2η)g}` and the
cutoff constant `C ≤ L^{ηg}` is at most the `X^η` rate `X L^{-(γ₁-100dη)g}` times `L^{4d}`. -/
theorem quarter_cell_rate_le {d g : ℕ} (hd : 1 ≤ d) {L η γ₁ C X : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hX : 0 ≤ X) (hC : 0 ≤ C) (hCL : C ≤ L ^ (η * g)) :
    ENNReal.ofReal C * (ENNReal.ofReal (X * L ^ (-(γ₁ - 2 * η) * g)) *
        ENNReal.ofReal (L ^ (2 * (d : ℝ))) ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal (X * L ^ (-(γ₁ - 100 * (d : ℝ) * η) * g) * L ^ (4 * (d : ℝ))) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hL0 _) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.rpow_mul hL0, show 2 * (d : ℝ) * (1 / 2) = d by ring]
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hgR : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have h1 : C * L ^ (-(γ₁ - 2 * η) * g) ≤ L ^ (-(γ₁ - 100 * (d : ℝ) * η) * g) := by
    calc C * L ^ (-(γ₁ - 2 * η) * g) ≤ L ^ (η * g) * L ^ (-(γ₁ - 2 * η) * g) :=
          mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg hL0 _)
      _ = L ^ (η * g + -(γ₁ - 2 * η) * g) := (Real.rpow_add hLp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by
          nlinarith [mul_nonneg hη hgR, mul_nonneg (mul_nonneg hη hgR) (sub_nonneg.mpr hdR)])
  have h2 : L ^ (d : ℝ) ≤ L ^ (4 * (d : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  calc C * (X * L ^ (-(γ₁ - 2 * η) * g) * L ^ (d : ℝ))
      = X * (C * L ^ (-(γ₁ - 2 * η) * g)) * L ^ (d : ℝ) := by ring
    _ ≤ X * L ^ (-(γ₁ - 100 * (d : ℝ) * η) * g) * L ^ (4 * (d : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hX) h2 (Real.rpow_nonneg hL0 _)
        (mul_nonneg hX (Real.rpow_nonneg hL0 _))

/-- `(K C δ)^n` is monotone in `C`. -/
theorem kpow_mono {K C C' δ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hCC : C ≤ C') (hδ : 0 ≤ δ) (n : ℕ) :
    (K * C * δ) ^ n ≤ (K * C' * δ) ^ n :=
  pow_le_pow_left₀ (mul_nonneg (mul_nonneg hK hC) hδ)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCC hK) hδ) n

/-- **o82 Lemma 16.1, incoherent couple** (main's unfiltered extension): the `X^{1/4}` bound with loss `L^{4d}` and the
incoherency gain at the `100dη` loss of the `X^η` bound (`exists_coupleExtension_cutoffUniform_decay`); the
dimensional constant precedes the cutoff. -/
theorem exists_coupleExtension_quarter_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ η : ℝ, 0 < η →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        Fourier.timeFourierNorm (1 / 4) (R.coupleExtension χ L γ δ Q I) ≤
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) *
              L ^ (4 * (d : ℝ))) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_rootDensity_endpoint_bounds d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro η hη χ hχ hcχ
  obtain ⟨Cₜ, hCₜ, htime⟩ := exists_translated_quarter_bound hχ hcχ
  obtain ⟨Lₐ, hLₐ, ha⟩ := exists_constant_absorption_threshold Cₜ hη
  intro γ hγ hηg δ hδ hδ₁ D hD
  obtain ⟨Lᵦ, hLᵦ, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨max Lₐ Lᵦ, hLₐ.trans (le_max_left _ _), ?_⟩
  intro L hL n Q hg hspan I hI hbox R
  have hLa := (le_max_left Lₐ Lᵦ).trans hL
  have hLb := (le_max_right Lₐ Lᵦ).trans hL
  have hLone := hLₐ.trans hLa
  have hLp := zero_lt_one.trans_le hLone
  obtain ⟨h1, hinf⟩ := hb L hLb n Q hspan I hI hbox R
  have hgR : (1 : ℝ) ≤ incoherenceCount Q := by exact_mod_cast hg
  have hCt : Cₜ ≤ L ^ (η * incoherenceCount Q) := (ha L hLa).trans
    (Real.rpow_le_rpow_of_exponent_le hLone (by nlinarith only [hgR, hη.le]))
  have hΛ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (L ^ (2 * (d : ℝ))) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow hLone (by positivity))
  have hq := htime (R.linkDensity L γ δ Q I) (R.baseRootTimes Q)
    (R.integrable_linkDensity hLp γ δ Q hI hbox).aestronglyMeasurable _ _ hΛ h1 hinf
  exact hq.trans (quarter_cell_rate_le (by omega) hLone hη.le (by positivity) hCₜ.le hCt)

end WaveTurbulence.Flower.FiltGate
