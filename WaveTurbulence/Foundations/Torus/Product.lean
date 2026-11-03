/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Torus.Series

/-!
# Coefficients of products on `𝕋_L^d`

For the coefficients `f̂(n) = torusFourierCoeff L f n` of TARGET (1.2) (L286):

* `torusFourierCoeff_torusChar_mul`: modulation, `(e^{2πi (m/L)·x} g)^(n) = ĝ(n - m)`;
* `torusFourierCoeff_conj`: `(ḡ)^(n) = conj ĝ(-n)`;
* `hasSum_torusFourierCoeff_mul`: `(f g)^(n) = L^{-d/2} ∑ₘ f̂(m) ĝ(n - m)`;
* `hasSum_torusFourierCoeff_mul_conj`: `(f ḡ)^(n) = L^{-d/2} ∑ₘ f̂(m) conj ĝ(m - n)`;
* `hasSum_torusFourierCoeff_mul_conj_mul`: the cubic convolution
  `(f ḡ h)^(n) = L^{-d} ∑_{n₁ - n₂ + n₃ = n} f̂(n₁) conj ĝ(n₂) ĥ(n₃)`, parametrized by `(n₁, n₂)`,
  and `hasSum_torusFourierCoeff_mul_conj_mul_resonant`, the same sum over the set
  `{(n₁, n₂, n₃) : n₁ - n₂ + n₃ = n}`;
* `hasSum_torusFourierCoeff_normSq_mul`: the coefficients of `|f|² f` (the NLS nonlinearity,
  TARGET L278) for smooth periodic `f`.

All sums converge absolutely. The products need only the first factors to be periodic with
absolutely summable coefficients (e.g. smooth and periodic); the last factor need only be continuous.
-/

public section

noncomputable section

open MeasureTheory Complex Set
open scoped ContDiff

namespace WaveTurbulence

variable {d : ℕ} {L : ℝ}

/-- Modulation: `(e^{2πi (m/L)·x} g)^(n) = ĝ(n - m)`. -/
theorem torusFourierCoeff_torusChar_mul (L : ℝ) (m : Fin d → ℤ) (g : (Fin d → ℝ) → ℂ)
    (n : Fin d → ℤ) :
    torusFourierCoeff L (fun x => torusChar L m x * g x) n = torusFourierCoeff L g (n - m) := by
  simp only [torusFourierCoeff_eq_integral]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h : torusChar L (-(n - m)) x = torusChar L m x * torusChar L (-n) x := by
    rw [← torusChar_add_index]
    congr 1
    abel
  simp only [h]
  ring

/-- `(ḡ)^(n) = conj ĝ(-n)`. -/
theorem torusFourierCoeff_conj (L : ℝ) (g : (Fin d → ℝ) → ℂ) (n : Fin d → ℤ) :
    torusFourierCoeff L (fun x => (starRingEnd ℂ) (g x)) n =
      (starRingEnd ℂ) (torusFourierCoeff L g (-n)) := by
  simp only [torusFourierCoeff_eq_integral, map_mul, map_inv₀, conj_ofReal, neg_neg]
  congr 1
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, torusChar_neg_index]

theorem exists_bound_Icc {g : (Fin d → ℝ) → ℂ} (hg : Continuous g) (L : ℝ) :
    ∃ C, ∀ x ∈ Icc (0 : Fin d → ℝ) (fun _ => L), ‖g x‖ ≤ C :=
  isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn

/-- The coefficients of a continuous function are bounded. -/
theorem exists_bound_torusFourierCoeff (hL : 0 < L) {g : (Fin d → ℝ) → ℂ} (hg : Continuous g) :
    ∃ C, ∀ n, ‖torusFourierCoeff L g n‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_Icc hg L
  exact ⟨L ^ ((d : ℝ) / 2) * C, fun n => norm_torusFourierCoeff_le hL hC n⟩

/-- The coefficients of a product are the discrete convolution with factor `L^{-d/2}`:
`(f g)^(n) = L^{-d/2} ∑ₘ f̂(m) ĝ(n - m)`, absolutely convergent, for continuous `L`-periodic `f`
with absolutely summable coefficients and continuous `g`. -/
theorem hasSum_torusFourierCoeff_mul (hL : 0 < L) {f g : (Fin d → ℝ) → ℂ} (hf : Continuous f)
    (hpf : IsTorusPeriodic L f) (hsf : Summable fun m => ‖torusFourierCoeff L f m‖)
    (hg : Continuous g) (n : Fin d → ℤ) :
    HasSum (fun m => ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
        (torusFourierCoeff L f m * torusFourierCoeff L g (n - m)))
      (torusFourierCoeff L (fun x => f x * g x) n) := by
  set c' : ℂ := ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ with hc'
  have hexp : (fun x => f x * g x) =
      fun x => ∑' m, c' * torusFourierCoeff L f m * torusChar L m x * g x := by
    funext x
    rw [tsum_mul_right,
      (hasSum_torusFourier_series_of_summable hL hf hpf (Summable.of_norm hsf) x).tsum_eq]
  have hF : ∀ m, torusFourierCoeff L (fun x => c' * torusFourierCoeff L f m * torusChar L m x * g x)
      n = c' * (torusFourierCoeff L f m * torusFourierCoeff L g (n - m)) := by
    intro m
    have h : (fun x => c' * torusFourierCoeff L f m * torusChar L m x * g x) =
        fun x => (c' * torusFourierCoeff L f m) * (torusChar L m x * g x) := by
      funext x
      ring
    rw [h, torusFourierCoeff_const_mul, torusFourierCoeff_torusChar_mul]
    ring
  have hint : ∀ m, IntegrableOn
      (fun x => c' * torusFourierCoeff L f m * torusChar L m x * g x)
      (Icc (0 : Fin d → ℝ) (fun _ => L)) := fun m =>
    ((continuous_const.mul (continuous_torusChar L m)).mul hg).integrableOn_Icc
  have hnorm : ∀ m, ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L),
      ‖c' * torusFourierCoeff L f m * torusChar L m x * g x‖ =
      ‖c'‖ * (∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), ‖g x‖) * ‖torusFourierCoeff L f m‖ := by
    intro m
    simp only [norm_mul, norm_torusChar, mul_one]
    rw [integral_const_mul]
    ring
  obtain ⟨C, hC⟩ := exists_bound_torusFourierCoeff hL hg
  have hsum : Summable fun m => c' * (torusFourierCoeff L f m * torusFourierCoeff L g (n - m)) := by
    refine Summable.of_norm_bounded (hsf.mul_left (‖c'‖ * C)) fun m => ?_
    rw [norm_mul, norm_mul]
    calc ‖c'‖ * (‖torusFourierCoeff L f m‖ * ‖torusFourierCoeff L g (n - m)‖)
        ≤ ‖c'‖ * (‖torusFourierCoeff L f m‖ * C) := by gcongr; exact hC _
      _ = ‖c'‖ * C * ‖torusFourierCoeff L f m‖ := by ring
  rw [hexp, torusFourierCoeff_tsum hint (by simp_rw [hnorm]; exact hsf.mul_left _)]
  simp_rw [hF]
  exact hsum.hasSum

/-- `(f ḡ)^(n) = L^{-d/2} ∑ₘ f̂(m) conj ĝ(m - n)`, absolutely convergent. -/
theorem hasSum_torusFourierCoeff_mul_conj (hL : 0 < L) {f g : (Fin d → ℝ) → ℂ}
    (hf : Continuous f) (hpf : IsTorusPeriodic L f)
    (hsf : Summable fun m => ‖torusFourierCoeff L f m‖) (hg : Continuous g) (n : Fin d → ℤ) :
    HasSum (fun m => ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
        (torusFourierCoeff L f m * (starRingEnd ℂ) (torusFourierCoeff L g (m - n))))
      (torusFourierCoeff L (fun x => f x * (starRingEnd ℂ) (g x)) n) := by
  have h := hasSum_torusFourierCoeff_mul (g := fun x => (starRingEnd ℂ) (g x)) hL hf hpf hsf
    (continuous_conj.comp hg) n
  simp only [torusFourierCoeff_conj, neg_sub] at h
  exact h

/-- The cubic convolution (TARGET L278, L540–L566): for continuous `L`-periodic `f, g` with
absolutely summable coefficients and continuous `h`,
`(f ḡ h)^(n) = L^{-d} ∑_{(n₁, n₂)} f̂(n₁) conj ĝ(n₂) ĥ(n - n₁ + n₂)`, absolutely convergent
(the sum over `n₁ - n₂ + n₃ = n`, parametrized by `(n₁, n₂)`). -/
theorem hasSum_torusFourierCoeff_mul_conj_mul (hL : 0 < L) {f g h : (Fin d → ℝ) → ℂ}
    (hf : Continuous f) (hpf : IsTorusPeriodic L f)
    (hsf : Summable fun m => ‖torusFourierCoeff L f m‖)
    (hg : Continuous g) (hpg : IsTorusPeriodic L g)
    (hsg : Summable fun m => ‖torusFourierCoeff L g m‖) (hh : Continuous h) (n : Fin d → ℤ) :
    HasSum (fun p : (Fin d → ℤ) × (Fin d → ℤ) => ((L ^ d : ℝ) : ℂ)⁻¹ *
        (torusFourierCoeff L f p.1 * (starRingEnd ℂ) (torusFourierCoeff L g p.2) *
          torusFourierCoeff L h (n - p.1 + p.2)))
      (torusFourierCoeff L (fun x => f x * (starRingEnd ℂ) (g x) * h x) n) := by
  set c' : ℂ := ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ with hc'
  have hcc : ((L ^ d : ℝ) : ℂ)⁻¹ = c' * c' := by
    rw [hc', ← mul_inv, ← ofReal_mul, ← sq, rpow_half_sq hL]
  -- the coefficients of `ḡ h`
  have hgc : Continuous fun x => (starRingEnd ℂ) (g x) := continuous_conj.comp hg
  have hsg' : Summable fun m => ‖torusFourierCoeff L (fun x => (starRingEnd ℂ) (g x)) m‖ := by
    simp_rw [torusFourierCoeff_conj, Complex.norm_conj]
    exact hsg.comp_injective neg_injective
  have hG : ∀ k, HasSum (fun n₂ => c' * ((starRingEnd ℂ) (torusFourierCoeff L g n₂) *
      torusFourierCoeff L h (k + n₂)))
      (torusFourierCoeff L (fun x => (starRingEnd ℂ) (g x) * h x) k) := by
    intro k
    have h1 := hasSum_torusFourierCoeff_mul (f := fun x => (starRingEnd ℂ) (g x)) hL hgc
      (hpg.comp _) hsg' hh k
    have h2 := (Equiv.neg (Fin d → ℤ)).hasSum_iff.mpr h1
    simp only [Function.comp_def, Equiv.neg_apply, torusFourierCoeff_conj, neg_neg,
      sub_neg_eq_add] at h2
    exact h2
  -- the outer product
  have hF := hasSum_torusFourierCoeff_mul (g := fun x => (starRingEnd ℂ) (g x) * h x) hL hf hpf
    hsf (hgc.mul hh) n
  -- joint summability
  obtain ⟨C, hC⟩ := exists_bound_torusFourierCoeff hL hh
  set F : (Fin d → ℤ) × (Fin d → ℤ) → ℂ := fun p => ((L ^ d : ℝ) : ℂ)⁻¹ *
    (torusFourierCoeff L f p.1 * (starRingEnd ℂ) (torusFourierCoeff L g p.2) *
      torusFourierCoeff L h (n - p.1 + p.2)) with hFdef
  have hFs : Summable F := by
    refine Summable.of_norm_bounded
      (((hsf.mul_of_nonneg hsg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left
        (‖((L ^ d : ℝ) : ℂ)⁻¹‖ * C))) fun p => ?_
    simp only [hFdef, norm_mul, Complex.norm_conj]
    calc ‖((L ^ d : ℝ) : ℂ)⁻¹‖ * (‖torusFourierCoeff L f p.1‖ * ‖torusFourierCoeff L g p.2‖ *
          ‖torusFourierCoeff L h (n - p.1 + p.2)‖)
        ≤ ‖((L ^ d : ℝ) : ℂ)⁻¹‖ * (‖torusFourierCoeff L f p.1‖ * ‖torusFourierCoeff L g p.2‖ *
          C) := by gcongr; exact hC _
      _ = ‖((L ^ d : ℝ) : ℂ)⁻¹‖ * C *
          (‖torusFourierCoeff L f p.1‖ * ‖torusFourierCoeff L g p.2‖) := by ring
  have hinner : ∀ n₁, HasSum (fun n₂ => F (n₁, n₂))
      (c' * (torusFourierCoeff L f n₁ *
        torusFourierCoeff L (fun x => (starRingEnd ℂ) (g x) * h x) (n - n₁))) := by
    intro n₁
    have := ((hG (n - n₁)).mul_left (c' * torusFourierCoeff L f n₁))
    convert this using 1
    · funext n₂
      simp only [hFdef, hcc]
      ring
    · ring
  have hassoc : (fun x => f x * (starRingEnd ℂ) (g x) * h x) =
      fun x => f x * ((starRingEnd ℂ) (g x) * h x) := by
    funext x
    ring
  have hval : torusFourierCoeff L (fun x => f x * (starRingEnd ℂ) (g x) * h x) n = ∑' p, F p := by
    rw [hassoc, hFs.tsum_prod, ← hF.tsum_eq]
    exact tsum_congr fun n₁ => ((hinner n₁).tsum_eq).symm
  rw [hval]
  exact hFs.hasSum

/-- The cubic convolution as a sum over the resonant set `{(n₁, n₂, n₃) : n₁ - n₂ + n₃ = n}`:
`(f ḡ h)^(n) = L^{-d} ∑_{n₁ - n₂ + n₃ = n} f̂(n₁) conj ĝ(n₂) ĥ(n₃)` (TARGET L540–L566). -/
theorem hasSum_torusFourierCoeff_mul_conj_mul_resonant (hL : 0 < L) {f g h : (Fin d → ℝ) → ℂ}
    (hf : Continuous f) (hpf : IsTorusPeriodic L f)
    (hsf : Summable fun m => ‖torusFourierCoeff L f m‖)
    (hg : Continuous g) (hpg : IsTorusPeriodic L g)
    (hsg : Summable fun m => ‖torusFourierCoeff L g m‖) (hh : Continuous h) (n : Fin d → ℤ) :
    HasSum (fun p : {p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) // p.1 - p.2.1 + p.2.2 = n} =>
        ((L ^ d : ℝ) : ℂ)⁻¹ * (torusFourierCoeff L f p.1.1 *
          (starRingEnd ℂ) (torusFourierCoeff L g p.1.2.1) * torusFourierCoeff L h p.1.2.2))
      (torusFourierCoeff L (fun x => f x * (starRingEnd ℂ) (g x) * h x) n) := by
  let e : (Fin d → ℤ) × (Fin d → ℤ) ≃
      {p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) // p.1 - p.2.1 + p.2.2 = n} :=
    { toFun := fun q => ⟨(q.1, q.2, n - q.1 + q.2), by dsimp only; abel⟩
      invFun := fun p => (p.1.1, p.1.2.1)
      left_inv := fun q => rfl
      right_inv := fun p => by
        obtain ⟨⟨a, b, c⟩, hp⟩ := p
        have hc : n - a + b = c := by rw [← hp]; abel
        exact Subtype.ext (by dsimp only; rw [hc]) }
  exact e.hasSum_iff.mp (hasSum_torusFourierCoeff_mul_conj_mul hL hf hpf hsf hg hpg hsg hh n)

/-- The coefficients of the NLS nonlinearity `|f|² f` (TARGET L278) for smooth `L`-periodic `f`:
`(|f|² f)^(n) = L^{-d} ∑_{(n₁, n₂)} f̂(n₁) conj f̂(n₂) f̂(n - n₁ + n₂)`, absolutely convergent. -/
theorem hasSum_torusFourierCoeff_normSq_mul (hL : 0 < L) {f : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : IsTorusPeriodic L f) (n : Fin d → ℤ) :
    HasSum (fun p : (Fin d → ℤ) × (Fin d → ℤ) => ((L ^ d : ℝ) : ℂ)⁻¹ *
        (torusFourierCoeff L f p.1 * (starRingEnd ℂ) (torusFourierCoeff L f p.2) *
          torusFourierCoeff L f (n - p.1 + p.2)))
      (torusFourierCoeff L (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) * f x) n) := by
  have hfun : (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) * f x) =
      fun x => f x * (starRingEnd ℂ) (f x) * f x := by
    funext x
    rw [Complex.mul_conj', ofReal_pow]
  rw [hfun]
  exact hasSum_torusFourierCoeff_mul_conj_mul hL hf.continuous hp
    (summable_norm_torusFourierCoeff hL hf hp) hf.continuous hp
    (summable_norm_torusFourierCoeff hL hf hp) hf.continuous n

end WaveTurbulence
