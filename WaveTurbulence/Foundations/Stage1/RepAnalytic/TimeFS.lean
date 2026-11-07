/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSMain
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SNormAux

/-! # W6: time-Fourier superposition of an `XNormRestr`-bounded kernel

TARGET L1961: "by the weighted Fourier `L¹` bounds for `K*_Q`, `K*_T` ... we can decompose these functions
using time Fourier transform".  The decomposition used is the period-2 Fourier series of
`VineEstS3.FS.fs_expansion` on a unit time cell (modes `e^{πi m·t}`, `m ∈ ℤ^r`): a function `f(t,k)` with
`‖f‖_{𝔛^{θ,Λ₁,Λ₂}(B × K)} < b` is `∑_m w_m a_m(k) e^{πi m·t}` on `B × K` with `w_m ≥ 0`, `‖a_m‖_{𝔖^{Λ₁,Λ₂}} ≤ 1`
and `∑_m ⟨m/2⟩^θ w_m ≤ C b`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS MeasureTheory
open scoped ENNReal

variable {r d : ℕ}

/-- Normalise a function of finite `𝔖`-norm: `c = w · a`, `w = ‖c‖`, `‖a‖ ≤ 1`. -/
theorem exists_normalised {Λ₁ Λ₂ : ℕ} (c : Mom d → ℂ) (h : SNorm Λ₁ Λ₂ c ≠ ⊤) :
    ∃ (w : ℝ) (a : Mom d → ℂ), 0 ≤ w ∧ ENNReal.ofReal w = SNorm Λ₁ Λ₂ c ∧
      SNorm Λ₁ Λ₂ a ≤ 1 ∧ (∀ k, c k = w * a k) ∧ ∀ k, a k ≠ 0 → c k ≠ 0 := by
  set w : ℝ := (SNorm Λ₁ Λ₂ c).toReal with hw
  have hwe : ENNReal.ofReal w = SNorm Λ₁ Λ₂ c := ENNReal.ofReal_toReal h
  by_cases hw0 : w = 0
  · have hc0 : SNorm Λ₁ Λ₂ c = 0 := by rw [← hwe, hw0]; simp
    have hc : c = 0 := VineEstS3.Eng.eq_zero_of_SNorm_eq_zero hc0
    refine ⟨w, 0, ENNReal.toReal_nonneg, hwe, ?_, fun k => by simp [hc, hw0], fun k hk => absurd rfl hk⟩
    have := VineEstS3.Eng.SNorm_smul_le (d := d) Λ₁ Λ₂ 0 (0 : Mom d → ℂ)
    simp only [zero_mul, enorm_zero] at this
    show SNorm Λ₁ Λ₂ (fun _ => 0) ≤ 1
    exact (le_of_le_of_eq this (by simp)).trans zero_le_one
  · have hwpos : 0 < w := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hw0)
    refine ⟨w, fun k => ((w⁻¹ : ℝ) : ℂ) * c k, ENNReal.toReal_nonneg, hwe, ?_, fun k => ?_, fun k hk h0 => hk (by simp [h0])⟩
    · refine (VineEstS3.Eng.SNorm_smul_le Λ₁ Λ₂ ((w⁻¹ : ℝ) : ℂ) c).trans ?_
      rw [← hwe, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity),
        inv_mul_cancel₀ hwpos.ne']
      simp
    · have : (w : ℂ) ≠ 0 := by exact_mod_cast hw0
      push_cast
      field_simp

theorem one_le_maxBracketPow {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (lam : Fin r → ℝ) : 1 ≤ maxBracketPow θ lam := by
  unfold maxBracketPow
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow le_sup_right hθ)

theorem summable_of_tsum_ofReal_ne_top {ι : Type*} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (h : ∑' i, ENNReal.ofReal (w i) ≠ ⊤) : Summable w := by
  have := ENNReal.summable_toReal h
  refine this.congr fun i => ?_
  simp [ENNReal.toReal_ofReal (hw i)]

/-- **W6, single time vector.**  A function `f(t,k)` with finite restriction norm
`‖f‖_{𝔛^{θ,Λ₁,Λ₂}(B × K)} < b`, `B` in a unit time cell, is a superposition
`f(t,k) = ∑_m w_m a_m(k) e^{πi m·t}` (`t ∈ B`, `k ∈ K`) of unit-`𝔖^{Λ₁,Λ₂}` amplitudes with an `ℓ¹` weight
`∑_m ⟨m/2⟩^θ w_m ≤ C b`; `C` depends on `(r, d, θ, Λ₁, Λ₂)` only (TARGET L1961, "weighted Fourier `L¹`
bounds ... decompose using time Fourier transform"). -/
theorem fourier_superposition {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (hΛ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B : Set (Fin r → ℝ)) (K : Set (Mom d))
      (f : (Fin r → ℝ) → Mom d → ℂ) (b : ℝ≥0∞), b ≠ ⊤ →
      B ⊆ cell q → B ⊆ closure (interior B) → (∀ k ∈ K, Continuous fun t => f t k) →
      XNormRestr θ Λ₁ Λ₂ B K f < b →
      ∃ (w : (Fin r → ℤ) → ℝ) (a : (Fin r → ℤ) → Mom d → ℂ),
        (∀ m, 0 ≤ w m) ∧ (∀ m, SNorm Λ₁ Λ₂ (a m) ≤ 1) ∧
        (∀ t ∈ B, ∀ k ∈ K, HasSum (fun m => (w m : ℂ) * a m k * fsPhase m t) (f t k)) ∧
        Summable w ∧
        ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) ≤ C * b := by
  obtain ⟨C, hC, hfs⟩ := fs_expansion (r := r) (d := d) hθ (Λ₂ := Λ₂) hΛ
  refine ⟨C, hC, fun q B K f b hb hBc hBi hfc hn => ?_⟩
  obtain ⟨c, hser, hbound⟩ := hfs q B K f b hBc hBi hfc hn
  have hfin : ∑' m, maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (c m) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hC hb) hbound
  have hc : ∀ m, SNorm Λ₁ Λ₂ (c m) ≠ ⊤ := by
    intro m
    have h1 : maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (c m) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin
        (ENNReal.le_tsum (f := fun m => maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (c m)) m)
    intro htop
    apply h1
    rw [htop, ENNReal.mul_top]
    have := one_le_maxBracketPow hθ (half m)
    exact (lt_of_lt_of_le one_pos this).ne'
  choose w a hw0 hwe ha hca _ using fun m => exists_normalised (c m) (hc m)
  have hsum_eq : ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) =
      ∑' m, maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (c m) := by
    refine tsum_congr fun m => ?_
    rw [hwe m]
  refine ⟨w, a, hw0, ha, fun t ht k hk => ?_, ?_, hsum_eq ▸ hbound⟩
  · refine (hser t ht k hk).congr_fun ?_
    intro m
    simp only [hca m k]
  · refine summable_of_tsum_ofReal_ne_top hw0 ?_
    refine ne_top_of_le_ne_top hfin ?_
    rw [← hsum_eq]
    exact ENNReal.tsum_le_tsum fun m => le_mul_of_one_le_left bot_le (one_le_maxBracketPow hθ _)

end WaveTurbulence.RepAnalytic
