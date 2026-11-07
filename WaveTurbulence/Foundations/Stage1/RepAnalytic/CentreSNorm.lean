/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.CentreSum

/-! # W5, leaf centres: the `𝔖^{A,0}` Leibniz bound and the centre sum

* `snorm_chi_mul_le`: `‖χ_n H‖_{𝔖^{A,0}} ≤ C ⟨a n⟩^{-Λ} ‖H‖_{𝔖^{A,Λ}}` (Leibniz, via
  `LGSpine.SNorm_mul_of_polynomial_jet_bound`), uniformly in `n`.
* `tsum_snorm_chi_mul_le`: `∑_n ‖χ_n H‖_{𝔖^{A,0}} ≤ C ‖H‖_{𝔖^{A,Λ}}` for `Λ > d`.
* `hasSum_chiC_mul`: `H = ∑_n χ_n H` pointwise.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence Finset
open scoped ContDiff ENNReal

/-- **Leibniz bound for a single centre** (uniform in the centre; the decay `⟨a n⟩^{-Λ}` is explicit). -/
theorem snorm_chi_mul_le {d : ℕ} (hd : 1 ≤ d) (A Λ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Mom d → ℂ), ContDiff ℝ A H → ∀ n : Fin d → ℤ,
      SNorm A 0 (fun k => chiC d n k * H k) ≤
        ENNReal.ofReal (C * ((jbr (latPt d n)) ^ Λ)⁻¹) * SNorm A Λ H := by
  obtain ⟨C0, hC0, hC⟩ := chi_jet_poly_bound d A Λ
  refine ⟨(2 : ℝ) ^ A * (d : ℝ) ^ A * C0 + 1, by positivity, fun H hH n => ?_⟩
  have hJ := Induct.jbr_pos (latPt d n)
  have hu : 0 < ((jbr (latPt d n)) ^ Λ)⁻¹ := by positivity
  set C : ℝ := (2 : ℝ) ^ A * (d : ℝ) ^ A * C0 + 1 with hCdef
  have hCpos : 0 < C * ((jbr (latPt d n)) ^ Λ)⁻¹ := by positivity
  by_cases htop : SNorm A Λ H = ⊤
  · rw [htop, ENNReal.mul_top (by simpa using hCpos)]
    exact le_top
  · set CF : ℝ := (SNorm A Λ H).toReal with hCF
    have hF : SNorm A (0 + Λ) H ≤ ENNReal.ofReal CF := by
      rw [zero_add, hCF, ENNReal.ofReal_toReal htop]
    have key := LGSpine.SNorm_mul_of_polynomial_jet_bound (A := A) (B := 0) (M := Λ) hd (chiC d n) H
      (chiC_contDiff d n A) hH (C0 * ((jbr (latPt d n)) ^ Λ)⁻¹) CF (by positivity) ENNReal.toReal_nonneg
      (fun r hr x => hC n r hr x) hF
    refine key.trans ?_
    rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul hCpos.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hCF0 : 0 ≤ CF := ENNReal.toReal_nonneg
    rw [hCF] at *
    set S := (SNorm A Λ H).toReal
    have : (2 : ℝ) ^ A * (d : ℝ) ^ A * (C0 * ((jbr (latPt d n)) ^ Λ)⁻¹) * S =
        ((2 : ℝ) ^ A * (d : ℝ) ^ A * C0) * ((jbr (latPt d n)) ^ Λ)⁻¹ * S := by ring
    rw [this]
    have h1 : (2 : ℝ) ^ A * (d : ℝ) ^ A * C0 ≤ C := by rw [hCdef]; linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hu.le
    exact mul_le_mul_of_nonneg_right h2 hCF0

/-- **The centre sum**: `∑_n ‖χ_n H‖_{𝔖^{A,0}} ≤ C ‖H‖_{𝔖^{A,Λ}}`, `Λ > d`. -/
theorem tsum_snorm_chi_mul_le {d : ℕ} (hd : 1 ≤ d) (A : ℕ) {Λ : ℕ} (hΛ : d < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Mom d → ℂ), ContDiff ℝ A H →
      ∑' n : Fin d → ℤ, SNorm A 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal C * SNorm A Λ H := by
  obtain ⟨C1, hC1, hC⟩ := snorm_chi_mul_le hd A Λ
  have hsum := (summable_jbr_latPt_inv hd hΛ).mul_left C1
  refine ⟨C1 * ∑' n : Fin d → ℤ, ((jbr (latPt d n)) ^ Λ)⁻¹, ?_, fun H hH => ?_⟩
  · refine mul_pos hC1 ?_
    exact (summable_jbr_latPt_inv hd hΛ).tsum_pos
      (fun n => inv_nonneg.2 (pow_nonneg (Induct.jbr_pos _).le _)) 0
      (by have := Induct.jbr_pos (latPt d 0); positivity)
  · calc ∑' n : Fin d → ℤ, SNorm A 0 (fun k => chiC d n k * H k)
        ≤ ∑' n : Fin d → ℤ, ENNReal.ofReal (C1 * ((jbr (latPt d n)) ^ Λ)⁻¹) * SNorm A Λ H :=
          ENNReal.tsum_le_tsum fun n => hC H hH n
      _ = (∑' n : Fin d → ℤ, ENNReal.ofReal (C1 * ((jbr (latPt d n)) ^ Λ)⁻¹)) * SNorm A Λ H :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (∑' n : Fin d → ℤ, C1 * ((jbr (latPt d n)) ^ Λ)⁻¹) * SNorm A Λ H := by
          rw [ENNReal.ofReal_tsum_of_nonneg
            (fun n => mul_nonneg hC1.le (inv_nonneg.2 (pow_nonneg (Induct.jbr_pos _).le _))) hsum]
      _ = _ := by rw [tsum_mul_left]

/-- **Pointwise decomposition** `H(k) = ∑_n χ_n(k) H(k)`. -/
theorem hasSum_chiC_mul {d : ℕ} (H : Mom d → ℂ) (k : Mom d) :
    HasSum (fun n : Fin d → ℤ => chiC d n k * H k) (H k) := by
  have h : HasSum (fun n : Fin d → ℤ => chiC d n k) 1 := by
    have := Complex.hasSum_ofReal.2 (hasSum_chi d k)
    simpa [chiC] using this
  simpa using h.mul_right (H k)

/-- The support of `χ_n H` lies in the unit ball around `a n`. -/
theorem norm_sub_latPt_le_one_of_chiC_mul_ne_zero {d : ℕ} {H : Mom d → ℂ} {n : Fin d → ℤ} {k : Mom d}
    (h : chiC d n k * H k ≠ 0) : ‖k - latPt d n‖ ≤ 1 := by
  refine norm_sub_le_one_of_chi_ne_zero (fun h0 => h ?_)
  simp [chiC, h0]

end WaveTurbulence.RepAnalytic
