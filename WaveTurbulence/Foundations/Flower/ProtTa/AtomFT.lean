/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtTa.Recon

/-! # PROT-TA, Lemma 12.1: the output atoms `Φ(t,s) e^{2πi(l₀t+(l₁+l₂)s)} h_{A/2+l₁}(t-s)` and their norms -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtTa

/-- The cutoff output atom of the frequency `l` (12.3). -/
def atom (A : ℝ) (l : Fin 3 → ℝ) (y : Fin 2 → ℝ) : ℂ :=
  Real.fourierChar (timePairing 2 y (nu l)) • psi (A / 2 + l 1) y

theorem atom_of_Phi {A : ℝ} {l : Fin 3 → ℝ} {y : Fin 2 → ℝ} (hy : Phi y = 1) :
    atom A l y = (Real.fourierChar (timePairing 2 y (nu l)) : ℂ) * hz (A / 2 + l 1) (y 0 - y 1) := by
  simp only [atom, psi, hy, one_mul, Circle.smul_def, smul_eq_mul]

theorem psi_continuous : Continuous (fun p : ℝ × (Fin 2 → ℝ) => psi p.1 p.2) := by
  simp only [psi]
  have h1 := Phi_contDiff.continuous
  have h2 : Continuous (fun p : ℝ × (Fin 2 → ℝ) => hz p.1 (p.2 0 - p.2 1)) :=
    hz_continuous.comp (by fun_prop : Continuous fun p : ℝ × (Fin 2 → ℝ) => (p.1, p.2 0 - p.2 1))
  exact (h1.comp continuous_snd).mul h2

theorem atom_continuous (A : ℝ) :
    Continuous (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) => atom A p.1 p.2) := by
  have h := psi_continuous.comp (by fun_prop : Continuous fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) =>
    (A / 2 + p.1 1, p.2))
  simp only [atom, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, pairing_apply, Fin.sum_univ_two, nu]
  have h' : Continuous (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) =>
      Complex.exp (((2 * Real.pi * (p.2 0 * p.1 0 + p.2 1 * (p.1 1 + p.1 2)) : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  exact h'.mul h

theorem norm_chi (y : Fin 2 → ℝ) : ‖chi y‖ = ‖Phi y‖ * |y 0 - y 1| := by
  rw [chi, norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_atom_le (A : ℝ) (l : Fin 3 → ℝ) (y : Fin 2 → ℝ) : ‖atom A l y‖ ≤ ‖chi y‖ := by
  rw [atom, Circle.norm_smul, norm_chi, psi, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_hz_le _ _) (norm_nonneg _)

theorem chi_integrable : Integrable chi :=
  chi_contDiff.continuous.integrable_of_hasCompactSupport chi_compact

theorem atom_integrable (A : ℝ) (l : Fin 3 → ℝ) : Integrable (atom A l) := by
  refine chi_integrable.norm.mono' ?_ (ae_of_all _ fun y => norm_atom_le A l y)
  exact ((atom_continuous A).comp (by fun_prop : Continuous fun y : Fin 2 → ℝ => (l, y))).aestronglyMeasurable

/-- Norm of an output atom: modulation by `ν(l)` of the uniformly bounded `ψ_z`. -/
theorem atom_norm_le {θ : ℝ} (hθ0 : 0 ≤ θ) {B : ℝ≥0∞} (hB : ∀ z : ℝ, timeFourierNorm θ (psi z) ≤ B)
    (A : ℝ) (l : Fin 3 → ℝ) :
    timeFourierNorm θ (atom A l) ≤ ENNReal.ofReal (2 ^ θ) * timeWeight θ (nu l) * B :=
  (timeFourierNorm_modulate_le hθ0 (psi (A / 2 + l 1)) (nu l)).trans
    (mul_le_mul_right (hB _) _)

theorem timeBracket_nu_le (l : Fin 3 → ℝ) : timeBracket (nu l) ≤ 2 * timeBracket l := by
  have h1 := one_le_timeBracket l
  apply timeBracket_le (by linarith)
  intro j
  have hb : ∀ i, 1 + l i ^ 2 ≤ timeBracket l ^ 2 := fun i => by
    have := bracket_le_timeBracket l i
    have h0 : 0 ≤ Real.sqrt (1 + l i ^ 2) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 + l i ^ 2 by positivity)]
  fin_cases j
  · have := bracket_le_timeBracket l 0
    simp only [nu]
    simp
    linarith
  · simp only [nu]
    simp
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith, ?_⟩
    nlinarith [hb 1, hb 2, sq_nonneg (l 1 - l 2)]

theorem timeWeight_nu_le {θ : ℝ} (hθ0 : 0 ≤ θ) (l : Fin 3 → ℝ) :
    timeWeight θ (nu l) ≤ ENNReal.ofReal (2 ^ θ) * timeWeight θ l := by
  unfold timeWeight
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.mul_rpow (by norm_num) (timeBracket_pos l).le]
  exact Real.rpow_le_rpow (timeBracket_pos _).le (timeBracket_nu_le l) hθ0

end WaveTurbulence.Flower.ProtTa
