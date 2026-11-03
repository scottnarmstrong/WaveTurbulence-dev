/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.NTOmegainvCoordinate
public import WaveTurbulence.Foundations.Resonant.NTOmegainvSmallEnergy

/-!
# DH21 Lemma 6.3: the square-torus source form

Both conclusions share one constant, chosen before the amplitude, its bound,
all centers, scales and Fourier frequencies. Frequencies are multiplied by
`2π` so the phase is exactly the source's `e(z)=exp(2πiz)`.
Only the zeroth and first second-momentum coordinate bounds from
(NTphibounds) are needed; the source's higher derivatives are stronger.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- DH21 Lemma 6.3, L1305–L1367, for the square torus (campaign D2).
The low-energy expression is characterized as a principal-value cutoff limit. -/
theorem dh21_lemma_6_3_square
    (hd : 3 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {ρ σ : Mom d → ℝ} (hρ : ContDiff ℝ 1 ρ) (hσ : ContDiff ℝ 1 σ)
    (hρc : HasCompactSupport ρ) (hσc : HasCompactSupport σ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (D : ℝ≥0) (scale : ℝ), 1 ≤ scale →
      ∀ (a b : Mom d) (Θ : Mom d → Mom d → ℂ),
      Continuous (Function.uncurry Θ) → (∀ x, Differentiable ℝ (Θ x)) →
      (∀ x y, ‖Θ x y‖ ≤ D) →
      (∀ x y (j : Fin d), ‖fderiv ℝ (Θ x) y (EuclideanSpace.single j 1)‖ ≤ D) →
      ∀ ξ η : Mom d,
      (∀ μ : ℝ, 1 < μ →
        ‖bilinearFourierTruncation χ μ (localizedAmplitude ρ σ Θ scale a b)
          ((2 * Real.pi) • ξ) ((2 * Real.pi) • η)‖ ≤ M * (D : ℝ) * scale ^ (2 * d)) ∧
      (∃ v : ℂ, Tendsto
        (fun μ => bilinearFourierTruncation χ μ (localizedAmplitude ρ σ Θ scale a b)
          ((2 * Real.pi) • ξ) ((2 * Real.pi) • η)) atTop (𝓝 v) ∧
          ‖v‖ ≤ M * (D : ℝ) * scale ^ (2 * d)) ∧
      ∀ μ : ℝ, 1 < μ → ∃ w : ℂ, Tendsto
        (fun ν => lowBilinearFourierTruncation χ ν μ (localizedAmplitude ρ σ Θ scale a b)
          ((2 * Real.pi) • ξ) ((2 * Real.pi) • η)) atTop (𝓝 w) ∧
        ‖w‖ ≤ M * (D : ℝ) * scale ^ (2 * d) * μ⁻¹ * (1 + ‖ξ‖ + ‖η‖) := by
  classical
  let b₀ := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  obtain ⟨K, _hK, hKb⟩ := b₀.exists_opNNNorm_le (F := ℂ)
  let B : ℝ≥0 := max K 1
  have hB : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (show (1 : ℝ≥0) ≤ B from le_max_right _ _)
  obtain ⟨M₁, hM₁, hmain₁⟩ := dh21_inverse_resonance_bound_of_coordinate_derivatives
    (by omega : 2 ≤ d) hχ hχs hρ hσ hρc hσc
  obtain ⟨M₂, hM₂, hmain₂⟩ := dh21_small_energy_bound hd hχ hχs hρ hσ hρc hσc
  let P : ℝ := M₂ * (B : ℝ) * (1 + 2 * Real.pi)
  let M : ℝ := M₁ + P
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hM₁M : M₁ ≤ M := by dsimp [M]; linarith only [hP]
  have hPM : P ≤ M := by dsimp [M]; linarith only [hM₁]
  refine ⟨M, hM, ?_⟩
  intro D scale hscale a b Θ hΘc hΘd hΘb hΘcoord ξ η
  have hDb : D ≤ B * D := by
    exact_mod_cast (show (D : ℝ) ≤ (B : ℝ) * (D : ℝ) from le_mul_of_one_le_left D.coe_nonneg hB)
  have hΘb' : ∀ x y, ‖Θ x y‖ ≤ (B * D : ℝ≥0) := fun x y => (hΘb x y).trans (by exact_mod_cast hDb)
  have hΘL : ∀ x, LipschitzWith (B * D) (Θ x) := by
    intro x
    apply lipschitzWith_of_nnnorm_fderiv_le (hΘd x)
    intro y
    have hc : ∀ j : Fin d, ‖fderiv ℝ (Θ x) y (b₀ j)‖₊ ≤ D := by
      intro j
      change ‖fderiv ℝ (Θ x) y (b₀ j)‖ ≤ (D : ℝ)
      simpa only [b₀, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hΘcoord x y j
    exact (hKb D hc).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (show (0 : ℝ≥0) ≤ D from bot_le))
  obtain ⟨hfinite, z, hz, hzb⟩ := hmain₁ D scale hscale a b Θ hΘc hΘd hΘb hΘcoord
    ((2 * Real.pi) • ξ) ((2 * Real.pi) • η)
  have hbound₁ : M₁ * (D : ℝ) * scale ^ (2 * d) ≤ M * (D : ℝ) * scale ^ (2 * d) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM₁M D.coe_nonneg) (by positivity)
  refine ⟨fun μ hμ => (hfinite μ (by linarith)).trans hbound₁, ⟨z, hz, hzb.trans hbound₁⟩, ?_⟩
  intro μ hμ
  have hμp : 0 < μ := by linarith
  obtain ⟨w, hw, hwb⟩ := hmain₂ (B * D) scale hscale a b Θ hΘc hΘb' hΘL μ hμp
    ((2 * Real.pi) • ξ) ((2 * Real.pi) • η)
  refine ⟨w, hw, hwb.trans ?_⟩
  have hfreq : 1 + ‖(2 * Real.pi) • ξ‖ + ‖(2 * Real.pi) • η‖ ≤
      (1 + 2 * Real.pi) * (1 + ‖ξ‖ + ‖η‖) := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith only [Real.pi_pos, norm_nonneg ξ, norm_nonneg η]
  have hcoef : 0 ≤ M₂ * ((B * D : ℝ≥0) : ℝ) * scale ^ (2 * d) * μ⁻¹ := by positivity
  have he : M₂ * ((B * D : ℝ≥0) : ℝ) * scale ^ (2 * d) * μ⁻¹ *
      ((1 + 2 * Real.pi) * (1 + ‖ξ‖ + ‖η‖)) =
      P * (D : ℝ) * scale ^ (2 * d) * μ⁻¹ * (1 + ‖ξ‖ + ‖η‖) := by
    dsimp [P]
    push_cast
    ring
  refine (mul_le_mul_of_nonneg_left hfreq hcoef).trans ?_
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPM D.coe_nonneg) (by positivity))
      (by positivity)) (by positivity)

end WaveTurbulence.Resonant
