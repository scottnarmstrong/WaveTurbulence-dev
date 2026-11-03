/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.NTOmegainv

/-!
# The coordinate-derivative premises of DH21 Lemma 6.3

The source's (NTphibounds), L1186–L1189, includes the zeroth-order and first
coordinate derivatives in the second momentum. A finite-dimensional basis
bound and the mean value theorem turn these source premises into the
Lipschitz bounds used in the proof. No integral estimate is an assumption.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence

variable {d : ℕ}

/-- DH21 Lemma 6.3(1) from the source's zeroth and first-coordinate derivative
bounds. The higher derivatives in (NTphibounds) are not needed for this result. -/
theorem dh21_inverse_resonance_bound_of_coordinate_derivatives
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {ρ σ : Mom d → ℝ} (hρ : ContDiff ℝ 1 ρ) (hσ : ContDiff ℝ 1 σ)
    (hρc : HasCompactSupport ρ) (hσc : HasCompactSupport σ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (D : ℝ≥0) (scale : ℝ), 1 ≤ scale →
      ∀ (a b : Mom d) (Θ : Mom d → Mom d → ℂ),
      Continuous (Function.uncurry Θ) → (∀ x, Differentiable ℝ (Θ x)) →
      (∀ x y, ‖Θ x y‖ ≤ D) →
      (∀ x y (j : Fin d), ‖fderiv ℝ (Θ x) y (EuclideanSpace.single j 1)‖ ≤ D) →
      ∀ ξ η : Mom d,
      (∀ μ : ℝ, 0 < μ →
        ‖bilinearFourierTruncation χ μ (localizedAmplitude ρ σ Θ scale a b) ξ η‖ ≤
          M * (D : ℝ) * scale ^ (2 * d)) ∧
      ∃ v : ℂ, Tendsto
        (fun μ => bilinearFourierTruncation χ μ (localizedAmplitude ρ σ Θ scale a b) ξ η)
        atTop (𝓝 v) ∧ ‖v‖ ≤ M * (D : ℝ) * scale ^ (2 * d) := by
  let v := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  obtain ⟨K, _hK, hKb⟩ := v.exists_opNNNorm_le (F := ℂ)
  let B : ℝ≥0 := max K 1
  have hB : 1 ≤ B := le_max_right _ _
  obtain ⟨M, hM, hmain⟩ := dh21_inverse_resonance_bound hd hχ hχs hρ hσ hρc hσc
  have hBreal : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBp : (0 : ℝ) < (B : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hBreal
  refine ⟨M * (B : ℝ), mul_pos hM hBp, ?_⟩
  intro D scale hscale a b Θ hΘc hΘd hΘb hΘcoord ξ η
  have hDb : D ≤ B * D := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hB (show (0 : ℝ≥0) ≤ D from bot_le)
  have hΘb' : ∀ x y, ‖Θ x y‖ ≤ (B * D : ℝ≥0) := fun x y =>
    (hΘb x y).trans (by exact_mod_cast hDb)
  have hΘL : ∀ x, LipschitzWith (B * D) (Θ x) := by
    intro x
    apply lipschitzWith_of_nnnorm_fderiv_le (hΘd x)
    intro y
    have hc : ∀ j : Fin d, ‖fderiv ℝ (Θ x) y (v j)‖₊ ≤ D := by
      intro j
      change ‖fderiv ℝ (Θ x) y (v j)‖ ≤ (D : ℝ)
      simpa only [v, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hΘcoord x y j
    exact (hKb D hc).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (show (0 : ℝ≥0) ≤ D from bot_le))
  obtain ⟨hfinite, z, hz, hzb⟩ := hmain (B * D) scale hscale a b Θ hΘc hΘb' hΘL ξ η
  have he : M * ((B * D : ℝ≥0) : ℝ) * scale ^ (2 * d) =
      (M * (B : ℝ)) * (D : ℝ) * scale ^ (2 * d) := by
    push_cast
    ring
  exact ⟨fun μ hμ => (hfinite μ hμ).trans_eq he, z, hz, hzb.trans_eq he⟩

end WaveTurbulence
