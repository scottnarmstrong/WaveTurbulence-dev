/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.AppTools
public import WaveTurbulence.Foundations.ApproxNT.Factors

/-!
# Factorization of the main term of one cell (packet NT6)

`∫ Φ̂(s) ∏ᵢ gᵢ(sᵢ) ds = (∏_{j∈J} ∫ m̂_{K_j}(t) g_j(t) dt) · ∫ Ψ̂₁(b) ∏_{i∉J} gᵢ(bᵢ) db` for the truncated
profile; with `gᵢ = cellInt_i(μ ·)` the `J`-factors are `μ⁻¹ pvTrunc_μ` (`AppTools.jfactor_eq`).
Also the one-dimensional integrals of `|cellInt(μt)|` and `|t|^θ |cellInt(μt)|`.
-/

public section

noncomputable section

open MeasureTheory Finset WithLp
open scoped ContDiff FourierTransform ENNReal

namespace WaveTurbulence.ApproxNT

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Splitting the time integral of the truncated profile into the `J` and `J^c` variables. -/
theorem integral_truncProfileHat_split (J : Finset ι) (Kj : ι → ℕ)
    (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (g : ι → ℝ → ℂ) :
    ∫ s, truncProfileHat J Kj Ψ₁ s * ∏ i, g i (s i) =
      (∏ j ∈ J, ∫ t, mKerHat (Kj j) t * g j t) *
        ∫ b : {j // j ∉ J} → ℝ, 𝓕 Ψ₁ (toLp 2 b) * ∏ i : {j // j ∉ J}, g i (b i) := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ J)
  have hpt : ∀ p : ({j // j ∈ J} → ℝ) × ({j // j ∉ J} → ℝ),
      truncProfileHat J Kj Ψ₁ (e.symm p) * ∏ i, g i (e.symm p i) =
      (∏ j : {j // j ∈ J}, mKerHat (Kj j) (p.1 j) * g j (p.1 j)) *
        (𝓕 Ψ₁ (toLp 2 p.2) * ∏ i : {j // j ∉ J}, g i (p.2 i)) := by
    intro p
    have hsplit : truncProfileHat J Kj Ψ₁ (e.symm p) =
        (∏ j : {j // j ∈ J}, mKerHat (Kj j) ((e (e.symm p)).1 j)) *
          𝓕 Ψ₁ (toLp 2 (e (e.symm p)).2) := by
      rw [truncProfileHat, ← prod_coe_sort J]
      rfl
    rw [hsplit, e.apply_symm_apply, ← prod_mul_prod_compl J (fun i => g i (e.symm p i)),
      ← prod_coe_sort J, prod_subtype Jᶜ (p := (· ∉ J)) (fun x => by simp), prod_mul_distrib]
    have h1 : ∀ i : {j // j ∈ J}, e.symm p i = p.1 i := fun i => by
      rw [piSplit_symm_apply]; simp [i.2]
    have h2 : ∀ i : {j // j ∉ J}, e.symm p i = p.2 i := fun i => by
      rw [piSplit_symm_apply]; simp [i.2]
    simp_rw [h1, h2]
    ring
  rw [integral_split_J J]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun p => hpt p)).trans ?_
  have hpm := integral_prod_mul (μ := (volume : Measure ({j // j ∈ J} → ℝ)))
    (ν := (volume : Measure ({j // j ∉ J} → ℝ)))
    (fun a => ∏ j : {j // j ∈ J}, mKerHat (Kj j) (a j) * g j (a j))
    (fun b => 𝓕 Ψ₁ (toLp 2 b) * ∏ i : {j // j ∉ J}, g i (b i))
  refine hpm.trans ?_
  rw [integral_fintype_prod_volume_eq_prod
    (f := fun (j : {j // j ∈ J}) (t : ℝ) => mKerHat (Kj j) t * g j t), ← prod_coe_sort J]

variable {d : ℕ}

theorem lintegral_cellInt_scale_le (hd : 2 ≤ d) {μ : ℝ} (hμ : 0 < μ) (p q ξ η : Mom d) :
    ∫⁻ t, ‖cellInt p q ξ η (μ * t)‖ₑ ≤ ENNReal.ofReal (μ⁻¹ * (cellK0 d * NTSP.sInt d)) := by
  have hc := lintegral_comp_mul hμ (continuous_cellInt p q ξ η).enorm.measurable
  rw [hc, ENNReal.ofReal_mul (inv_nonneg.2 hμ.le)]
  exact mul_le_mul_of_nonneg_left (lintegral_cellInt_le hd p q ξ η) zero_le

theorem lintegral_rpow_cellInt_scale_le (hd : 3 ≤ d) {μ θ : ℝ} (hμ : 0 < μ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (p q ξ η : Mom d) :
    ∫⁻ t, ENNReal.ofReal (|t| ^ θ) * ‖cellInt p q ξ η (μ * t)‖ₑ ≤
      ENNReal.ofReal (μ⁻¹ * μ ^ (-θ) * (cellK0 d * NTSP.sInt (d - 1))) := by
  have hm : Measurable fun u => ENNReal.ofReal (|u / μ| ^ θ) * ‖cellInt p q ξ η u‖ₑ :=
    (ENNReal.measurable_ofReal.comp ((continuous_abs.comp (continuous_id.div_const μ)).rpow_const
      (fun _ => Or.inr hθ0)).measurable).mul (continuous_cellInt p q ξ η).enorm.measurable
  have hc := lintegral_comp_mul hμ hm
  simp only [mul_div_cancel_left₀ _ hμ.ne'] at hc
  rw [hc]
  have hK := cellK0_nonneg d
  have hbound : ∀ u : ℝ, ENNReal.ofReal (|u / μ| ^ θ) * ‖cellInt p q ξ η u‖ₑ ≤
      ENNReal.ofReal (μ ^ (-θ) * cellK0 d * ((1 + |u|) ^ (d - 1))⁻¹) := by
    intro u
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := norm_cellInt_le p q ξ η u
    have hpos : 0 < 1 + |u| := by positivity
    have h2 : |u / μ| ^ θ = μ ^ (-θ) * |u| ^ θ := by
      rw [abs_div, abs_of_pos hμ, Real.div_rpow (abs_nonneg _) hμ.le, Real.rpow_neg hμ.le,
        div_eq_inv_mul]
    have h3 : |u| ^ θ ≤ 1 + |u| := by
      rcases le_total |u| 1 with h | h
      · calc |u| ^ θ ≤ 1 := Real.rpow_le_one (abs_nonneg _) h hθ0
          _ ≤ 1 + |u| := by linarith [abs_nonneg u]
      · calc |u| ^ θ ≤ |u| ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hθ1
          _ ≤ 1 + |u| := by rw [Real.rpow_one]; linarith
    have hpow : (1 + |u|) ^ d = (1 + |u|) * (1 + |u|) ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2]
    calc μ ^ (-θ) * |u| ^ θ * ‖cellInt p q ξ η u‖
        ≤ μ ^ (-θ) * (1 + |u|) * (cellK0 d * ((1 + |u|) ^ d)⁻¹) := by
          gcongr
    _ = μ ^ (-θ) * cellK0 d * ((1 + |u|) ^ (d - 1))⁻¹ := by
          rw [hpow]; field_simp
  calc ENNReal.ofReal μ⁻¹ * ∫⁻ u, ENNReal.ofReal (|u / μ| ^ θ) * ‖cellInt p q ξ η u‖ₑ
      ≤ ENNReal.ofReal μ⁻¹ * ENNReal.ofReal (μ ^ (-θ) * cellK0 d * NTSP.sInt (d - 1)) := by
        gcongr
        exact NTSP.lintegral_le_of_le_inv_pow (by omega)
          (mul_nonneg (Real.rpow_nonneg hμ.le _) hK) hbound
    _ = _ := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hμ.le)]
        congr 1; ring

end WaveTurbulence.ApproxNT
