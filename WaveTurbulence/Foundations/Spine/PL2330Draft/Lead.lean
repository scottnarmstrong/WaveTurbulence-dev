/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Step
public import WaveTurbulence.Foundations.XChain.SNormOperations

/-!
# Leading terms: separated sums `∑_Z M_Z(k) J(t)` in the derivative norms (PL23-30D)

* `spatialNorm_const_mul_le`, `SNorm_const_mul_bound`: a complex constant multiple;
* `rN_lead_le`: `𝔛^{θ,Λ,a}(∑_{Z∈S} M_Z(k) J(t)) ≤ |S| L max‖M_Z‖_{𝔖^{Λ,a}} 𝔛^{θ,Λ,0}(J)`.
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref WaveTurbulence.NormBridgeScratch

variable {r d : ℕ}

theorem momentumSupNorm_const_mul (Λ₂ : ℕ) (u : ℂ) (g : Mom d → ℂ) :
    momentumSupNorm Λ₂ (fun k => u * g k) = ‖u‖ₑ * momentumSupNorm Λ₂ g := by
  unfold momentumSupNorm
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun k => ?_
  rw [enorm_mul]
  ring

theorem spatialNorm_zero_fun (Λ Λ₂ : ℕ) : spatialNorm Λ Λ₂ (fun _ : Mom d => (0 : ℂ)) = 0 := by
  unfold spatialNorm
  simp only [(contDiff_const : ContDiff ℝ Λ fun _ : Mom d => (0 : ℂ)), or_true, ite_true]
  refine le_antisymm (iSup₂_le fun n _ => iSup_le fun ρ => ?_) zero_le
  simp [momentumDerivative_zero_fun, momentumSupNorm]

theorem spatialNorm_const_mul_le {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0) (u : ℂ) (f : Mom d → ℂ) :
    spatialNorm Λ Λ₂ (fun k => u * f k) ≤ ‖u‖ₑ * spatialNorm Λ Λ₂ f := by
  by_cases hu : u = 0
  · subst hu
    have h0 : (fun k => (0 : ℂ) * f k) = fun _ => 0 := by funext k; simp
    rw [h0]
    unfold spatialNorm
    simp only [hΛ, false_or, (contDiff_const : ContDiff ℝ Λ fun _ : Mom d => (0 : ℂ)), ite_true]
    refine le_trans (iSup₂_le fun n _ => iSup_le fun ρ => ?_) zero_le
    simp [momentumDerivative_zero_fun, momentumSupNorm]
  by_cases hf : ContDiff ℝ Λ f
  · have hfu : ContDiff ℝ Λ (fun k => u * f k) := hf.const_smul u
    unfold spatialNorm
    simp only [hΛ, false_or, hf, hfu, ite_true]
    refine iSup₂_le fun n hn => iSup_le fun ρ => ?_
    rw [momentumDerivative_const_mul hn ρ u hf, momentumSupNorm_const_mul]
    exact mul_le_mul_right (le_iSup₂_of_le n hn (le_iSup (fun ρ : Fin n → Fin d =>
      momentumSupNorm Λ₂ (momentumDerivative ρ f)) ρ)) _
  · have : spatialNorm Λ Λ₂ f = ⊤ := by
      unfold spatialNorm
      simp [hΛ, hf]
    rw [this, ENNReal.mul_top (by simpa using hu)]
    exact le_top

theorem SNorm_const_mul_bound {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0) (u : ℂ) (f : Mom d → ℂ) {C : ℝ}
    (h : SNorm Λ Λ₂ f ≤ ENNReal.ofReal C) : SNorm Λ Λ₂ (fun k => u * f k) ≤ ENNReal.ofReal (‖u‖ * C) := by
  rw [SNorm_eq_spatialNorm] at h ⊢
  refine (spatialNorm_const_mul_le hΛ u f).trans ?_
  rw [ENNReal.ofReal_mul (norm_nonneg u), ofReal_norm]
  exact mul_le_mul_right h _

/-- **A separated sum** `∑_{Z ∈ S} M_Z(k) J(t)`. -/
theorem rN_lead_le {θ : ℝ} {Λ : ℕ} (hΛ : Λ ≠ 0) (hd : 1 ≤ d) (a₀ : ℕ) {ι : Type*} (S : Finset ι)
    (B : Set (Fin r → ℝ)) (M : ι → Mom d → ℂ) (J : (Fin r → ℝ) → ℂ) {m j : ℝ} (hm : 0 ≤ m)
    (_hj : 0 ≤ j) (hM : ∀ Z ∈ S, spatialNorm Λ a₀ (M Z) ≤ ENNReal.ofReal m)
    (hJ : rN θ Λ 0 B (fun t (_ : Mom d) => J t) ≤ ENNReal.ofReal j) {n : ℕ} (hS : S.card ≤ 2 ^ n) :
    rN θ Λ a₀ B (fun t k => ∑ Z ∈ S, M Z k * J t) ≤ ENNReal.ofReal (2 ^ n * (cLeib d Λ * m * j)) := by
  have hL := cLeib_nonneg d Λ
  refine (restr_finsetSum_le hΛ S B Set.univ (fun Z t k => M Z k * J t)).trans ?_
  have hterm : ∀ Z ∈ S, rN θ Λ a₀ B (fun t k => M Z k * J t) ≤ ENNReal.ofReal (cLeib d Λ * m * j) := by
    intro Z hZ
    exact restr_mul_w_le hΛ hd (θ := θ) a₀ B (c := M Z) (fun t _ => J t) hm (hM Z hZ) hJ
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  calc (S.card : ℝ≥0∞) * ENNReal.ofReal (cLeib d Λ * m * j)
      ≤ 2 ^ n * ENNReal.ofReal (cLeib d Λ * m * j) := by gcongr; exact_mod_cast hS
    _ = ENNReal.ofReal (2 ^ n * (cLeib d Λ * m * j)) := by
        rw [show (2 : ℝ≥0∞) ^ n = ENNReal.ofReal (2 ^ n) by
          rw [ENNReal.ofReal_pow (by norm_num)]; simp, ← ENNReal.ofReal_mul (by positivity)]

end WaveTurbulence.PL2330
