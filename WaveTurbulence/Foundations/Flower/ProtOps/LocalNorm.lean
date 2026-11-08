/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOps.LocalDeriv
public import WaveTurbulence.Foundations.Spine.RA1LW.XNormBridge
public import WaveTurbulence.Foundations.Regref.TraceDeriv
public import WaveTurbulence.Foundations.Sumint.TimeBridge

/-! # PROT-OPS: the `X^{θ,N,0}` norm of a superposition of bumps -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence MeasureTheory WaveTurbulence.Fourier
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.ProtOps

variable {d : ℕ} {r : ℕ}

/-- `∑_j g_j(t) psi(L (k - j))`. -/
def superpose (L : ℝ) (S : Finset (Mom d)) (g : Mom d → (Fin r → ℝ) → ℂ) (t : Fin r → ℝ) (y : Mom d) : ℂ :=
  ∑ j ∈ S, g j t * psiT d L j y

theorem mixedTimeFourier_superpose (L : ℝ) (S : Finset (Mom d)) (g : Mom d → (Fin r → ℝ) → ℂ)
    (hg : ∀ j ∈ S, Integrable (g j)) (ξ : Fin r → ℝ) :
    mixedTimeFourier (superpose L S g) ξ = fun y => ∑ j ∈ S, timeFourier (g j) ξ * psiT d L j y := by
  funext y
  have := congrFun (timeFourier_finsum S g hg (fun j => psiT d L j y)) ξ
  exact this

theorem norm_word_le {N n : ℕ} {B : ℝ} (hB : ∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n (psi d) x‖ ≤ B)
    {L : ℝ} (hL : 1 ≤ L) (S : Finset (Mom d)) (c : Mom d → ℂ) (hn : n ≤ N) (ρ : Fin n → Fin d) (k : Mom d) :
    ‖iteratedFDeriv ℝ n (fun y => ∑ j ∈ S, c j * psiT d L j y) k (fun i => EuclideanSpace.single (ρ i) 1)‖ ≤
      L ^ N * B * ∑ j ∈ S, ‖c j‖ := by
  have hcd : ∀ j ∈ S, ContDiffAt ℝ n (fun y => c j * psiT d L j y) k := fun j _ =>
    (contDiff_const.mul (psiT_contDiff d L j)).contDiffAt
  rw [iteratedFDeriv_fun_sum_apply hcd]
  have hterm : ∀ j ∈ S, iteratedFDeriv ℝ n (fun y => c j * psiT d L j y) k =
      c j • iteratedFDeriv ℝ n (psiT d L j) k := fun j _ => by
    have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := c j) (i := n) (f := psiT d L j) (x := k)
      (psiT_contDiff d L j).contDiffAt
    simpa only [smul_eq_mul] using this
  rw [Finset.sum_congr rfl hterm, sum_apply]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  calc ‖∑ j ∈ S, (c j • iteratedFDeriv ℝ n (psiT d L j) k) fun i => EuclideanSpace.single (ρ i) 1‖
      ≤ ∑ j ∈ S, ‖(c j • iteratedFDeriv ℝ n (psiT d L j) k) fun i => EuclideanSpace.single (ρ i) 1‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ S, ‖c j‖ * (L ^ N * B) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [smul_apply, norm_smul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
        have h1 : ∏ i, ‖(EuclideanSpace.single (ρ i) (1 : ℝ) : Mom d)‖ = 1 :=
          Finset.prod_eq_one fun i _ => by simp
        rw [h1, mul_one]
        exact norm_iteratedFDeriv_psiT_le hB hL j hn k
    _ = L ^ N * B * ∑ j ∈ S, ‖c j‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem XNorm_superpose_le {N : ℕ} {B : ℝ} (hB : ∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n (psi d) x‖ ≤ B)
    {L : ℝ} (hL : 1 ≤ L) (S : Finset (Mom d)) (g : Mom d → (Fin r → ℝ) → ℂ)
    (hg : ∀ j ∈ S, Integrable (g j)) (θ : ℝ) :
    XNorm θ N 0 (superpose L S g) ≤ ENNReal.ofReal (L ^ N * B) * ∑ j ∈ S, timeFourierNorm θ (g j) := by
  rw [RA1Leafwise.XNorm_eq_mixedFourierNorm]
  have hadm : MixedFourierAdmissible N (superpose L S g) := by
    refine ⟨fun y => ?_, Or.inr (ae_of_all _ fun ξ => ?_)⟩
    · exact integrable_finsetSum _ fun j hj => (hg j hj).mul_const _
    · rw [mixedTimeFourier_superpose L S g hg ξ]
      exact ContDiff.sum fun j _ => contDiff_const.mul (psiT_contDiff d L j)
  rw [Regref.mixedFourierNorm_eq_iSup hadm]
  refine iSup₂_le fun n hn => iSup_le fun ρ => ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  have hpt : ∀ ξ, momentumSupNorm 0 (momentumDerivative ρ (mixedTimeFourier (superpose L S g) ξ)) ≤
      ENNReal.ofReal (L ^ N * B) * ∑ j ∈ S, ‖timeFourier (g j) ξ‖ₑ := by
    intro ξ
    refine iSup_le fun k => ?_
    have hw := norm_word_le hB hL S (fun j => timeFourier (g j) ξ) hn ρ k
    have hm : momentumDerivative ρ (mixedTimeFourier (superpose L S g) ξ) k =
        iteratedFDeriv ℝ n (fun y => ∑ j ∈ S, timeFourier (g j) ξ * psiT d L j y) k
          (fun i => EuclideanSpace.single (ρ i) 1) := by
      unfold momentumDerivative
      rw [mixedTimeFourier_superpose L S g hg ξ]
    simp only [momentumBracket, pow_zero, ENNReal.ofReal_one, one_mul]
    rw [hm, ← ofReal_norm_eq_enorm]
    refine (ENNReal.ofReal_le_ofReal hw).trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    simp only [ofReal_norm_eq_enorm, ge_iff_le, le_refl]
  have hme : ∀ j ∈ S, Measurable fun ξ => ‖timeFourier (g j) ξ‖ₑ := fun j hj =>
    (timeFourier_continuous (hg j hj)).measurable.enorm
  calc ∫⁻ ξ, timeWeight θ ξ * momentumSupNorm 0 (momentumDerivative ρ (mixedTimeFourier (superpose L S g) ξ))
      ≤ ∫⁻ ξ, ENNReal.ofReal (L ^ N * B) * ∑ j ∈ S, timeWeight θ ξ * ‖timeFourier (g j) ξ‖ₑ := by
        refine lintegral_mono fun ξ => ?_
        calc _ ≤ timeWeight θ ξ * (ENNReal.ofReal (L ^ N * B) * ∑ j ∈ S, ‖timeFourier (g j) ξ‖ₑ) :=
              mul_le_mul_right (hpt ξ) _
          _ = _ := by rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ = ENNReal.ofReal (L ^ N * B) * ∑ j ∈ S, timeFourierNorm θ (g j) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum]
        · congr 1
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [timeFourierNorm_eq_lintegral (hg j hj)]
        · exact fun j hj => (timeWeight_measurable θ).mul (hme j hj)

end WaveTurbulence.Flower.ProtOps
