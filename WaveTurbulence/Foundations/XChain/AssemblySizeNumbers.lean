/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.StageSizeThreshold
public import WaveTurbulence.Foundations.XChain.UniformThetaGap
/-! One fixed-data lower threshold supplies every numerical stage condition in the assembly. -/
@[expose] public section
namespace WaveTurbulence.Induct

theorem theta_le_zero (P : WTParams) (p : ℕ) : P.theta p ≤ P.theta 0 := by
  have hpow : (2 : ℝ)⁻¹ ^ p ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold WTParams.theta
  simp only [pow_zero]
  have hη : 0 ≤ P.η ^ 20 := by positivity
  nlinarith

noncomputable def assemblySizeK (P : WTParams) (Cmom : ℕ) : ℝ :=
  max 2000000 (max (2 * P.d + 4 : ℕ)
    (max (1000 * ((2 * (Cmom + 2) + 2) ^ 2 + 1) : ℕ) (P.theta 0)))

noncomputable def assemblySizeThreshold (P : WTParams) (C : ℝ) (Cmom : ℕ) : ℝ :=
  max (stageSizeThreshold P (max C (P.C₂ / (1 - P.C₁ * P.δ))) (assemblySizeK P Cmom))
    (Real.exp (Real.log 4 / uniformThetaGap P))

theorem assembly_stage_sizes (P : WTParams) (hd : 1 ≤ P.d) (hη : 0 < P.η)
    (C : ℝ) (Cmom : ℕ) (hsize : assemblySizeThreshold P C Cmom ≤ P.L) :
    Real.exp 2 ≤ P.L ∧ C ≤ P.L ∧ baseLatticeSum P.d ≤ P.L ∧
      ∀ p, p < P.D →
        2000000 ≤ P.N (p + 1) ∧ 2 * P.d + 4 ≤ P.N (p + 1) ∧
        (P.Lambda p : ℝ) / 4 ≤ P.N (p + 1) ∧
        1000 * ((2 * (Cmom + 2) + 2) ^ 2 + 1) ≤ P.R (p + 1) ∧
        P.theta (p + 1) ≤ P.N (p + 1) ∧ Real.log P.L ≤ P.N (p + 1) ∧
        P.C₂ / (1 - P.C₁ * P.δ) ≤ Real.exp (P.N (p + 1) : ℝ) ∧
        4 ≤ P.L ^ ((4 * P.theta (p + 1) + P.theta p) / 5 - P.theta (p + 1)) := by
  have hs := stage_sizes_of_threshold P hd (max C (P.C₂ / (1 - P.C₁ * P.δ))) (assemblySizeK P Cmom)
    ((le_max_left _ _).trans hsize)
  have hC := (le_max_left C _).trans hs.2.1
  refine ⟨hs.1, hC, hs.2.2.1, fun p hp => ?_⟩
  have hkN := (hs.2.2.2 (p + 1)).2.1
  have hkR := (hs.2.2.2 (p + 1)).1
  have hN : (2000000 : ℝ) ≤ P.N (p + 1) := (le_max_left _ _).trans hkN
  have hNd : ((2 * P.d + 4 : ℕ) : ℝ) ≤ P.N (p + 1) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hkN)
  have hR : ((1000 * ((2 * (Cmom + 2) + 2) ^ 2 + 1) : ℕ) : ℝ) ≤ P.R (p + 1) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hkR))
  have hθ : P.theta 0 ≤ P.N (p + 1) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hkN))
  have hlog := log_le_N P hd hs.1 (p + 1)
  have hA : P.C₂ / (1 - P.C₁ * P.δ) ≤ P.L := (le_max_right _ _).trans hs.2.1
  have hL0 : 0 < P.L := (Real.exp_pos 2).trans_le hs.1
  have hLe : P.L ≤ Real.exp (P.N (p + 1) : ℝ) := by
    exact (Real.exp_log hL0).symm.trans_le (Real.exp_le_exp.mpr hlog)
  have hS : stageSizeThreshold P (max C (P.C₂ / (1 - P.C₁ * P.δ))) (assemblySizeK P Cmom) ≤ P.L :=
    (le_max_left _ _).trans hsize
  have heL : Real.exp (max 2 (max (assemblySizeK P Cmom) (P.Lambda 0 : ℝ))) ≤ P.L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hS))
  have hΛlog : (P.Lambda 0 : ℝ) ≤ Real.log P.L := by
    apply (Real.le_log_iff_exp_le hL0).mpr
    exact (Real.exp_le_exp.mpr ((le_max_right _ _).trans (le_max_right _ _))).trans heL
  have hΛp : (P.Lambda p : ℝ) ≤ P.Lambda 0 := by exact_mod_cast lambda_le_zero P hd p
  have hΛpos : (0 : ℝ) ≤ P.Lambda p := Nat.cast_nonneg _
  have hbp : (P.Lambda p : ℝ) / 4 ≤ P.N (p + 1) := by linarith
  exact ⟨by exact_mod_cast hN, by exact_mod_cast hNd, hbp,
    by exact_mod_cast hR, (theta_le_zero P _).trans hθ, hlog, hA.trans hLe,
    uniformThetaGap_scale P hη hp ((le_max_right _ _).trans hsize)⟩

end WaveTurbulence.Induct
