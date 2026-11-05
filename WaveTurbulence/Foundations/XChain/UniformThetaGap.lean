/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.RemainderScaleAbsorption
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! One positive scale gap controls every induction stage of the spatial remainder. -/
@[expose] public section
namespace WaveTurbulence.Induct

noncomputable def uniformThetaGap (P : WTParams) : ℝ := P.η ^ 20 * (2 : ℝ)⁻¹ ^ P.D / 5

theorem uniformThetaGap_pos (P : WTParams) (hη : 0 < P.η) : 0 < uniformThetaGap P := by
  unfold uniformThetaGap
  positivity

theorem uniformThetaGap_le (P : WTParams) {p : ℕ} (hp : p < P.D) :
    uniformThetaGap P ≤ (4 * P.theta (p + 1) + P.theta p) / 5 - P.theta (p + 1) := by
  have hpow : (2 : ℝ)⁻¹ ^ P.D ≤ (2 : ℝ)⁻¹ ^ (p + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h := mul_le_mul_of_nonneg_left hpow (pow_nonneg (sq_nonneg P.η) 10)
  rw [← pow_mul] at h
  unfold uniformThetaGap WTParams.theta
  rw [pow_succ ((2 : ℝ)⁻¹) p] at h ⊢
  nlinarith

theorem uniformThetaGap_scale (P : WTParams) (hη : 0 < P.η) {p : ℕ} (hp : p < P.D)
    (hL : Real.exp (Real.log 4 / uniformThetaGap P) ≤ P.L) :
    4 ≤ P.L ^ ((4 * P.theta (p + 1) + P.theta p) / 5 - P.theta (p + 1)) := by
  have hg := uniformThetaGap_pos P hη
  have hLpos : 0 < P.L := (Real.exp_pos _).trans_le hL
  have hlog : Real.log 4 / uniformThetaGap P ≤ Real.log P.L := by
    exact (Real.exp_le_exp.mp (hL.trans_eq (Real.exp_log hLpos).symm))
  have hm : Real.log 4 ≤ Real.log P.L * uniformThetaGap P :=
    (div_le_iff₀ hg).mp hlog
  have hlog0 : 0 ≤ Real.log P.L :=
    (div_nonneg (Real.log_nonneg (by norm_num)) hg.le).trans hlog
  rw [Real.rpow_def_of_pos hLpos]
  calc
    4 = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hm.trans (mul_le_mul_of_nonneg_left
      (uniformThetaGap_le P hp) hlog0))

end WaveTurbulence.Induct
