/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AssemblySizeNumbers
public import WaveTurbulence.Foundations.XChain.SmallDeltaConsequences
public import WaveTurbulence.Foundations.XChain.UniformPhiWeights
public import WaveTurbulence.Foundations.XChain.NextRemainderAbsorption
public import WaveTurbulence.Foundations.XChain.ExponentialScaleBound
/-! Fixed standing data, the exact three gate bodies, and explicit numerical choices for the finite induction. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Set
open scoped ENNReal
universe u

structure InductContext (P : WTParams) where
  dimension : 1 ≤ P.d
  eta_pos : 0 < P.η
  delta_pos : 0 < P.δ
  delta_le_one : P.δ ≤ 1
  nu_nonneg : 0 ≤ P.ν
  gamma_le_dimension : P.γ ≤ (P.d : ℝ)
  C1_nonneg : 0 ≤ P.C₁
  C2_nonneg : 0 ≤ P.C₂
  time_range : P.δ * P.D ≤ P.τstar
  initial_nonneg : ∀ k, 0 ≤ P.φin k
  wke : IsWKESolution P.φin P.τstar P.φ
  layergarden : LayergardenBody P
  fixedpoint : FixedpointBody.{u} P
  taylor : WkeTaylorBody P
  B : ℝ
  B_ge_one : 1 ≤ B
  phi_bound : ∀ t ∈ Icc 0 P.τstar, ∀ k, |P.φ t k| ≤ B * jbr k ^ (-(4 * P.Lambda 0 : ℝ))
  Cmom : ℕ
  Cmom_ge : B + 4 ≤ Cmom
  size : assemblySizeThreshold P (B + 1) Cmom ≤ P.L
  small_delta : P.δ ^ (P.ν / 2) ≤ Real.exp (-4000000)
  small_taylor : P.C₁ * P.δ ≤ Real.exp (-1)

namespace InductContext
variable {P : WTParams} (H : InductContext.{u} P)
include H

theorem sizes : Real.exp 2 ≤ P.L ∧ H.B + 1 ≤ P.L ∧ baseLatticeSum P.d ≤ P.L ∧
    ∀ p, p < P.D → 2000000 ≤ P.N (p + 1) ∧ 2 * P.d + 4 ≤ P.N (p + 1) ∧
      (P.Lambda p : ℝ) / 4 ≤ P.N (p + 1) ∧
      1000 * ((2 * (H.Cmom + 2) + 2) ^ 2 + 1) ≤ P.R (p + 1) ∧
      P.theta (p + 1) ≤ P.N (p + 1) ∧ Real.log P.L ≤ P.N (p + 1) ∧
      P.C₂ / (1 - P.C₁ * P.δ) ≤ Real.exp (P.N (p + 1) : ℝ) ∧
      4 ≤ P.L ^ ((4 * P.theta (p + 1) + P.theta p) / 5 - P.theta (p + 1)) := assembly_stage_sizes P H.dimension H.eta_pos (H.B + 1) H.Cmom H.size

theorem L_ge_exp_two : Real.exp 2 ≤ P.L := H.sizes.1

theorem L_ge_one : 1 ≤ P.L :=
  (by linarith [Real.add_one_le_exp (2 : ℝ)] : (1 : ℝ) ≤ Real.exp 2).trans H.L_ge_exp_two

theorem geometric_small : P.δ ^ (P.ν / 2) ≤ 1 / 2 ∧ P.δ ^ P.ν ≤ 1 / 2 ∧
    P.δ ^ (2 * P.ν) ≤ 1 / 2 ∧ P.δ ^ P.ν ≤ Real.exp (-21) := small_delta_consequences H.delta_pos H.small_delta

theorem taylor_nonneg : 0 ≤ P.C₁ * P.δ := mul_nonneg H.C1_nonneg H.delta_pos.le

theorem taylor_lt_one : P.C₁ * P.δ < 1 :=
  H.small_taylor.trans_lt (exp_neg_one_le_half.trans_lt (by norm_num))

theorem phi_stage {q : ℕ} (hq : q ≤ P.D) {t : ℝ} (ht : t ∈ Icc 0 (q : ℝ)) :
    ∀ k, |P.φ (P.δ * t) k| ≤ H.B * jbr k ^ (-(4 * P.Lambda q : ℝ)) :=
  uniform_phi_stage_weight P H.dimension H.delta_pos.le H.time_range H.B
    (zero_le_one.trans H.B_ge_one) H.phi_bound hq ht

theorem theta_le_R (q : ℕ) : P.theta q ≤ P.R q := by
  have hs := stage_sizes_of_threshold P H.dimension
    (max (H.B + 1) (P.C₂ / (1 - P.C₁ * P.δ))) (assemblySizeK P H.Cmom)
    ((le_max_left _ _).trans H.size)
  have hk : P.theta 0 ≤ assemblySizeK P H.Cmom :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact (theta_le_zero P q).trans (hk.trans (hs.2.2.2 q).1)

theorem exp_le_scale (q : ℕ) : Real.exp (-(P.N q : ℝ)) ≤ P.L ^ (-P.theta q) :=
  exp_neg_stage_le_scale P H.dimension q H.L_ge_exp_two
    (by have h := N_ge_two_of_exp_two_le P H.dimension H.L_ge_exp_two q
        by_contra hn
        have hr : P.R q = 0 := by omega
        simp only [WTParams.N, hr, zero_pow (by have hd := H.dimension; omega : 40 * P.d ≠ 0)] at h
        omega) (H.theta_le_R q)

theorem remainder_constant {p : ℕ} (hp : p < P.D) :
    2 * P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) +
      P.C₂ * (P.C₁ * P.δ) ^ (P.N (p + 1) ^ 4 / 2 + 1) / (1 - P.C₁ * P.δ) ≤
        P.L ^ (-P.theta (p + 1)) := by
  obtain ⟨hN, _, _, _, hθ, hlog, hA, hgap⟩ := H.sizes.2.2.2 p hp
  exact nextRemainder_constant_le_target P p (by omega) (zero_lt_one.trans_le H.L_ge_one)
    H.C2_nonneg H.taylor_nonneg H.taylor_lt_one H.small_taylor hθ hlog hA hgap

end InductContext
end WaveTurbulence.Induct
