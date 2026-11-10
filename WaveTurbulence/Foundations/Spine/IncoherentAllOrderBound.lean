/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentLegPrefix
public import WaveTurbulence.Foundations.Spine.RegularParity
public import WaveTurbulence.Foundations.Spine.ZeroRemainderNorm
/-! TARGET L2253–2255: the even/odd incoherent contribution at the requested delta exponent. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

abbrev IncoherentRemainderAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ N : ℕ, N ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1),
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
      (fun k => incoherentCoupleSum P (inputsF P R) (p + 1) N t k) ≤
      ENNReal.ofReal (P.δ ^ (2 * P.ν * N) *
        P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))

theorem incoherent_remainder_of_even_comparison (P : WTParams)
    (heven : IncoherentEvenComparisonAt P) (hsmall : CoherentSmallParameters P) :
    IncoherentRemainderAt P := by
  classical
  intro p hp R hR N hN t ht
  by_cases hpar : Even N
  · obtain ⟨n, hn⟩ := hpar
    have heq : N = 2 * n := by omega
    clear hn
    subst N
    have hc := heven p hp R hR n (by omega) t ht
    have hpow : P.δ ^ ((n : ℝ) / 2) ≤ P.δ ^ (2 * P.ν * (2 * n : ℕ)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hsmall.delta_pos hsmall.delta_le
      have hν := hsmall.nu_le
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      push_cast
      nlinarith
    exact hc.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by linarith [hsmall.large_L]) _)))
  · have heq : (fun k => incoherentCoupleSum P (inputsF P R) (p + 1) N t k) =
        fun _ => 0 := by
      funext k
      exact incoherentCoupleSum_eq_zero_of_odd P _ _ _ hpar t k
    rw [heq, SNorm_zero_function]
    exact bot_le

end WaveTurbulence.LGSpine
