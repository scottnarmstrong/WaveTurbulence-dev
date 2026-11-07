/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestAnalytic
import Mathlib.Tactic

/-! # Analytic absorption with a remainder: the `L^(-η²ρ+C(w+1))` form

The third bound of DH23 Prop 10.2 (L1834, L1915-L1917) combines a count of
`kf+kg` fine/good steps, `S = C(w+1)` remainder units, the normal-step budget
`2n ≤ 48000 (kf+kg+S)` and the ladder bound `ρ ≤ C0 (kf+kg+S)`. Here `S` and
`C0` are only numbers; the combinatorial inputs are supplied elsewhere.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
open Filter

theorem budget_real_bound_rem (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ L : ℝ in atTop,∀ (n kf kg S : ℕ) (a b : ℝ),2*n ≤ 48000*(kf+kg+S) →
      ((Real.log L)^8)^n * (L^(-a))^kf * (L^(-b))^kg ≤
        L^((θ-a)*kf+(θ-b)*kg+θ*S) := by
  filter_upwards [log_pow_le_rpow_eventually θ hθ,eventually_gt_atTop (1 : ℝ)] with L hL hL1
  obtain ⟨hpow,hlog⟩ := hL
  intro n kf kg S a b hn
  have hLp : 0 < L := by linarith only [hL1]
  have hA : 1 ≤ ((Real.log L)^8) := one_le_pow₀ hlog
  have hn' : n ≤ 24000*(kf+kg+S) := by omega
  calc ((Real.log L)^8)^n * (L^(-a))^kf * (L^(-b))^kg
      ≤ (((Real.log L)^8)^24000)^(kf+kg+S) * (L^(-a))^kf * (L^(-b))^kg := by
        gcongr
        calc ((Real.log L)^8)^n ≤ ((Real.log L)^8)^(24000*(kf+kg+S)) := pow_le_pow_right₀ hA hn'
          _ = _ := by rw [pow_mul]
    _ ≤ (L^θ)^(kf+kg+S) * (L^(-a))^kf * (L^(-b))^kg := by
        gcongr
        calc (((Real.log L)^8)^24000) = (Real.log L)^(192000 : ℕ) := by rw [← pow_mul]
          _ ≤ L^θ := hpow
    _ = L^((θ-a)*kf+(θ-b)*kg+θ*S) := by
        rw [← Real.rpow_natCast,← Real.rpow_natCast (L^(-a)),← Real.rpow_natCast (L^(-b)),
          ← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le,
          ← Real.rpow_add hLp,← Real.rpow_add hLp]
        congr 1
        push_cast
        ring

/-- The `L^(-η²ρ+(η/3)S)` absorption. Smallness of `η` enters only as
`η C0 ≤ 1/4`, where `C0` is the combinatorial ladder constant. -/
theorem budget_rho (γ η : ℝ) (hγ : 0 < γ ∧ γ < 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ))
    (C0 : ℝ) (hηC : η*C0 ≤ 1/4) :
    ∃ L₁ : ℝ,1 < L₁ ∧ ∀ L ≥ L₁,∀ n kf kg S ρ : ℕ,2*n ≤ 48000*(kf+kg+S) →
      (ρ : ℝ) ≤ C0*((kf : ℝ)+kg+S) →
      (ENNReal.ofReal (Real.log L^8))^n*(ENNReal.ofReal (L^(-η/2)))^kf*
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))^kg ≤
        ENNReal.ofReal (L^(-η^2*ρ+(η/3)*S)) := by
  have hγ0 : 0 < min γ (1-γ) := lt_min hγ.1 (by linarith only [hγ.2])
  set γ0 := min γ (1-γ) with hγ0def
  set θ := min (η/12) (γ0/40) with hθdef
  have hθ : 0 < θ := lt_min (by linarith only [hη]) (by linarith only [hγ0])
  have hθ1 : θ ≤ η/12 := min_le_left _ _
  have hθ2 : θ ≤ γ0/40 := min_le_right _ _
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp ((budget_real_bound_rem θ hθ).and (eventually_gt_atTop (1 : ℝ)))
  refine ⟨max L₁ 2,by simp,?_⟩
  intro L hL n kf kg S ρ hn hρ
  obtain ⟨hb,hL1⟩ := hL₁ L ((le_max_left _ _).trans hL)
  have hLp : 0 < L := by linarith only [hL1]
  have hreal := hb n kf kg S (η/2) (5*γ0/8) hn
  have hconv : (ENNReal.ofReal (Real.log L^8))^n*(ENNReal.ofReal (L^(-η/2)))^kf*
      (ENNReal.ofReal (L^(-5*γ0/8)))^kg =
      ENNReal.ofReal (((Real.log L)^8)^n*(L^(-(η/2)))^kf*(L^(-(5*γ0/8)))^kg) := by
    have hlog : 0 ≤ Real.log L := (Real.log_pos hL1).le
    have e1 : -η/2 = -(η/2) := by ring
    have e2 : -5*γ0/8 = -(5*γ0/8) := by ring
    have h1 : ENNReal.ofReal (((Real.log L)^8)^n) = ENNReal.ofReal ((Real.log L)^8)^n :=
      ENNReal.ofReal_pow (by positivity) n
    have h2 : ENNReal.ofReal ((L^(-(η/2)))^kf) = ENNReal.ofReal (L^(-(η/2)))^kf :=
      ENNReal.ofReal_pow (by positivity) kf
    have h3 : ENNReal.ofReal ((L^(-(5*γ0/8)))^kg) = ENNReal.ofReal (L^(-(5*γ0/8)))^kg :=
      ENNReal.ofReal_pow (by positivity) kg
    rw [e1,e2,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),h1,h2,h3]
  rw [hconv]
  refine ENNReal.ofReal_le_ofReal (hreal.trans ?_)
  apply Real.rpow_le_rpow_of_exponent_le hL1.le
  have hkf0 : (0 : ℝ) ≤ kf := Nat.cast_nonneg _
  have hkg0 : (0 : ℝ) ≤ kg := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have c1 : θ-η/2 ≤ -5*η/12 := by linarith only [hθ1]
  have c2 : θ-5*γ0/8 ≤ -5*η/12 := by linarith only [hθ2,hηγ,hη]
  have hρ' : η^2*ρ ≤ (η/4)*((kf : ℝ)+kg+S) := by
    have h1 := mul_le_mul_of_nonneg_left hρ (sq_nonneg η)
    have h2 : η^2*(C0*((kf : ℝ)+kg+S)) ≤ (η/4)*((kf : ℝ)+kg+S) := by
      have : η^2*C0 = η*(η*C0) := by ring
      have h3 : η*(η*C0) ≤ η*(1/4) := mul_le_mul_of_nonneg_left hηC hη.le
      calc η^2*(C0*((kf : ℝ)+kg+S)) = (η*(η*C0))*((kf : ℝ)+kg+S) := by ring
        _ ≤ (η*(1/4))*((kf : ℝ)+kg+S) := by gcongr
        _ = _ := by ring
    exact h1.trans h2
  nlinarith only [mul_le_mul_of_nonneg_right c1 hkf0,mul_le_mul_of_nonneg_right c2 hkg0,hρ',hθ1,hS0,hη,
    mul_le_mul_of_nonneg_right hθ1 hS0]

end WaveTurbulence.Mole.AppbAlgorithm
