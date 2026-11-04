/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PhaseTranslation
import Mathlib.Tactic

/-!
# Extracting the exact time modulation from the source phase

Every input time parameter occurs exactly once. Simultaneous time
translation therefore leaves only a single output modulation, whose
frequency is the sum of the original parameters.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- The product of all literal source time-parameter phases. -/
@[expose] noncomputable def parameterPhase {d : ℕ} (D : SumintDatum d) (τ : D.S.TVar → ℝ) : ℂ :=
  ∏ v, Complex.exp ((Real.pi * (D.param v * τ v) : ℝ) * Complex.I)

/-- The full source phase is its geometric part times precisely the time-parameter phases. -/
theorem phase_eq_geometric_mul_parameter {d : ℕ} (D : SumintDatum d)
    (L γ δ η : ℝ) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    D.phase L γ δ η x r t τ = geometricPhase D L γ δ η x r t τ * parameterPhase D τ := by
  classical
  unfold geometricPhase SumintDatum.phase parameterPhase
  simp only [zero_mul, mul_zero, Complex.ofReal_zero, Complex.exp_zero, Finset.prod_const_one,
    one_mul, mul_one, Fintype.prod_sum_type, Fintype.prod_sigma]
  simp_rw [Finset.prod_mul_distrib]
  ring

/-- Simultaneous translation of the parameter phases produces their summed modulation. -/
theorem parameterPhase_translate {d : ℕ} (D : SumintDatum d) (τ : D.S.TVar → ℝ) (a : ℝ) :
    parameterPhase D (fun v => τ v + a) =
      Complex.exp ((Real.pi * (∑ v, D.param v) * a : ℝ) * Complex.I) * parameterPhase D τ := by
  classical
  have he (v : D.S.TVar) :
      Complex.exp ((Real.pi * (D.param v * (τ v + a)) : ℝ) * Complex.I) =
      Complex.exp ((Real.pi * (D.param v * τ v) : ℝ) * Complex.I) *
        Complex.exp ((Real.pi * (D.param v * a) : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hs : (∏ v, Complex.exp ((Real.pi * (D.param v * a) : ℝ) * Complex.I)) =
      Complex.exp ((Real.pi * (∑ v, D.param v) * a : ℝ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  unfold parameterPhase
  simp_rw [he]
  rw [Finset.prod_mul_distrib, hs, mul_comm]

/-- The exact source phase under the shear and simultaneous input-time translation. -/
theorem phase_translate {d : ℕ} (D : SumintDatum d)
    (L γ δ η : ℝ) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t a : ℝ) (τ : D.S.TVar → ℝ) :
    D.phase L γ δ η x r (t+a) (fun v => τ v+a) =
      Complex.exp ((Real.pi * (∑ v, D.param v) * a : ℝ) * Complex.I) *
        D.phase L γ δ η x r t τ := by
  rw [phase_eq_geometric_mul_parameter, phase_eq_geometric_mul_parameter,
    geometricPhase_translate, parameterPhase_translate]
  ring

end WaveTurbulence.Sumint
