/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.SignedParam
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSKernel

/-! # The mode phases of clocked weights (engine step MOD)

A weight row `ρ` depends on two clocks, each either an internal time variable `τ_v` or an output time
`t_c`.  For an integer mode `m_ρ ∈ ℤ²` the product over rows of `e^{πi m_ρ · clock_ρ}` equals
`paramFactor Δ_m τ · e^{πi ν_m · tt}`, with `Δ_m`, `ν_m` the mode totals per slot.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset
open scoped ENNReal

variable {d : ℕ} (D : SumintPar.SumintDatum d)

/-- Weight rows: the `𝒦` rows and the `ℒ` rows. -/
abbrev Row : Type := D.S.VIdx ⊕ D.S.VIdx

/-- Time slots: an internal time variable or one of the three output times. -/
abbrev Slot : Type := D.S.TVar ⊕ Fin 3

/-- The value of a slot. -/
def slotVal (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) : Slot D → ℝ := Sum.elim τ tt

/-- The unimodular output factor `e^{πi ν · tt}`. -/
noncomputable def outFactor (ν tt : Fin 3 → ℝ) : ℂ :=
  Complex.exp ((Real.pi * ∑ c, ν c * tt c : ℝ) * Complex.I)

theorem fsPhase_eq_exp {r : ℕ} (m : Fin r → ℤ) (t : Fin r → ℝ) :
    fsPhase m t = Complex.exp ((Real.pi * ∑ i, (m i : ℝ) * t i : ℝ) * Complex.I) := by
  unfold fsPhase
  rw [Real.fourierChar_apply]
  congr 1
  have : timePairing r t (fun i => (m i : ℝ) / 2) = ∑ i, (m i : ℝ) * t i / 2 := by
    show ∑ i, t i * ((m i : ℝ) / 2) = _
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  push_cast
  rw [← Finset.sum_div]
  ring


end WaveTurbulence.VineEstS3Par.Eng
