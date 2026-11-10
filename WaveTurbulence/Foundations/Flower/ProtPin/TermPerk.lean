/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermTree
public import WaveTurbulence.Foundations.Flower.ProtPin.CutFlat

/-! # D3 PROT-PIN: `term`, one output: assembly of the cut, the core estimate and the gates -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem abs_epsCoef_le {d : ℕ} (a b c : Fin d → ℤ) : |epsCoef a b c| ≤ 1 := by
  unfold epsCoef; split_ifs <;> norm_num

theorem abs_cutEps_le {d : ℕ} (m : MiniTreeCode) (e : PairE m d) : |cutEps m e| ≤ 1 := by
  unfold cutEps
  rw [abs_mul]
  exact mul_le_one₀ (abs_epsCoef_le _ _ _) (abs_nonneg _) (abs_epsCoef_le _ _ _)

theorem norm_I_mul_unit (u : ℤˣ) : ‖Complex.I * (((u : ℤ) : ℂ))‖ = 1 := by
  rw [norm_mul, Complex.norm_I, one_mul]
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

theorem coupling_nonneg {d : ℕ} {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) : 0 ≤ coupling d L γ δ := by
  unfold coupling
  have := Real.rpow_nonneg hL ((d : ℝ) - γ)
  positivity

/-- The modulus of the prefactor of (cut-term). -/
theorem norm_cutPrefactor {d : ℕ} {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (u v : ℤˣ) :
    ‖(coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((u : ℤ) : ℂ)) * (Complex.I * ((v : ℤ) : ℂ))‖ =
      coupling d L γ δ ^ 2 := by
  rw [norm_mul, norm_mul, norm_I_mul_unit, norm_I_mul_unit, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (coupling_nonneg hL hδ)]
  ring

instance instCountablePairE {d : ℕ} (m : MiniTreeCode) : Countable (PairE m d) := by
  unfold PairE; infer_instance

end WaveTurbulence.Flower.ProtPin
