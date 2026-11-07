/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForest
import Mathlib.Tactic

/-! # The standing half-gap, with a threshold independent of the atom type -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Filter
universe u v

theorem forest_half_gap_uniform (γ η : ℝ) (hη : 0 < η) (m : ℕ) :
    ∃ L₀ : ℝ,Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,∀ (V : Type v) [DecidableEq V] (d : ℕ) (w : Mom d) (c : ℝ) (B : ℕ),
      (B : ℝ) ≤ 2*(1+Real.log L)^m → ∀ F : CountingForest.{u,v} V d L γ η w c B,
      L^(-γ+η)/2 ≤ F.gap := by
  have hh := appb_polylog_gap_loss_eventual γ η hη (m+1)
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp (hh.and (eventually_ge_atTop (Real.exp 1)))
  refine ⟨max L₁ (Real.exp 1),le_max_right _ _,?_⟩
  intro L hL V _ d w c B hB F
  obtain ⟨hgap0,hexp⟩ := hL₁ L ((le_max_left _ _).trans hL)
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hexp
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  have hbase : 2 ≤ 1+Real.log L := by linarith only [hlog]
  have hpow : 2*(1+Real.log L)^m ≤ (1+Real.log L)^(m+1) := by
    calc
      _ ≤ (1+Real.log L)*(1+Real.log L)^m :=
        mul_le_mul_of_nonneg_right hbase (pow_nonneg (by linarith only [hlog]) m)
      _ = _ := by rw [pow_succ]; ring
  have hgap := hgap0 B (hB.trans hpow)
  have hE : 0 ≤ (forestBonds (F.problems.map Problem.state) : ℝ)*L^(-γ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hLp.le _)
  rw [F.reserve_eq]
  unfold forestGapReserve
  nlinarith only [hgap,hE]

end WaveTurbulence.Mole.AppbAlgorithm
