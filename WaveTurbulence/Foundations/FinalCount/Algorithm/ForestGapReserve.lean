/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestBondBudget
public import WaveTurbulence.Foundations.FinalCount.AppBIteratedLargeGap
import Mathlib.Tactic

/-! # A bond-budget reserve pays every actual reinsertion gap loss

Each graph edit removes at least one bond. Charging one L^(-γ) per bond
removed therefore covers every reinsertion and is harmless for literal
cuts. Component splitting leaves the bond sum unchanged.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Filter
universe u v
variable {V : Type v} [DecidableEq V]

noncomputable def forestGapReserve (B : ℕ) (L γ η : ℝ) (F : List (State.{u,v} V)) : ℝ :=
  L^(-γ+η)-((B : ℝ)-(forestBonds F : ℝ))*L^(-γ)

theorem forestGapReserve_initial (B : ℕ) (L γ η : ℝ) (F : List (State.{u,v} V))
    (h : forestBonds F = B) : forestGapReserve B L γ η F = L^(-γ+η) := by
  simp only [forestGapReserve,h,sub_self,zero_mul,sub_zero]

theorem ForestMove.gapReserve_le {F G : List (State.{u,v} V)} (h : ForestMove F G)
    (B : ℕ) (L γ η : ℝ) (hL : 0 ≤ L) :
    forestGapReserve B L γ η G ≤ forestGapReserve B L γ η F := by
  have he : (forestBonds G : ℝ) ≤ forestBonds F := by exact_mod_cast h.bonds_le
  have hp := Real.rpow_nonneg hL (-γ)
  have hh := mul_nonneg (sub_nonneg.mpr he) hp
  unfold forestGapReserve
  nlinarith only [hh]

theorem forestGapReserve_edit_loss (pre tail : List (State.{u,v} V))
    {s t : State.{u,v} V} (h : GeometricStep s t) (B : ℕ) (L γ η : ℝ) (hL : 0 ≤ L) :
    forestGapReserve B L γ η (pre++t::tail) ≤
      forestGapReserve B L γ η (pre++s::tail)-L^(-γ) := by
  have he : (forestBonds (pre++t::tail) : ℝ)+1 ≤ forestBonds (pre++s::tail) := by
    exact_mod_cast forestBonds_edit_decrease pre tail h
  have hp := Real.rpow_nonneg hL (-γ)
  have hh := mul_nonneg (sub_nonneg.mpr he) hp
  unfold forestGapReserve
  nlinarith only [hh]

/-- The initial molecule has at most twice its number of atoms in bonds.
For polylogarithmic size, the entire forest iteration retains half the
source gap, uniformly in every graph carrier and every current forest. -/
theorem forestGapReserve_half_eventual (γ η : ℝ) (hη : 0 < η) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop,∀ B : ℕ,(B : ℝ) ≤ 2*(1+Real.log L)^m →
      ∀ F : List (State.{u,v} V),L^(-γ+η)/2 ≤ forestGapReserve B L γ η F := by
  have hh := appb_polylog_gap_loss_eventual γ η hη (m+1)
  filter_upwards [hh,eventually_ge_atTop (Real.exp 1)] with L hL hexp B hB F
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hexp
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  have hbase : 2 ≤ 1+Real.log L := by linarith only [hlog]
  have hpow : 2*(1+Real.log L)^m ≤ (1+Real.log L)^(m+1) := by
    calc
      _ ≤ (1+Real.log L)*(1+Real.log L)^m :=
        mul_le_mul_of_nonneg_right hbase (pow_nonneg (by linarith only [hlog]) m)
      _ = _ := by rw [pow_succ]; ring
  have hgap := hL B (hB.trans hpow)
  have hE : 0 ≤ (forestBonds F : ℝ)*L^(-γ) := mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hLp.le _)
  unfold forestGapReserve
  nlinarith only [hgap,hE]

end WaveTurbulence.Mole.AppbAlgorithm
