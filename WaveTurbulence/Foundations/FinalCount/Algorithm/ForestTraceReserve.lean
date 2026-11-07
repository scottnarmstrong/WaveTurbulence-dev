/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestGapReserve
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TraceBounds
import Mathlib.Tactic

/-! # A compound source step pays its reinsertion reserve by actual bond descent -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

theorem forestBonds_trace_decrease (pre tail : List (State.{u,v} V))
    {s t : State.{u,v} V} {n : ℕ} (h : Trace s t n) (hn : 0 < n) :
    forestBonds (pre++t::tail)+1 ≤ forestBonds (pre++s::tail) := by
  have hh := h.bondPotential_lt hn
  simp only [forestBonds,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
  omega

theorem forestGapReserve_trace_loss (pre tail : List (State.{u,v} V))
    {s t : State.{u,v} V} {n : ℕ} (h : Trace s t n) (hn : 0 < n)
    (B : ℕ) (L γ η : ℝ) (hL : 0 ≤ L) :
    forestGapReserve B L γ η (pre++t::tail) ≤
      forestGapReserve B L γ η (pre++s::tail)-L^(-γ) := by
  have he : (forestBonds (pre++t::tail) : ℝ)+1 ≤ forestBonds (pre++s::tail) := by
    exact_mod_cast forestBonds_trace_decrease pre tail h hn
  have hh := mul_nonneg (sub_nonneg.mpr he) (Real.rpow_nonneg hL (-γ))
  unfold forestGapReserve
  nlinarith only [hh]

end WaveTurbulence.Mole.AppbAlgorithm
