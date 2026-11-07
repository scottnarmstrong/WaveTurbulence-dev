/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIteratedLargeGap
import Mathlib.Tactic

/-! # Monotonicity and fixed-factor source large-gap thresholds -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Filter
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem AppbLargeGap.mono {M : Molecule V D} {d : ℕ} {L : ℝ} {w : Mom d}
    {κ : D → (Fin d → ℤ)} {g h : ℝ} (hg : AppbLargeGap M L w κ g) (hh : h ≤ g) :
    AppbLargeGap M L w κ h := by
  intro v hv x hx y hy hdir hmate
  exact hh.trans (hg v hv x hx y hy hdir hmate)

end WaveTurbulence.Mole
