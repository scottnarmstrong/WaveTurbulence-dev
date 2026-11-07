/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Final96b
public import WaveTurbulence.Foundations.FinalCount.XRoute.Branch
import Mathlib.Tactic

/-! # DH23 Proposition 9.6 for `1/2 < γ < 1`, unconditional (finalcount-g8 glued with g8-xroute)

`prop96 : Prop96At` is `prop96_of_smallcell` applied to `case4SmallCell_proved` (X-terminal Theorem A, R26).
Parameter hypotheses: `d ≥ 3`, `γ ∈ (1/2, 1)`, `0 < η`, and the three instances of `η ≪_{d,γ} 1` (DH23 L438):
`d η ≤ min γ (1-γ) / 1000`, `d η ≤ (2γ-1)/1000`, `4·1440061·η ≤ 1`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FinalCountG8
universe u v

/-- **DH23 Proposition 9.6 for `1/2 < γ < 1`** (`lgmolect`, L1818-L1822). -/
theorem prop96 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1) : Prop96At.{u, v} d γ η :=
  prop96_of_smallcell d hd γ hγ η hη hsm hsm2 hηs (case4SmallCell_proved d hd γ hγ η hη hsm hηs)

end WaveTurbulence.FinalCountG8
