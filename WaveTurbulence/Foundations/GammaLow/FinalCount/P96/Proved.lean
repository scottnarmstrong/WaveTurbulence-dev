/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6Final
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Main
/-! # Prop 9.6 at `γ ≤ 1/2`, closed up to N2 Lemma 5.2 (packet L6, item F)

`prop96_low` (`P96/Final.lean`) with its case-(6) top input `Case6TopLow` discharged by L6-COUNT's
`case6TopLow_proved` (`Count/C6Final.lean`). The only remaining hypothesis is the named input `DrawnTVineInput`
(N2 Lemma 5.2, owner L3); `prop96_low_closed` discharges it with L3D's proof `TVine.Struct.Drawn.drawnTVine`, so
Prop 9.6 at `γ ≤ 1/2` holds with only the parameter hypotheses. The H port uses `prop96_low_closed`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.FinalCountG8

universe u v

/-- **Prop 9.6 at `0 < γ ≤ 1/2`** (DH23 Prop 9.6 over `𝒱_γ`), from N2 Lemma 5.2 only. -/
theorem prop96_low_proved (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) (hDT : DrawnTVineInput.{u, v}) :
    Prop96LowAt.{u, v} d γ η :=
  prop96_low d hd γ hγ η hη hsm hηs hDT (Count.case6TopLow_proved d hd γ hγ η hη hsm hηs)

/-- **Prop 9.6 at `0 < γ ≤ 1/2`, closed**: all inputs discharged (N2 Lemma 5.2 by `TVine.Struct.Drawn.drawnTVine`,
case (6) by `Count.case6TopLow_proved`). -/
theorem prop96_low_closed (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) : Prop96LowAt.{u, v} d γ η :=
  prop96_low d hd γ hγ η hη hsm hηs TVine.Struct.Drawn.drawnTVine (Count.case6TopLow_proved d hd γ hγ η hη hsm hηs)

end WaveTurbulence.GammaLow.FinalCount
