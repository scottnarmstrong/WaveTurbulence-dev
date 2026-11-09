/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Assembly
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.BridgeProof
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Case6
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.C4NonExcLow
import Mathlib.Tactic

/-! # DH23 Proposition 9.6 at `0 < γ ≤ 1/2` (M2 §4), conditional on three inputs

`prop96_low : Prop96LowAt d γ η`, from the proved cases and:
* `DrawnTVineInput` (N2 Lemma 5.2; NAMED INPUT, owner L3);
* `Case6TopLow` (case (6), sub-cases (6b), (6d); internal L6 target, needs L6-COUNT's operation (e)).
Case (4)′'s T-type branch uses `c4TBridge_proved`.
The non-exceptional branch of case (4)′ is `case4NonExc_all` (Prop 10.4(2)′ and the X-route at every `γ ∈ (0, 1)`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8

/-- **Proposition 9.6 at `0 < γ ≤ 1/2`** (conditional helper: `DrawnTVineInput`, `Case6TopLow`). -/
theorem prop96_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1)
    (hDT : DrawnTVineInput.{u, v}) (htop : Case6TopLow.{u, v} d γ η) :
    Prop96LowAt.{u, v} d γ η :=
  prop96_low_of_cases46 d hd γ hγ η hη hsm hηs hDT
    (case_four_low d hd γ hγ η hη hsm hηs hDT c4TBridge_proved
      (case4NonExc_all d hd γ ⟨hγ.1, by linarith [hγ.2]⟩ η hη hsm hηs))
    (case_six_low_of_top d hd γ hγ η hη hsm hηs htop)

end WaveTurbulence.GammaLow.FinalCount
