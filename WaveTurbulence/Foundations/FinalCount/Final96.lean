/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Assembly96
public import WaveTurbulence.Foundations.FinalCount.Case6_96
public import WaveTurbulence.Foundations.FinalCount.C4Main
import Mathlib.Tactic

/-! # DH23 Proposition 9.6 for `1/2 < γ < 1`: the assembly

`prop96_of_nonexc` is `Prop96At` from the proved cases and the NAMED input `Case4NonExc` of case (4) (Prop 10.4(2),
findings F6-1/F6-2). Case (6) is proved without operation (e) (`case_six`, `γ > 1/2`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v

/-- Case (6) in the shape `EvenCaseAt`. -/
theorem case_six_even (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1) :
    EvenCaseAt.{u, v} d γ η (fun a b => a = 2 ∧ b = 1) := by
  obtain ⟨Cs, hCs, h⟩ := case_six.{u, v} d hd γ hγ η hη hsm hsm2 hηs
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR₀, hR⟩ := h m C1 hC1 δ hδ
  exact ⟨R₀, hR₀, fun L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA _ hnodd hnc hc =>
    hR L hL M cls odd Adm P hS hF hsz hP hMA hnodd hnc hc⟩

/-- **DH23 Proposition 9.6 for `1/2 < γ < 1`**, conditional on the named input `Case4NonExc` (case (4), Prop 10.4(2)). -/
theorem prop96_of_nonexc (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1) (hNE : Case4NonExc.{u, v} d γ η) : Prop96At.{u, v} d γ η :=
  prop96_of_cases46 d hd γ hγ η hη hsm hsm2 hηs (case_four_of_nonexc d hd γ hγ η hη hsm hsm2 hηs hNE)
    (case_six_even d hd γ hγ η hη hsm hsm2 hηs)

end WaveTurbulence.FinalCountG8
