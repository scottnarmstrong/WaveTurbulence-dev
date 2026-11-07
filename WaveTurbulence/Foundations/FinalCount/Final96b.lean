/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Final96
public import WaveTurbulence.Foundations.FinalCount.C4NonExc
import Mathlib.Tactic

/-! # DH23 Proposition 9.6 for `1/2 < γ < 1`, conditional on the small-cell sub-branch of case (4)

`prop96_of_smallcell : Case4SmallCell → Prop96At`.  The only open input is `Case4SmallCell` (C4NonExc.lean): the closure
`𝕄₁` of a case-(4) component is not `Y`-exceptional and reaches a small cell or has at most four atoms (finding F6-2).
Everything else (cases (1)–(6), the decoration-level split of Prop 10.4(2)′, F6-1) is proved.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FinalCountG8
universe u v

/-- **DH23 Proposition 9.6 for `1/2 < γ < 1`**, conditional on `Case4SmallCell`. -/
theorem prop96_of_smallcell (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1) (hSC : Case4SmallCell.{u, v} d γ η) : Prop96At.{u, v} d γ η :=
  prop96_of_nonexc d hd γ hγ η hη hsm hsm2 hηs (case4_nonexc_of_smallcell d hd γ hγ η hη hsm hηs hSC)

end WaveTurbulence.FinalCountG8
