/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.DecoratedLeafFactorization
/-! Every scalar coefficient in the exact root-weight expansion has absolute value one. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem abs_quadraticSign {I : Type*} {d : ℕ} (ε : I → ℤˣ)
    (c : RootQuadraticChoice I d) : |quadraticSign ε c| = 1 := by
  cases c with
  | none => exact abs_one
  | some z =>
    rcases z with ⟨j, a, b⟩
    rcases Int.units_eq_one_or (ε a) with ha | ha <;>
      rcases Int.units_eq_one_or (ε b) with hb | hb <;>
        simp [quadraticSign, ha, hb]

theorem abs_rootChoiceSign {w d m : ℕ} (G : Garden w) (c : RootWeightChoices G d m) :
    |rootChoiceSign G c| = 1 := by
  unfold rootChoiceSign
  simp only [abs_prod, abs_quadraticSign, prod_const_one]

theorem norm_rootChoiceSign {w d m : ℕ} (G : Garden w) (c : RootWeightChoices G d m) :
    ‖((rootChoiceSign G c : ℝ) : ℂ)‖ = 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_rootChoiceSign]

end WaveTurbulence.LGSpine
