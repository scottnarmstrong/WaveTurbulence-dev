/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot3

/-! # V5 Step 4d-B2: the bottom vine, part 4 (the `b`-factor is twist invariant)

`bFac_tw`: for a decoration `x` obeying the conservation at the lower joint `b = P.lower`, the `b`-factor of the twisted garden at the
label-switched decoration `twistNodeLabels G P x` (and the clock `u'` with `u' (eB b) = u b`) equals the `b`-factor of the original:
the sign of `b` and the resonance factor `Ω_b` both flip, the interaction coefficient is unchanged under conservation, and the two
boundary time conditions are unchanged because the boundary children are the same subtrees.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

theorem epsCoef_swap1 {d : ℕ} (n1 n2 n3 : Fin d → ℤ) : epsCoef (n1 - n2 + n3) n3 n2 = epsCoef n1 n2 n3 := by
  have key : n1 - n2 + n3 = n3 ↔ n1 = n2 := by rw [add_eq_right, sub_eq_zero]
  unfold epsCoef
  by_cases h1 : n1 = n2 <;> by_cases h2 : n2 = n3 <;> simp_all [eq_comm]

theorem epsCoef_swap2 {d : ℕ} (n1 n2 n3 : Fin d → ℤ) : epsCoef n2 n1 (n1 - n2 + n3) = epsCoef n1 n2 n3 := by
  have key : n1 - n2 + n3 = n1 ↔ n2 = n3 := by
    constructor
    · intro h
      have e : n3 - n2 = (n1 - n2 + n3) - n1 := by abel
      have : n3 - n2 = 0 := by rw [e, h, sub_self]
      exact (sub_eq_zero.mp this).symm
    · intro h; rw [h]; simp
  unfold epsCoef
  by_cases h1 : n1 = n2 <;> by_cases h2 : n2 = n3 <;> simp_all [eq_comm]

theorem phaseAtom_neg (L γ δ : ℝ) (ζ : ℤˣ) (Ω t : ℝ) : phaseAtom L γ δ (-ζ) (-Ω) t = phaseAtom L γ δ ζ Ω t := by
  unfold phaseAtom
  congr 2
  simp only [Units.val_neg, Int.cast_neg]
  congr 1
  ring

end WaveTurbulence.VineEstS5B2
