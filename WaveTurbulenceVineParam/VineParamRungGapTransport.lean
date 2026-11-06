/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamRungResonance
import Mathlib.Tactic

/-! # Oriented physical gaps are forced by the two source rung equations -/

public section
namespace WaveTurbulence.Vine.Param.RungPattern
variable {E : Type*} [AddCommGroup E]

/-- Summing the two actual vertex equations transports the oriented rail gap. -/
theorem oriented_gap_transport (P : RungPattern) (a b c d C D : E)
    (hu : P.signs 0 • a+P.signs 1 • b+P.signs 3 • C-P.signs 2 • c=0)
    (hl : P.signs 0 • a+P.signs 1 • b+P.signs 3 • D-P.signs 2 • d=0) :
    P.signs 2 • (c-d)=P.signs 3 • (C-D) := by
  apply sub_eq_zero.mp
  calc
    P.signs 2 • (c-d)-P.signs 3 • (C-D)=
        (P.signs 0 • a+P.signs 1 • b+P.signs 3 • D-P.signs 2 • d)-
          (P.signs 0 • a+P.signs 1 • b+P.signs 3 • C-P.signs 2 • c) := by
      simp only [smul_sub]
      abel
    _=0 := by rw [hu,hl,sub_self]

/-- The source-oriented preceding gap gives the exact incoming upper label. -/
theorem upperBefore_of_gap (P : RungPattern) (c d r : E)
    (h : P.signs 2 • (c-d)=r) : c=P.upperBefore r d := by
  rw [← h]
  cases P <;> simp [upperBefore,signs]

/-- Negating the signed cut flux gives the oriented outgoing gap. -/
theorem outgoing_gap_of_cut_flux (P : RungPattern) (C D r : E)
    (h : -(P.signs 3) • C+P.signs 3 • D= -r) :
    P.signs 3 • (C-D)=r := by
  have hh := congrArg Neg.neg h
  simpa only [neg_add,neg_smul,neg_neg,smul_sub,sub_eq_add_neg, smul_add, smul_neg] using hh

end WaveTurbulence.Vine.Param.RungPattern
