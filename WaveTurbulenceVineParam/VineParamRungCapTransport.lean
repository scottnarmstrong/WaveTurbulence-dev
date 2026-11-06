/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamRungResonance
import Mathlib.Tactic

/-! # Exact boundary matching for contracting an inserted rung

Translating the cap by the rung correction μ matches both old slot labels.
If the rail direction changes, reflect the cap first, interchanging its
ports. These equalities give the arbitrary-insertion transport and explain
why the paired resonance is the corresponding linear gap correction.
-/

public section
namespace WaveTurbulence.Vine.Param.RungPattern
variable {E : Type*} [AddCommGroup E]

/-- Exactly the same-direction doubled-bond patterns reverse the rail order. -/
@[expose] def reversesPorts : RungPattern → Bool
  | .pp | .mm => true
  | _ => false

/-- Both boundary labels match after the explicit translation/reflection. -/
theorem cap_ports_match (P : RungPattern) (r d : E) (xy : E×E) :
    if P.reversesPorts then
      P.lowerAfter d xy+P.correction r xy=P.upperBefore r d ∧
        P.upperAfter r d xy+P.correction r xy=d
    else
      P.upperAfter r d xy+P.correction r xy=P.upperBefore r d ∧
        P.lowerAfter d xy+P.correction r xy=d := by
  cases P <;> dsimp only [reversesPorts,lowerAfter,correction,upperBefore,upperAfter]
  all_goals constructor <;> abel

/-- The translation is always an integral affine function with source
ternary coefficients. This is also valid for a zero-gap ladder. -/
theorem correction_coefficients (P : RungPattern) (r : E) (xy : E×E) :
    P.correction r xy=(P.coefficients 0) • xy.1+
      (P.coefficients 1) • xy.2+(P.coefficients 2) • r := by
  cases P <;> simp only [correction,coefficients,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,one_zsmul,neg_one_zsmul,zero_zsmul,
    add_zero] <;> abel

end WaveTurbulence.Vine.Param.RungPattern
