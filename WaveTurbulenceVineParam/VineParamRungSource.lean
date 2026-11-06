/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamRungResonance
import Mathlib.Tactic

/-! # Recovering rung charts from source momentum equations

The local chart is forced by actual conservation and the incoming gap;
its decoder identities are not additional assumptions about decorations.
-/

public section
namespace WaveTurbulence.Vine.Param.RungPattern
variable {E : Type*} [AddCommGroup E]

/-- Both reconstructed conservation equations hold over any additive group;
no normed-space structure is needed by the integral lattice chart. -/
theorem momentum_additive (P : RungPattern) (r d : E) (xy : E×E) :
    P.signs 0 • (P.decode d xy).1+P.signs 1 • (P.decode d xy).2+
      P.signs 3 • P.upperAfter r d xy-P.signs 2 • P.upperBefore r d=0 ∧
    P.signs 0 • (P.decode d xy).1+P.signs 1 • (P.decode d xy).2+
      P.signs 3 • P.lowerAfter d xy-P.signs 2 • d=0 := by
  cases P <;> constructor <;>
    simp [signs,decode,upperAfter,upperBefore,lowerAfter] <;> abel

/-- Lower conservation determines the following physical rail from actual
rung labels in every balanced orientation. -/
theorem lowerAfter_of_conservation (P : RungPattern) (a b d D : E)
    (h : P.signs 0 • a+P.signs 1 • b+P.signs 3 • D-P.signs 2 • d=0) :
    P.lowerAfter d (P.encode d (a,b))=D := by
  cases P <;>
    simp only [signs,encode,lowerAfter,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
      one_zsmul,neg_one_zsmul] at h ⊢
  all_goals apply sub_eq_zero.mp
  · convert h using 1; abel
  · convert congrArg Neg.neg h using 1 <;> abel
  · convert h using 1; abel
  · convert congrArg Neg.neg h using 1 <;> abel
  · convert h using 1; abel
  · convert congrArg Neg.neg h using 1 <;> abel

/-- Upper conservation and the incoming gap determine the other following
rail. Together with the lower equation this recovers all six local labels. -/
theorem upperAfter_of_conservation (P : RungPattern) (r a b d C : E)
    (h : P.signs 0 • a+P.signs 1 • b+P.signs 3 • C-
      P.signs 2 • P.upperBefore r d=0) :
    P.upperAfter r d (P.encode d (a,b))=C := by
  cases P <;>
    simp only [signs,encode,upperAfter,upperBefore,lowerAfter,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
      one_zsmul,neg_one_zsmul] at h ⊢
  all_goals apply sub_eq_zero.mp
  · convert h using 1; abel
  · convert congrArg Neg.neg h using 1 <;> abel
  · convert h using 1; abel
  · convert congrArg Neg.neg h using 1 <;> abel
  · convert h using 1; abel
  · convert congrArg Neg.neg h using 1 <;> abel

end WaveTurbulence.Vine.Param.RungPattern
