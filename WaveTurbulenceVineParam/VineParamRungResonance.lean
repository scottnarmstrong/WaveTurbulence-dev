/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamRungCharts
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! # Exact bilinear resonance identities in all six directed rung charts

TARGET (Omegax_0ladder), DH23 (zetaOmegasum): the lower resonance is
2⟪x,y⟫ and the pair sum is 2⟪r,αx+βy+θr⟫. The coefficients lie in
{0,±1}, with (α,β) nonzero. No estimate or resonance identity is assumed.
-/

public section
namespace WaveTurbulence.Vine.Param
namespace RungPattern

section Additive
variable {E : Type*} [AddCommGroup E]

/-- The upper preceding label, from the lower preceding label and the gap. -/
@[expose] def upperBefore (P : RungPattern) (r d : E) : E :=
  match P with
  | .pp | .pmForward | .mpForward => d+r
  | .pmBackward | .mpBackward | .mm => d-r

/-- The lower following label, recovered from the rung coordinates. -/
@[expose] def lowerAfter (P : RungPattern) (d : E) (xy : E×E) : E :=
  match P with
  | .pp => d+xy.2-xy.1
  | .pmForward | .mpForward => d-xy.1
  | .pmBackward | .mpBackward => d+xy.1
  | .mm => d+xy.1+xy.2

/-- The upper following label, including the possibly reversed next gap. -/
@[expose] def upperAfter (P : RungPattern) (r d : E) (xy : E×E) : E :=
  match P with
  | .pp | .pmBackward | .mpBackward => P.lowerAfter d xy-r
  | .pmForward | .mpForward | .mm => P.lowerAfter d xy+r

/-- The exact three coefficients of the gap correction. -/
@[expose] def coefficients : RungPattern → Fin 3 → ℤ
  | .pp => ![1,-1,1]
  | .pmForward | .mpForward => ![1,0,0]
  | .pmBackward | .mpBackward => ![-1,0,0]
  | .mm => ![-1,-1,-1]

/-- Every correction has the source ternary coefficients, and depends on
at least one of the new rung variables. -/
theorem coefficients_properties (P : RungPattern) :
    (∀ i,P.coefficients i ∈ ({-1,0,1} : Finset ℤ)) ∧
    (P.coefficients 0)^2+(P.coefficients 1)^2 ≠ 0 := by
  cases P <;> decide

/-- The vector μ in the paired resonance formula. -/
@[expose] def correction (P : RungPattern) (r : E) (xy : E×E) : E :=
  match P with
  | .pp => xy.1-xy.2+r
  | .pmForward | .mpForward => xy.1
  | .pmBackward | .mpBackward => -xy.1
  | .mm => -xy.1-xy.2-r

end Additive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The negative molecular Gamma of the lower rung atom. -/
@[expose] def lowerPhase (P : RungPattern) (d : E) (xy : E×E) : ℝ :=
  (P.signs 0 : ℝ)*‖(P.decode d xy).1‖^2+
    (P.signs 1 : ℝ)*‖(P.decode d xy).2‖^2+
    (P.signs 3 : ℝ)*‖P.lowerAfter d xy‖^2-(P.signs 2 : ℝ)*‖d‖^2

/-- The negative molecular Gamma of the upper rung atom. -/
@[expose] def upperPhase (P : RungPattern) (r d : E) (xy : E×E) : ℝ :=
  -(P.signs 0 : ℝ)*‖(P.decode d xy).1‖^2-
    (P.signs 1 : ℝ)*‖(P.decode d xy).2‖^2-
    (P.signs 3 : ℝ)*‖P.upperAfter r d xy‖^2+
    (P.signs 2 : ℝ)*‖P.upperBefore r d‖^2

omit [InnerProductSpace ℝ E] in
/-- All six local momentum constraints hold for the reconstructed labels. -/
theorem momentum (P : RungPattern) (r d : E) (xy : E×E) :
    (P.signs 0) • (P.decode d xy).1+(P.signs 1) • (P.decode d xy).2+
      (P.signs 3) • P.upperAfter r d xy-(P.signs 2) • P.upperBefore r d=0 ∧
    (P.signs 0) • (P.decode d xy).1+(P.signs 1) • (P.decode d xy).2+
      (P.signs 3) • P.lowerAfter d xy-(P.signs 2) • d=0 := by
  cases P <;> constructor <;>
    simp only [signs,decode,upperAfter,upperBefore,lowerAfter,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,one_zsmul,neg_one_zsmul] <;> abel

/-- The lower resonance has the required exact bilinear form. -/
theorem lowerPhase_eq (P : RungPattern) (d : E) (xy : E×E) :
    P.lowerPhase d xy=2*inner ℝ xy.1 xy.2 := by
  cases P <;> simp only [lowerPhase,decode,lowerAfter,signs]
  all_goals norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Int.cast_one,Int.cast_neg,neg_mul,one_mul]
  all_goals simp only [norm_add_sq_real,norm_sub_sq_real,inner_add_left,real_inner_comm]
  all_goals ring

/-- The upper resonance is the opposite bilinear term plus the gap correction. -/
theorem upperPhase_eq (P : RungPattern) (r d : E) (xy : E×E) :
    P.upperPhase r d xy= -2*inner ℝ xy.1 xy.2+2*inner ℝ r (P.correction r xy) := by
  cases P <;> simp only [upperPhase,decode,upperAfter,upperBefore,lowerAfter,correction,signs]
  all_goals norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Int.cast_one,Int.cast_neg,neg_mul,one_mul]
  all_goals simp only [norm_add_sq_real,norm_sub_sq_real,inner_add_left,inner_add_right,
    inner_sub_left,inner_sub_right,inner_neg_right,
    real_inner_self_eq_norm_sq,real_inner_comm]
  all_goals ring

end RungPattern
end WaveTurbulence.Vine.Param
