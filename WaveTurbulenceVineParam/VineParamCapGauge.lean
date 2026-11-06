/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamRungCapTransport
public import WaveTurbulenceVineParam.VineParamIntegerMatrices
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

/-! # Integral cap translation with a fixed physical reference coordinate

If the included joint lies in a cap, its reference coordinate is adjusted
by the rung correction. The resulting old-label shift has coefficients
zero or plus/minus one. The two new rung labels retain the same bound in
all twelve orientation/reference cases.
-/

public section
namespace WaveTurbulence.Vine.Param

/-- Shift sign at an old bond, after retaining the included-joint reference. -/
@[expose] def capGauge (anchorInside bondInside : Bool) : ℤ :=
  (if anchorInside then 1 else 0)-(if bondInside then 1 else 0)

/-- Reanchoring can only shift an old label by zero or one signed correction. -/
theorem capGauge_mem (a b : Bool) : capGauge a b ∈ ({-1,0,1} : Finset ℤ) := by
  cases a <;> cases b <;> decide

/-- The designated reference bond keeps exactly its physical value. -/
theorem capGauge_reference (a : Bool) : capGauge a a=0 := by cases a <;> rfl

/-- The exact new-label rows in coordinates (old rail, x, y, gap). -/
@[expose] def gaugeDecodeRows (P : RungPattern) (anchorInside : Bool) : Matrix (Fin 2) (Fin 4) ℤ :=
  match P,anchorInside with
  | .pp,false => ![![1,0,1,0],![1,-1,0,0]]
  | .pp,true => ![![1,1,0,1],![1,0,-1,1]]
  | .pmForward,false => ![![1,0,1,0],![1,-1,1,0]]
  | .pmForward,true => ![![1,1,1,0],![1,0,1,0]]
  | .pmBackward,false => ![![1,1,1,0],![1,0,1,0]]
  | .pmBackward,true => ![![1,0,1,0],![1,-1,1,0]]
  | .mpForward,false => ![![1,-1,1,0],![1,0,1,0]]
  | .mpForward,true => ![![1,0,1,0],![1,1,1,0]]
  | .mpBackward,false => ![![1,0,1,0],![1,1,1,0]]
  | .mpBackward,true => ![![1,-1,1,0],![1,0,1,0]]
  | .mm,false => ![![1,0,1,0],![1,1,0,0]]
  | .mm,true => ![![1,-1,0,-1],![1,0,-1,-1]]

/-- All twelve local decoder matrices have the source ternary coefficients. -/
theorem gaugeDecodeRows_mem (P : RungPattern) (a : Bool) :
    ∀ i j,gaugeDecodeRows P a i j ∈ ({-1,0,1} : Finset ℤ) := by
  cases P <;> cases a <;> intro i j <;> fin_cases i <;> fin_cases j <;> norm_num [gaugeDecodeRows]

/-- Every decoded new label retains coefficient one on the old physical rail. -/
theorem gaugeDecodeRows_rail (P : RungPattern) (a : Bool) :
    ∀ i,gaugeDecodeRows P a i 0=1 := by cases P <;> cases a <;> decide

/-- The rows are the actual rung decoder after the cap reference adjustment,
proved over arbitrary additive groups and hence on the integer lattice. -/
theorem gaugeDecodeRows_eval {E : Type*} [AddCommGroup E]
    (P : RungPattern) (a : Bool) (d r : E) (xy : E×E) :
    intEval (gaugeDecodeRows P a) ![d,xy.1,xy.2,r]=
      ![(P.decode (d+(if a then P.correction r xy else 0)) xy).1,
        (P.decode (d+(if a then P.correction r xy else 0)) xy).2] := by
  cases P <;> cases a <;> funext i <;> fin_cases i
  all_goals simp [intEval,gaugeDecodeRows,RungPattern.decode,RungPattern.correction,
    Fin.sum_univ_succ]
  all_goals abel

/-- Each old-label correction coefficient remains ternary after reanchoring. -/
theorem capGauge_coeff_mem (P : RungPattern) (a b : Bool) :
    ∀ i,capGauge a b*P.coefficients i ∈ ({-1,0,1} : Finset ℤ) := by
  cases P <;> cases a <;> cases b <;> decide

section Additive
variable {ι E : Type*} [AddCommGroup E]

/-- Apply the exact cap/reference adjustment to all old physical labels. -/
@[expose] def gaugeShift (P : RungPattern) (a : Bool) (inside : ι → Bool)
    (r : E) (xy : E×E) (k : ι → E) : ι → E :=
  fun j => k j+capGauge a (inside j) • P.correction r xy

/-- For fixed new rung coordinates, the old-label shift is an integral affine
bijection. Its inverse subtracts precisely the same actual correction. -/
@[expose] def gaugeShiftEquiv (P : RungPattern) (a : Bool) (inside : ι → Bool)
    (r : E) (xy : E×E) : (ι → E) ≃ (ι → E) where
  toFun := gaugeShift P a inside r xy
  invFun := fun k j => k j-capGauge a (inside j) • P.correction r xy
  left_inv := by intro k; funext j; simp only [gaugeShift,add_sub_cancel_right]
  right_inv := by intro k; funext j; simp only [gaugeShift,sub_add_cancel]

/-- The actual designated reference value is preserved by the cap adjustment. -/
theorem gaugeShift_reference (P : RungPattern) (a : Bool) (inside : ι → Bool)
    (r : E) (xy : E×E) (k : ι → E) (j : ι) (hj : inside j=a) :
    gaugeShift P a inside r xy k j=k j := by
  simp only [gaugeShift,hj,capGauge_reference,zero_zsmul,add_zero]

end Additive
end WaveTurbulence.Vine.Param
