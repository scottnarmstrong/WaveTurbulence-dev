/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceEnergyLaw
public import WaveTurbulenceVineParam.VineParamCapGauge
import Mathlib.Tactic

/-! # Retaining the physical joint reference during source rung insertion -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {ι E : Type*} [DecidableEq ι] [AddCommGroup E]

/-- Reanchor only the joint reference coordinate after cap contraction.
The remaining old differences and both new differences are retained. -/
@[expose] def referenceShear (P : RungPattern) (inside : Bool) (ref : ι) (r : E) :
    ((ι → E)×(E×E)) ≃ ((ι → E)×(E×E)) where
  toFun := fun q => (fun i => q.1 i+(if i=ref ∧ inside=true then P.correction r q.2 else 0),q.2)
  invFun := fun q => (fun i => q.1 i-(if i=ref ∧ inside=true then P.correction r q.2 else 0),q.2)
  left_inv := by
    intro q
    apply Prod.ext
    · funext i
      exact add_sub_cancel_right _ _
    · rfl
  right_inv := by
    intro q
    apply Prod.ext
    · funext i
      exact sub_add_cancel _ _
    · rfl

/-- The exact inverse of reanchoring subtracts only the cap-reference shift. -/
theorem referenceShear_symm (P : RungPattern) (inside : Bool) (ref : ι) (r : E)
    (q : (ι → E)×(E×E)) (i : ι) :
    ((referenceShear P inside ref r).symm q).1 i=
      q.1 i-(if i=ref ∧ inside=true then P.correction r q.2 else 0) := rfl

/-- A decoder whose reference coefficient is -1 acquires exactly the
uniform reference correction, independently of every other coordinate. -/
theorem referenceShear_decoder [Fintype ι] (P : RungPattern) (inside : Bool) (ref : ι) (r : E)
    (A : ι → ℤ) (href : A ref= -1) (q : (ι → E)×(E×E)) :
    (∑ i,A i • ((referenceShear P inside ref r).symm q).1 i)=
      (∑ i,A i • q.1 i)+(if inside then P.correction r q.2 else 0) := by
  simp only [referenceShear_symm,smul_sub,sum_sub_distrib]
  have hsum : (∑ i,A i • (if i=ref ∧ inside=true then P.correction r q.2 else 0))=
      -(if inside then P.correction r q.2 else 0) := by
    cases inside <;> simp [href]
  rw [hsum,sub_neg_eq_add]

end WaveTurbulence.Vine.Param
