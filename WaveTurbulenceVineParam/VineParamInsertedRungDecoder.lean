/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamAnchoredRestCoefficients
import Mathlib.Tactic

/-! # Explicit affine unit decoder for both actual new rung bonds -/

public section
namespace WaveTurbulence.Vine.Param
variable {ι : Type*}

/-- The old rail decoder and the two new columns occupy disjoint slots. -/
@[expose] def insertedRungFree (P : RungPattern) (anchor : Bool) (row : Fin 2)
    (A : ι → ℤ) : ι ⊕ Fin 2 → ℤ :=
  Sum.elim A ![-gaugeDecodeRows P anchor row 1,gaugeDecodeRows P anchor row 2]

/-- The gap column incorporates the physical cap gap sign. -/
@[expose] def insertedRungGap (P : RungPattern) (anchor : Bool) (row : Fin 2) (D ε : ℤ) : ℤ :=
  D+gaugeDecodeRows P anchor row 3*ε

/-- The complete decoder retains the ternary free coefficient bound. -/
theorem insertedRungFree_unit (P : RungPattern) (anchor : Bool) (row : Fin 2) (A : ι → ℤ)
    (hA : ∀ i,A i ∈ ({-1,0,1} : Finset ℤ)) :
    ∀ i,insertedRungFree P anchor row A i ∈ ({-1,0,1} : Finset ℤ) := by
  intro i
  cases i with
  | inl i => exact hA i
  | inr i =>
    simp only [insertedRungFree,Sum.elim_inr]
    cases P <;> cases anchor <;> fin_cases row <;> fin_cases i <;> decide

/-- Both physical new rung labels have the exact affine integer decoder
with coefficient1 on g and ternary free columns. -/
theorem insertedRungFree_eval {E : Type*} [AddCommGroup E] [Fintype ι]
    (P : RungPattern) (anchor : Bool) (row : Fin 2) (A : ι → ℤ) (D ε : ℤ) (g r : E)
    (x : ι ⊕ Fin 2 → E) :
    ![(P.decode (g+(∑ i,A i • x (.inl i))+D • r+
        (if anchor then P.correction (ε • r) (-x (.inr 0),x (.inr 1)) else 0))
        (-x (.inr 0),x (.inr 1))).1,
      (P.decode (g+(∑ i,A i • x (.inl i))+D • r+
        (if anchor then P.correction (ε • r) (-x (.inr 0),x (.inr 1)) else 0))
        (-x (.inr 0),x (.inr 1))).2] row=
      g+(∑ i,insertedRungFree P anchor row A i • x i)+insertedRungGap P anchor row D ε • r := by
  have h := congrFun (gaugeDecodeRows_eval P anchor (g+(∑ i,A i • x (.inl i))+D • r)
    (ε • r) (-x (.inr 0),x (.inr 1))) row
  rw [← h,Fintype.sum_sum_type]
  simp only [intEval,insertedRungFree,insertedRungGap,Sum.elim_inl,Sum.elim_inr,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    gaugeDecodeRows_rail,one_zsmul,add_zero,neg_smul,add_smul,mul_smul]
  abel_nf
  simp only [neg_one_zsmul,smul_neg]

end WaveTurbulence.Vine.Param
