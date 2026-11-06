/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamAnchoredRestDecoder
import Mathlib.Tactic

/-! # Explicit ternary free coefficients of every uncut inserted label -/

public section
namespace WaveTurbulence.Vine.Param
variable {ι : Type*}

/-- Old and new free slots are disjoint, so their coefficients do not add. -/
@[expose] def insertedRestFree (P : RungPattern) (anchor bond : Bool) (A : ι → ℤ) : ι ⊕ Fin 2 → ℤ :=
  Sum.elim A ![-capGauge anchor bond*P.coefficients 0,capGauge anchor bond*P.coefficients 1]

/-- The physical gap coefficient is unrestricted, as in the exact V4 contract. -/
@[expose] def insertedRestGap (P : RungPattern) (anchor bond : Bool) (D ε : ℤ) : ℤ :=
  D+capGauge anchor bond*P.coefficients 2*ε

/-- Every old unit coefficient and both local cap corrections remain units. -/
theorem insertedRestFree_unit (P : RungPattern) (anchor bond : Bool) (A : ι → ℤ)
    (hA : ∀ i,A i ∈ ({-1,0,1} : Finset ℤ)) :
    ∀ i,insertedRestFree P anchor bond A i ∈ ({-1,0,1} : Finset ℤ) := by
  intro i
  cases i with
  | inl i => exact hA i
  | inr i =>
    simp only [insertedRestFree,Sum.elim_inr]
    cases P <;> cases anchor <;> cases bond <;> fin_cases i <;> decide

/-- Evaluation of the new integer decoder is exactly the old decoder plus
the cap/reference correction. The identity holds over arbitrary groups. -/
theorem insertedRestFree_eval {E : Type*} [AddCommGroup E] [Fintype ι]
    (P : RungPattern) (anchor bond : Bool) (A : ι → ℤ) (D ε : ℤ) (r : E)
    (x : ι ⊕ Fin 2 → E) :
    (∑ i,insertedRestFree P anchor bond A i • x i)+insertedRestGap P anchor bond D ε • r=
      (∑ i,A i • x (.inl i))+D • r+
        capGauge anchor bond • P.correction (ε • r) (-x (.inr 0),x (.inr 1)) := by
  rw [Fintype.sum_sum_type,P.correction_coefficients]
  simp only [insertedRestFree,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_succ,
    Matrix.cons_val_zero,
    Fin.sum_univ_zero,add_zero,insertedRestGap,add_smul,mul_smul,neg_smul,smul_neg,smul_add]
  abel_nf
  simp only [mul_smul]
  abel

end WaveTurbulence.Vine.Param
