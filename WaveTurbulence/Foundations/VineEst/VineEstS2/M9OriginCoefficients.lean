/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulenceVineParam.Contract
public import WaveTurbulence.Foundations.VineEst.VineEstS2.IntegerLinearPhaseFactors

/-! # Integer coefficients of actual chart origin differences -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type} [DecidableEq V] [Fintype D] {M : Molecule V D}
variable {X : VineType} {S : Finset V} {a b : V}

abbrev ChartAffineIndex (A : FullVineChart M X S a b) := Fin A.indexing.shape.n ⊕ Unit

def chartOriginCoeff (A : FullVineChart M X S a b) :
    Bond M S ⊕ Fin 2 → ChartAffineIndex A → ℤ
  | .inl e,.inl i => A.decodeFree e i
  | .inl e,.inr _ => A.decodeGap e
  | .inr _,.inl _ => 0
  | .inr j,.inr _ => if j = 0 then 0 else -1

def chartDifferenceCoeff (A : FullVineChart M X S a b) (p q : Bond M S ⊕ Fin 2) : ChartAffineIndex A → ℤ :=
  fun i => chartOriginCoeff A p i-chartOriginCoeff A q i

/-- All actual origins share the same anchor g, so their difference is a
homogeneous integer form on free coordinates and the one gap coordinate. -/
theorem chartOrigin_affine (A : FullVineChart M X S a b)
    {E : Type} [AddCommGroup E] (g r : E) (x : Fin A.indexing.shape.n → E) (p : Bond M S ⊕ Fin 2) :
    origin M S ((A.chart g r).symm x).1 g r p =
      g+∑ i : ChartAffineIndex A, chartOriginCoeff A p i • Sum.elim x (fun _ => r) i := by
  rw [Fintype.sum_sum_type]
  cases p with
  | inl e =>
    simp only [origin,chartOriginCoeff,Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique]
    rw [A.decode_eq]
    abel
  | inr j =>
    simp only [origin,chartOriginCoeff,Sum.elim_inl,Sum.elim_inr,zero_smul,Finset.sum_const_zero,
      Fintype.sum_unique,zero_add]
    by_cases hj : j = 0 <;> simp only [hj,ite_true,ite_false,zero_smul,add_zero,neg_one_zsmul,sub_eq_add_neg]

theorem chartOrigin_difference (A : FullVineChart M X S a b)
    {E : Type} [AddCommGroup E] (g r : E) (x : Fin A.indexing.shape.n → E) (p q : Bond M S ⊕ Fin 2) :
    origin M S ((A.chart g r).symm x).1 g r p-origin M S ((A.chart g r).symm x).1 g r q =
      ∑ i : ChartAffineIndex A, chartDifferenceCoeff A p q i • Sum.elim x (fun _ => r) i := by
  rw [chartOrigin_affine,chartOrigin_affine,add_sub_add_left_eq_sub,← Finset.sum_sub_distrib]
  simp only [chartDifferenceCoeff,sub_smul]

end WaveTurbulence.VineEstS2
