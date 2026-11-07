/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalBondDarts

/-! # Exact equality of the dart conservation sum and M9 bond flow -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type*} [DecidableEq V] [Fintype D]

noncomputable def internalDartValue {E : Type*} (M : Molecule V D) (S : Finset V)
    (k : Bond M S → E) (x : InternalDart M S) : E :=
  k ((internalBondDartEquiv M S).symm x).1

theorem internalDartValue_bondDart {E : Type*} (M : Molecule V D) (S : Finset V)
    (k : Bond M S → E) (p : Bond M S × Bool) :
    internalDartValue M S k (internalBondDart M S p) = k p.1 := by
  change k (((internalBondDartEquiv M S).symm ((internalBondDartEquiv M S) p)).1) = k p.1
  rw [Equiv.symm_apply_apply]

/-- Outgoing and incoming occurrences are kept distinct, including loops. -/
def internalDartCoeff (M : Molecule V D) (v : V) (x : D) : ℤ :=
  if M.out x = true then (if M.atom x = v then 1 else 0) else -(if M.atom x = v then 1 else 0)

open Classical in
theorem internalDartFlow_eq_flow {E : Type*} [AddCommGroup E] (M : Molecule V D) (S : Finset V)
    (k : Bond M S → E) (v : V) :
    (∑ x : InternalDart M S, internalDartCoeff M v x.1 • internalDartValue M S k x) = flow M S k v := by
  classical
  calc
    _ = ∑ p : Bond M S × Bool,
        internalDartCoeff M v (internalBondDart M S p).1 • internalDartValue M S k (internalBondDart M S p) :=
      ((internalBondDartEquiv M S).sum_comp (fun x => internalDartCoeff M v x.1 • internalDartValue M S k x)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro e _
      rw [Fintype.sum_bool]
      simp only [internalDartValue_bondDart]
      have he := internalBond_out M S e
      have hm : M.out (M.mate e.1) = false := by rw [M.out_mate,he]; rfl
      simp only [internalBondDart,internalDartCoeff,he,hm,ite_true,Bool.false_eq_true,ite_false,
        incidence,sub_smul,neg_smul]
      by_cases hfirst : M.atom e.1 = v <;> by_cases hsecond : M.atom (M.mate e.1) = v <;>
        simp only [hfirst,hsecond,ite_true,ite_false,one_smul,zero_smul,neg_zero,neg_add_cancel,
          add_zero,zero_add,sub_self,sub_zero,zero_sub]

end WaveTurbulence.VineEstS2
