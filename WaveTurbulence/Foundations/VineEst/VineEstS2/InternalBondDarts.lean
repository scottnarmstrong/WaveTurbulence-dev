/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulenceVineParam.Contract

/-! # Actual internal bonds and their two dart incidences -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type*} [DecidableEq V] [Fintype D]

abbrev InternalDart (M : Molecule V D) (S : Finset V) := {x : D // M.InGroup S x}

omit [DecidableEq V] [Fintype D] in
theorem inGroup_mate (M : Molecule V D) (S : Finset V) (x : D) :
    M.InGroup S (M.mate x) ↔ M.InGroup S x := by
  simp only [Molecule.InGroup,M.mate_mate,and_comm]

theorem internalBond_out (M : Molecule V D) (S : Finset V) (e : Bond M S) : M.out e.1 = true :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp e.2).1).2

theorem internalBond_inGroup (M : Molecule V D) (S : Finset V) (e : Bond M S) : M.InGroup S e.1 :=
  (Finset.mem_filter.mp e.2).2

noncomputable def internalBondDart (M : Molecule V D) (S : Finset V) : Bond M S × Bool → InternalDart M S
  | (e,false) => ⟨e.1,internalBond_inGroup M S e⟩
  | (e,true) => ⟨M.mate e.1,(inGroup_mate M S e.1).mpr (internalBond_inGroup M S e)⟩

noncomputable def internalDartBond (M : Molecule V D) (S : Finset V)
    (x : InternalDart M S) : Bond M S × Bool := by
  classical
  by_cases hx : M.out x.1 = true
  · exact (⟨x.1,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,x.2⟩⟩,false)
  · have hm : M.out (M.mate x.1) = true := by rw [M.out_mate,Bool.eq_false_of_not_eq_true hx]; rfl
    exact (⟨M.mate x.1,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩,(inGroup_mate M S x.1).mpr x.2⟩⟩,true)

/-- No orientation or multiplicity is dropped: loops still have two darts. -/
noncomputable def internalBondDartEquiv (M : Molecule V D) (S : Finset V) :
    Bond M S × Bool ≃ InternalDart M S where
  toFun := internalBondDart M S
  invFun := internalDartBond M S
  left_inv := by
    rintro ⟨e,s⟩
    cases s
    · change internalDartBond M S ⟨e.1,internalBond_inGroup M S e⟩ = (e,false)
      unfold internalDartBond
      rw [dite_eq_left (internalBond_out M S e)]
    · have ho : M.out (M.mate e.1) = false := by rw [M.out_mate,internalBond_out]; rfl
      simp only [internalBondDart,internalDartBond,ho,Bool.false_eq_true,dite_false,M.mate_mate]
  right_inv := by
    intro x
    unfold internalDartBond
    split_ifs <;> simp only [internalBondDart,M.mate_mate]

end WaveTurbulence.VineEstS2
