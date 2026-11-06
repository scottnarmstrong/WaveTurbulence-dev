/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamDirectedBondModel
import Mathlib.Tactic

/-! # Exact included-atom deletion through an actual directed bond model -/

public section
namespace WaveTurbulence.Vine.Param.DirectedBondModel
open Finset
variable {V D A β : Type*} [DecidableEq V] [Fintype D] [DecidableEq A] [Fintype A] [Fintype β]
  {M : Molecule V D} {S : Finset V}
variable (Q : DirectedBondModel M S A β)

/-- Deleting a designated source atom commutes with the actual atom
realization. Both maps retain literal actual atom values. -/
@[expose] noncomputable def erasedAtomEquiv (a : A) :
    ↥((univ : Finset A).erase a) ≃ ↥(S.erase (Q.atom a).1) := by
  classical
  refine {
    toFun := fun v => ⟨(Q.atom v.1).1,mem_erase.mpr ⟨?_,(Q.atom v.1).2⟩⟩
    invFun := fun v => ⟨Q.atom.symm ⟨v.1,(mem_erase.mp v.2).2⟩,mem_erase.mpr ⟨?_,mem_univ _⟩⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro h
    exact (mem_erase.mp v.2).1 ((Q.atom_val_eq_iff v.1 a).mp h)
  · intro h
    have hv := congrArg Subtype.val (Q.atom.apply_symm_apply ⟨v.1,(mem_erase.mp v.2).2⟩)
    rw [h] at hv
    exact (mem_erase.mp v.2).1 hv.symm
  · intro v
    apply Subtype.ext
    exact Q.atom.symm_apply_apply v.1
  · intro v
    apply Subtype.ext
    change (Q.atom (Q.atom.symm ⟨v.1,(mem_erase.mp v.2).2⟩)).1=v.1
    exact congrArg Subtype.val (Q.atom.apply_symm_apply ⟨v.1,(mem_erase.mp v.2).2⟩)

/-- The included atom realization is literally the old atom value mapped
by the fixed source atom equivalence. -/
theorem erasedAtomEquiv_value (a : A) (v : ↥((univ : Finset A).erase a)) :
    (Q.erasedAtomEquiv a v).1=(Q.atom v.1).1 := rfl

end WaveTurbulence.Vine.Param.DirectedBondModel
