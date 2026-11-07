/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.CutLabelEquations
import Mathlib.Tactic

/-! # Old cut momentum fixes one label once the others are fixed

This is used inside actual counting fibers. The old cut need not be a
singleton; bridge labels after an R step can depend on several first-star
labels, all of which are part of the actual counted profile.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem cut_label_unique_of_other_labels (M : Molecule V D) {d : ℕ} {L : ℝ}
    (hL : L ≠ 0) {w : Mom d} {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L w c κ) (hd' : M.IsDecoration L w c κ')
    (U : Finset V) (hU : U ⊆ M.atoms) (e : D) (he : e ∈ Degen.boundaryDarts M U)
    (hother : ∀ x ∈ Degen.boundaryDarts M U, x ≠ e → κ x = κ' x) : κ e = κ' e := by
  have hs : (∑ x ∈ Degen.boundaryDarts M U, M.dartSign x • Molecule.kvec L w κ x) =
      ∑ x ∈ Degen.boundaryDarts M U, M.dartSign x • Molecule.kvec L w κ' x :=
    (Degen.cut_momentum M hd U hU).trans (Degen.cut_momentum M hd' U hU).symm
  have hrem : (∑ x ∈ (Degen.boundaryDarts M U).erase e, M.dartSign x • Molecule.kvec L w κ x) =
      ∑ x ∈ (Degen.boundaryDarts M U).erase e, M.dartSign x • Molecule.kvec L w κ' x := by
    apply sum_congr rfl
    intro x hx
    have heq := hother x (mem_erase.mp hx).2 (mem_erase.mp hx).1
    simp only [Molecule.kvec,heq]
  rw [← add_sum_erase _ (fun x => M.dartSign x • Molecule.kvec L w κ x) he,
    ← add_sum_erase _ (fun x => M.dartSign x • Molecule.kvec L w κ' x) he,hrem] at hs
  have hsgn := add_right_cancel hs
  have hphys : Molecule.kvec L w κ e = Molecule.kvec L w κ' e := by
    cases ho : M.out e <;> simpa only [Molecule.dartSign,ho,Bool.false_eq_true,ite_false,ite_true,
      neg_one_smul,one_smul,neg_inj] using hsgn
  exact Degen.coset_label_injective hL w hphys

end WaveTurbulence.MoleProp
