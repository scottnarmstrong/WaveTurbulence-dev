/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarPair
import Mathlib.Tactic

/-! # Actual degree-three equations with one prescribed label

Subtracting the fixed third incidence gives the canonical two-variable
momentum and energy constraints, for every orientation pattern.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem ordered_fixed_third_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    {v : V} (hv : v ∈ M.atoms) (e : Fin 3 ≃ IncidentDart M v)
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} {q : Fin d → ℤ}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hq : κ (e 2).val = q) :
    latticePoint L (κ (e 0).val) +
      (pairUnit (M.out (e 0).val) (M.out (e 1).val) : ℤ) • latticePoint L (κ (e 1).val) =
        if M.out (e 0).val then c v - M.dartSign (e 2).val • latticePoint L q
        else -(c v - M.dartSign (e 2).val • latticePoint L q) := by
  have h := ordered_star_momentum M L (0 : Mom d) hv e hd
  simp only [Fin.sum_univ_three] at h
  cases h0 : M.out (e 0).val <;> cases h1 : M.out (e 1).val <;> cases h2 : M.out (e 2).val <;>
    simp [Molecule.dartSign,pairUnit,h0,h1,h2,Molecule.kvec,hq] at h ⊢ <;>
    rw [← h] <;> abel

theorem ordered_fixed_third_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {v : V} (hv : v ∈ M.atoms) (e : Fin 3 ≃ IncidentDart M v)
    {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)} {q : Fin d → ℤ}
    (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) (hq : κ (e 2).val = q) :
    |‖latticePoint L (κ (e 0).val)‖ ^ 2 +
      (pairUnit (M.out (e 0).val) (M.out (e 1).val) : ℤ) * ‖latticePoint L (κ (e 1).val)‖ ^ 2 -
      (if M.out (e 0).val then β v - M.dartSign (e 2).val * ‖latticePoint L q‖ ^ 2
       else -(β v - M.dartSign (e 2).val * ‖latticePoint L q‖ ^ 2))| ≤ δ⁻¹ * L ^ (-2*γ) := by
  have h := ordered_star_energy M L γ δ (0 : Mom d) hv e hr
  simp only [Fin.sum_univ_three] at h
  cases h0 : M.out (e 0).val
  · cases h1 : M.out (e 1).val <;> cases h2 : M.out (e 2).val <;>
      simp [Molecule.dartSign,pairUnit,h0,h1,h2,Molecule.kvec,hq] at h ⊢ <;>
      rw [← abs_neg] at h <;> convert h using 1 <;> congr 1 <;> ring
  · cases h1 : M.out (e 1).val <;> cases h2 : M.out (e 2).val <;>
      simp [Molecule.dartSign,pairUnit,h0,h1,h2,Molecule.kvec,hq] at h ⊢ <;>
      convert h using 1 <;> congr 1 <;> ring

theorem ordered_fixed_third_integer_momentum_eq (M : Molecule V D) {d : ℕ} {L : ℝ}
    (hL : L ≠ 0) {v : V} (hv : v ∈ M.atoms) (e : Fin 3 ≃ IncidentDart M v)
    {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)} {q : Fin d → ℤ}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd' : M.IsDecoration L (0 : Mom d) c κ')
    (hq : κ (e 2).val = q) (hq' : κ' (e 2).val = q) :
    κ (e 0).val + (pairUnit (M.out (e 0).val) (M.out (e 1).val) : ℤ) • κ (e 1).val =
      κ' (e 0).val + (pairUnit (M.out (e 0).val) (M.out (e 1).val) : ℤ) • κ' (e 1).val := by
  have h := (ordered_fixed_third_momentum M L hv e hd hq).trans
    (ordered_fixed_third_momentum M L hv e hd' hq').symm
  apply Degen.coset_label_injective hL (0 : Mom d)
  simpa only [zero_add,latticePoint_pairUnit_add] using h

/-- The enumeration placing a chosen actual incidence last is constructed
from the actual degree, with no additional orientation premise. -/
theorem exists_three_enumeration_last (M : Molecule V D) {v : V}
    (hdeg : M.deg v = 3) (x : D) (hx : M.atom x = v) :
    ∃ e : Fin 3 ≃ IncidentDart M v, (e 2).val = x := by
  classical
  let e0 : Fin 3 ≃ IncidentDart M v :=
    (Fintype.equivFinOfCardEq ((card_incidentDart M v).trans hdeg)).symm
  let e := (Equiv.swap (2 : Fin 3) (e0.symm ⟨x,hx⟩)).trans e0
  refine ⟨e,?_⟩
  simp only [e,Equiv.trans_apply,Equiv.swap_apply_left,Equiv.apply_symm_apply]

end WaveTurbulence.MoleProp
