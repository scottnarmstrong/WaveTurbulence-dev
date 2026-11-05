/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapPrefixMembership
public import WaveTurbulence.Foundations.Molecule.VineHyperTransitions
public import WaveTurbulence.Foundations.Molecule.VineRungPairIndices
import Mathlib.Tactic

/-! # Actual hyper-block joints are exactly the front of primitive cap data -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- For two distinct actual atoms, equality of their unordered finite joint
sets gives equality of the corresponding undirected endpoint pairs. -/
theorem sym2_eq_of_finset_pair_eq {V : Type*} [DecidableEq V] {a b c d : V}
    (hne : a ≠ b) (he : ({a,b} : Finset V)={c,d}) : s(a,b)=s(c,d) := by
  have ha : a=c ∨ a=d := by
    have hh : a ∈ ({c,d} : Finset V) := he ▸ mem_insert_self a {b}
    simpa only [mem_insert,mem_singleton] using hh
  have hb : b=c ∨ b=d := by
    have hh : b ∈ ({c,d} : Finset V) := he ▸ mem_insert_of_mem (mem_singleton_self b)
    simpa only [mem_insert,mem_singleton] using hh
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (hne rfl)
  · rfl
  · exact Sym2.eq_swap
  · exact False.elim (hne rfl)

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace CapPrefixData
variable {M : Molecule V D} {A : Finset V} {n r : ℕ} (C : CapPrefixData M A n r)

/-- A cap with a nonempty selected prefix has its hyper-block joints at
the last selected full rung. -/
theorem hyper_front_joints_pos (hM : M.IsMolecule) {x y : V}
    (hH : Mole.IsHyperBlock M A x y) (hr : 1 ≤ r) :
    ({C.side.ladder.u r,C.side.ladder.v r} : Finset V)={x,y} := by
  have hru : C.side.ladder.u r ∈ A := (C.upper_mem_iff r hr (by have := C.r_le; omega)).mpr le_rfl
  have hrv : C.side.ladder.v r ∈ A := (C.lower_mem_iff r hr (by have := C.r_le; omega)).mpr le_rfl
  exact hyperBlock_transition_joints M hM hH (C.side.ladder.upper r hr C.r_le)
    (C.side.ladder.lower r hr C.r_le) hru hrv
    (C.side.ladder.upper_ne_lower hr C.r_le hr C.r_le)
    (Or.inr C.front_neighbors_absent.1) (Or.inr C.front_neighbors_absent.2)

/-- Positive-cap hyper-block joints have the exact last-rung cap labels. -/
theorem hyper_front_labels_pos (hM : M.IsMolecule) {x y : V}
    (hH : Mole.IsHyperBlock M A x y) (hr : 1 ≤ r) :
    s(C.label x,C.label y)=s(9+(r-1),9+r+(r-1)) := by
  have hp := C.hyper_front_joints_pos hM hH hr
  have hs := sym2_eq_of_finset_pair_eq
    (C.side.ladder.upper_ne_lower hr C.r_le hr C.r_le) hp
  have hh := congrArg (Sym2.map C.label) hs
  rw [Sym2.map_mk,Sym2.map_mk,C.label_upper r hr le_rfl,C.label_lower r hr le_rfl] at hh
  exact hh.symm

/-- With no selected rung, both triangle legs and no other atoms are the
hyper-block joints. -/
theorem hyper_front_joints_zero (hM : M.IsMolecule) {x y : V}
    (hH : Mole.IsHyperBlock M A x y) (hr : r=0) :
    ({C.upper,C.lower} : Finset V)={x,y} := by
  have hfront := C.front_neighbors_absent
  rw [show r+1=1 by omega] at hfront
  have huj := hyperBlock_joint_of_degree_le_three M hH C.triangle_mem.2.1
    (rung_degree_le_three M hM C.side.upper_row C.triangle_mem.2.1 (Or.inr hfront.1))
  have hvj := hyperBlock_joint_of_degree_le_three M hH C.triangle_mem.2.2
    (rung_degree_le_three M hM C.side.lower_row C.triangle_mem.2.2 (Or.inr hfront.2))
  have hne : C.upper ≠ C.lower := by
    intro hh
    have he : (1 : Fin 5)=2 := C.side.distinct (by exact hh)
    have hv := congrArg Fin.val he
    norm_num at hv
  rcases huj with hux | huy <;> rcases hvj with hvx | hvy
  · exact False.elim (hne (hux.trans hvx.symm))
  · rw [hux,hvy]
  · rw [huy,hvx]
    exact pair_comm _ _
  · exact False.elim (hne (huy.trans hvy.symm))

end CapPrefixData
end WaveTurbulence.Vine
