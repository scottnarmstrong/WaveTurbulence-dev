/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-!
# Adding and removing actual bonds; adjoints of blocks

TARGET `defblock`, DH23 Definition 4.10. A new bond has two new darts;
removing a bond removes both mates. Loops and multiple bonds are retained.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] (M : Molecule V D)

/-- Add one directed bond a→b, with its two distinct half-edges. -/
@[expose] def addBond (a b : V) : Molecule V (D ⊕ Bool) where
  atoms := insert a (insert b M.atoms)
  atom := Sum.elim M.atom (fun out => if out then a else b)
  mate := Sum.map M.mate Bool.not
  out := Sum.elim M.out id
  atom_mem := by
    rintro (x|out)
    · exact mem_insert_of_mem (mem_insert_of_mem (M.atom_mem x))
    · cases out <;> simp
  mate_mate := by rintro (x|out); exact congrArg Sum.inl (M.mate_mate x); cases out <;> rfl
  mate_ne := by
    rintro (x|out) h
    · exact M.mate_ne x (Sum.inl.inj h)
    · cases out <;> cases h
  out_mate := by rintro (x|out); exact M.out_mate x; rfl

/-- Remove the entire bond represented by e, not just one incidence. -/
@[expose] def eraseBond (e : D) : Molecule V {x : D // x ≠ e ∧ x ≠ M.mate e} where
  atoms := M.atoms
  atom := fun x => M.atom x.1
  mate := fun x => ⟨M.mate x.1,
    fun h => x.2.2 (by have hh := congrArg M.mate h; simpa only [M.mate_mate] using hh),
    fun h => x.2.1 (mate_injective M h)⟩
  out := fun x => M.out x.1
  atom_mem := fun x => M.atom_mem x.1
  mate_mate := fun x => Subtype.ext (M.mate_mate x.1)
  mate_ne := fun x h => M.mate_ne x.1 (congrArg Subtype.val h)
  out_mate := fun x => M.out_mate x.1

/-- A hyper-block is realized by deleting its added joint-to-joint bond
and obtaining an actual block on the same atom set. This realization
remembers which bond is added when parallel bonds occur. -/
@[expose] def IsHyperBlock [Fintype D] [DecidableEq D] (S : Finset V) (j1 j2 : V) : Prop :=
  ∃ e : D, M.ends e = s(j1,j2) ∧ (eraseBond M e).IsBlock S j1 j2

variable [Fintype D]

private theorem card_filter_sum (p : D ⊕ Bool → Prop) [DecidablePred p] :
    (univ.filter p).card = (univ.filter (fun x : D => p (.inl x))).card +
      (univ.filter (fun x : Bool => p (.inr x))).card := by
  have he : univ.filter p = (univ.filter (fun x : D => p (.inl x))).disjSum
      (univ.filter (fun x : Bool => p (.inr x))) := by
    ext x
    cases x <;> simp
  rw [he,Finset.card_disjSum]

/-- Adding one bond increases E by exactly one. -/
theorem addBond_card_bonds (a b : V) : (addBond M a b).bonds.card = M.bonds.card+1 := by
  change (univ.filter (fun x : D ⊕ Bool => (addBond M a b).out x = true)).card = _
  rw [card_filter_sum]
  change M.bonds.card + (univ.filter (fun x : Bool => x = true)).card = _
  have hb : (univ.filter (fun x : Bool => x = true)).card = 1 := by decide
  rw [hb]

/-- Both endpoints acquire one incidence; a loop acquires two. -/
theorem addBond_deg (a b v : V) :
    (addBond M a b).deg v = M.deg v + (if a = v then 1 else 0) + (if b = v then 1 else 0) := by
  change (univ.filter (fun x : D ⊕ Bool => (addBond M a b).atom x = v)).card = _
  rw [card_filter_sum]
  change M.deg v + (univ.filter (fun x : Bool => (if x then a else b) = v)).card = _
  rw [show (univ : Finset Bool) = {true,false} by decide]
  by_cases ha : a = v <;> by_cases hb : b = v <;> simp [ha,hb]
  all_goals decide

/-- The two joints of an actual block become degree three in its adjoint. -/
theorem block_adjoint_joint_degrees {S : Finset V} {j1 j2 : V} (hB : M.IsBlock S j1 j2) :
    (addBond (induced M S) j1 j2).deg j1 = 3 ∧
    (addBond (induced M S) j1 j2).deg j2 = 3 := by
  obtain ⟨h1,h2⟩ := block_joint_degrees M hB
  have hne := hB.2.2.2.1
  simp [addBond_deg,induced_deg,h1,h2,hne,Ne.symm hne]

end WaveTurbulence.Mole
