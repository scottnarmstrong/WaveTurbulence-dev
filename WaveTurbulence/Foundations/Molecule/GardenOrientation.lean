/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenIncidence
import Mathlib.Tactic

/-!
# Actual incoming and outgoing degree bounds for garden molecules

TARGET `defcplmol` and `propcplmol`, L1297–L1306: the child signs determine
which two of the four incidence positions may point outwards. The other
two point inwards. No molecule axiom is assumed to prove these bounds.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

private theorem child_out_profile (v : GBranch G.tree) (i : Fin 3) :
    decide (G.sign (v.child i) ≠ 1) =
      if G.sign v.toNode = 1 then decide (i.succ.val%2 = 0) else decide (i.succ.val%2 = 1) := by
  have hsign : G.sign (v.child 0) = G.sign v.toNode ∧
      G.sign (v.child 1) = -G.sign v.toNode ∧ G.sign (v.child 2) = G.sign v.toNode := by
    simp [Garden.sign,nodeSign,TTree.pathSign,GBranch.child,List.count_append,pow_succ,GBranch.toNode]
  rcases Int.units_eq_one_or (G.sign v.toNode) with hs | hs
  · fin_cases i <;> simp [hsign.1,hsign.2.1,hsign.2.2,hs]
  · fin_cases i <;> simp [hsign.1,hsign.2.1,hsign.2.2,hs]

private theorem nonroot_out_profile (a : GNode G.tree) (ha : a.1.2 ≠ []) :
    decide (G.sign a ≠ 1) =
      if G.sign (GNode.parent a ha).toNode = 1 then decide ((a.1.2.getLast ha).succ.val%2 = 0)
      else decide ((a.1.2.getLast ha).succ.val%2 = 1) := by
  have he := child_out_profile G (GNode.parent a ha) (a.1.2.getLast ha)
  rw [parent_child_eq_node] at he
  exact he

/-- Exact orientation from the source sign and actual incidence position. -/
theorem dart_out_profile (x : GardenDart G) :
    G.molecule.out x =
      if G.sign (G.molecule.atom x).toNode = 1 then decide ((dartPosition G x).val%2 = 0)
      else decide ((dartPosition G x).val%2 = 1) := by
  rcases x with ⟨c,_|_⟩ | l
  · change decide (G.sign c.1.toNode = 1) =
      if G.sign c.1.toNode = 1 then decide ((0:Fin 4).val%2 = 0) else decide ((0:Fin 4).val%2 = 1)
    by_cases hs : G.sign c.1.toNode = 1 <;> simp [hs]
  · exact nonroot_out_profile G c.1.toNode c.2
  · exact nonroot_out_profile G l.1.toNode l.2.2.1

private theorem card_oriented_incidence_le_two (v : GBranch G.tree) (b : Bool) :
    ((G.molecule.dartsAt v).filter (fun x => G.molecule.out x = b)).card ≤ 2 := by
  let S := (G.molecule.dartsAt v).filter (fun x => G.molecule.out x = b)
  let T : Finset (Fin 4) := Finset.univ.filter (fun i =>
    (if G.sign v.toNode = 1 then decide (i.val%2 = 0) else decide (i.val%2 = 1)) = b)
  have hT : T.card = 2 := by
    dsimp only [T]
    by_cases hs : G.sign v.toNode = 1
    · simp only [hs,ite_true]
      cases b <;> decide
    · simp only [hs,ite_false]
      cases b <;> decide
  have hinj : Set.InjOn (dartPosition G) S := by
    intro x hx y hy hxy
    apply atom_position_injective G
    apply Prod.ext
    · have hxv := (mem_dartsAt G.molecule v x).mp (Finset.mem_filter.mp hx).1
      have hyv := (mem_dartsAt G.molecule v y).mp (Finset.mem_filter.mp hy).1
      exact hxv.trans hyv.symm
    · exact hxy
  have hsub : S.image (dartPosition G) ⊆ T := by
    intro i hi
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hxv,hxb⟩ := Finset.mem_filter.mp hx
    have hv := (mem_dartsAt G.molecule v x).mp hxv
    have hp := dart_out_profile G x
    rw [hv] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp.symm.trans hxb⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj,hT] at hcard
  exact hcard

/-- Actual garden molecules satisfy the outgoing part of molecule axiom (i). -/
theorem garden_molecule_outdeg_le_two (v : GBranch G.tree) : G.molecule.outdeg v ≤ 2 :=
  card_oriented_incidence_le_two G v true

/-- Actual garden molecules satisfy the incoming part of molecule axiom (i). -/
theorem garden_molecule_indeg_le_two (v : GBranch G.tree) : G.molecule.indeg v ≤ 2 :=
  card_oriented_incidence_le_two G v false

end WaveTurbulence.Mole
