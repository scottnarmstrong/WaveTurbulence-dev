/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideLadderData
public import WaveTurbulence.Foundations.Molecule.VineBlockJoints
public import WaveTurbulence.Foundations.Molecule.VineTriangleClosure
public import WaveTurbulence.Foundations.Molecule.VineSelectedRungs
public import WaveTurbulence.Foundations.Molecule.VineEmptyRungsReverse
import Mathlib.Tactic

/-! # A nontrivial block confined to the side ladder selects its whole core -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Selecting the triangle center selects every rung and both terminal
atoms of the side ladder. -/
theorem SideLadderData.full_of_center {M : Molecule V D} {c u v a b : V} {n : ℕ}
    (D : SideLadderData M c u v a b n) (hM : M.IsMolecule)
    {A : Finset V} {x y : V} (hB : M.IsBlock A x y) (hC : GroupConnected M A)
    (hcard : 2<A.card) (hc : c ∈ A) :
    ∀ i,i ≤ n+1 → D.ladder.u i ∈ A ∧ D.ladder.v i ∈ A := by
  classical
  have hdiff (i j : Fin 5) (hij : i ≠ j) :
      (![c,u,v,a,b] i) ≠ (![c,u,v,a,b] j) := fun he => hij (D.distinct he)
  have huv : M.Adj u v := ⟨D.upper_row.dart 2,D.upper_row.atom_eq 2,D.upper_row.neighbor_eq 2⟩
  have hcorners := block_double_triangle_corners_mem M hM hB hC hcard
    D.upper_row.rung.mates D.lower_row.rung.mates
    (hdiff 0 1 (by decide)) (hdiff 0 2 (by decide)) (hdiff 1 2 (by decide)) huv hc
  have hu1 := block_rung_next_mem M hM hB D.upper_row hcorners.1 hc hcorners.2
  have hv1 := block_rung_next_mem M hM hB D.lower_row hcorners.2 hc hcorners.1
  apply block_selected_fullRungSequence M hM hB D.ladder
  · simpa only [D.start_upper] using hcorners.1
  · simpa only [D.start_lower] using hcorners.2
  · exact hu1
  · exact hv1

omit [DecidableEq D] in
/-- A block larger than a double bond, confined to the side core and its
rungs, must select the center if a terminal atom has an external neighbor.
The conclusion follows from actual degree and joint constraints. -/
theorem SideLadderData.center_mem_of_region {M : Molecule V D} {c u v a b : V} {n : ℕ}
    (D : SideLadderData M c u v a b n) (hM : M.IsMolecule)
    {A : Finset V} {x y : V} (hB : M.IsBlock A x y) (hC : GroupConnected M A)
    (hcard : 2<A.card)
    (hregion : ∀ z ∈ A,z=c ∨ z=u ∨ z=v ∨ z=a ∨ z=b ∨
      ∃ i,1 ≤ i ∧ i ≤ n ∧ (z=D.ladder.u i ∨ z=D.ladder.v i))
    (hexit : ∃ p,p ∉ A ∧ M.Adj a p) : c ∈ A := by
  classical
  by_contra hc
  have hdiff (i j : Fin 5) (hij : i ≠ j) :
      (![c,u,v,a,b] i) ≠ (![c,u,v,a,b] j) := fun he => hij (D.distinct he)
  have huNot : u ∉ A := by
    intro hu
    have hv : v ∈ A := by
      by_contra hv
      exact hc (block_rung_partner_of_missing_rail M hM hB D.upper_row hu hv)
    have hu1 : D.ladder.u 1 ∈ A := by
      by_contra hh
      exact hc (block_rung_partner_of_missing_successor M hM hB D.upper_row hu hh)
    have hv1 : D.ladder.v 1 ∈ A := by
      by_contra hh
      exact hc (block_rung_partner_of_missing_successor M hM hB D.lower_row hv hh)
    have hu2 : M.degIn A u=2 := by
      have hmax := twoOutside_degree_le_two M hM D.upper_row.rung hc
      have hmin := block_degree_ge_two M hB hu
      omega
    have hv2 : M.degIn A v=2 := by
      have hmax := twoOutside_degree_le_two M hM D.lower_row.rung hc
      have hmin := block_degree_ge_two M hB hv
      omega
    have huj := block_degree_two_joint M hB hu hu2
    have hvj := block_degree_two_joint M hB hv hv2
    have hjpair : ({u,v} : Finset V)={x,y} := by
      rcases huj with rfl | rfl <;> rcases hvj with rfl | rfl
      · exact False.elim (hdiff 1 2 (by decide) rfl)
      · rfl
      · exact pair_comm _ _
      · exact False.elim (hdiff 1 2 (by decide) rfl)
    have hfull := block_selected_fullRungSequence M hM hB D.ladder
      (by simpa only [D.start_upper] using hu)
      (by simpa only [D.start_lower] using hv) hu1 hv1
    have ha : a ∈ A := by simpa only [D.end_upper] using (hfull (n+1) le_rfl).1
    obtain ⟨p,hp,hap⟩ := hexit
    have haj := block_joint_of_external_neighbor M hM hB ha hp hap
    have hm : a ∈ ({x,y} : Finset V) := by simpa only [mem_insert,mem_singleton] using haj
    rw [← hjpair] at hm
    simp only [mem_insert,mem_singleton] at hm
    exact hm.elim (hdiff 3 1 (by decide)) (hdiff 3 2 (by decide))
  have hvNot : v ∉ A := by
    intro hv
    by_cases hu : u ∈ A
    · exact huNot hu
    · exact hc (block_rung_partner_of_missing_rail M hM hB D.lower_row hv hu)
  have hempty := block_empty_fullRungSequence M hM hB hC hcard D.ladder
    (by simpa only [D.start_upper] using huNot)
    (by simpa only [D.start_lower] using hvNot)
  have hsub : A ⊆ ({a,b} : Finset V) := by
    intro z hz
    rcases hregion z hz with rfl | rfl | rfl | rfl | rfl | ⟨i,hi,hin,he⟩
    · exact False.elim (hc hz)
    · exact False.elim (huNot hz)
    · exact False.elim (hvNot hz)
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_singleton_self _)
    · rcases he with rfl | rfl
      · exact False.elim ((hempty i hi hin).1 hz)
      · exact False.elim ((hempty i hi hin).2 hz)
  have hpair := card_insert_le a ({b} : Finset V)
  rw [card_singleton] at hpair
  have hle := (card_le_card hsub).trans hpair
  omega

end WaveTurbulence.Vine
