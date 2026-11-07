/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD33NeighborTable
public import WaveTurbulence.Foundations.FinalCount.AppBLinkDeletion
import Mathlib.Tactic

/-! # A degree-three double-pair removal loses at most one selected link -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbD33LinkAtoms {M : Molecule V D} (r : AppbRealization M AppbPatternKind.d33.pattern) : Finset V :=
  {r.vertex 1,r.vertex 2,r.vertex 3,r.vertex 4}

theorem appb_d33_linkAtoms_card (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) : (appbD33LinkAtoms r).card = 4 := by
  have hmap : ({1,2,3,4} : Finset ℕ).image r.vertex = appbD33LinkAtoms r := by simp [appbD33LinkAtoms]
  have hinj : Set.InjOn r.vertex ({1,2,3,4} : Finset ℕ) := by
    have he : AppbPatternKind.d33.pattern.vertices = {1,2,3,4} := by decide
    simpa only [he] using r.vertex_injective
  rw [← hmap,card_image_of_injOn hinj]
  decide

/-- Every old selected link touching either deleted atom is exactly the
four displayed atoms. The proof uses actual single and double neighbours. -/
theorem appb_d33_lost_link_eq (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern) {S : Finset V}
    (hS : AppbLink M S) (hdis : ¬Disjoint S r.removedAtoms) : S = appbD33LinkAtoms r := by
  have h12 : r.vertex 1 ≠ r.vertex 2 := by
    intro he
    have hh := r.vertex_injective (by decide : 1 ∈ AppbPatternKind.d33.pattern.vertices)
      (by decide : 2 ∈ AppbPatternKind.d33.pattern.vertices) he
    omega
  have hdouble := appb_d33_internal_multiplicity M r
  have hdouble' : M.bondsBetween (r.vertex 2) (r.vertex 1) = 2 := by
    rw [Degen.bondsBetween_comm]
    exact hdouble
  have h1 : r.vertex 1 ∈ S := by
    obtain ⟨a,ha,hY⟩ := not_disjoint_iff.mp hdis
    obtain ⟨b,hb,hba⟩ := mem_image.mp hY
    change b ∈ ({1,2} : Finset ℕ) at hb
    simp only [mem_insert,mem_singleton] at hb
    rw [← hba] at ha
    rcases hb with rfl | rfl
    · exact ha
    · exact hS.partner_mem hM ha h12.symm hdouble'
  have h2 := hS.partner_mem hM h1 h12 hdouble
  obtain ⟨c,hc,hnc,hc1⟩ := hS.single_neighbor h1
  have hcEq := appb_d33_single_neighbor_1 M r c hc1
  have h3 : r.vertex 3 ∈ S := hcEq ▸ hc
  obtain ⟨b,hb,hnb,hb1⟩ := hS.single_neighbor h2
  have hbEq := appb_d33_single_neighbor_2 M r b hb1
  have h4 : r.vertex 4 ∈ S := hbEq ▸ hb
  have hsub : appbD33LinkAtoms r ⊆ S := by
    intro x hx
    simp only [appbD33LinkAtoms,mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  exact (eq_of_subset_of_card_le hsub (by rw [hS.card,appb_d33_linkAtoms_card M r])).symm

/-- Exact link-family effect, with no logarithmic estimate. -/
theorem appb_d33_links_post (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern) :
    appbLinks r.post = (appbLinks M).erase (appbD33LinkAtoms r) := by
  classical
  change appbLinks (Degen.eraseAtoms M r.removedAtoms) = _
  rw [appbLinks_eraseAtoms]
  ext S
  by_cases hS : AppbLink M S
  · have hd : Disjoint S r.removedAtoms ↔ S ≠ appbD33LinkAtoms r := by
      constructor
      · intro h he
        subst S
        have hT : r.vertex 1 ∈ appbD33LinkAtoms r := by simp [appbD33LinkAtoms]
        have hY : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ (show 1 ∈ AppbPatternKind.d33.pattern.removed by decide)
        exact disjoint_left.mp h hT hY
      · intro hne
        by_contra hn
        exact hne (appb_d33_lost_link_eq M hM r hS hn)
    simp only [mem_filter,mem_appbLinks,hS,true_and,mem_erase,hd,and_true]
  · simp only [mem_filter,mem_appbLinks,hS,false_and,mem_erase,and_false]

end WaveTurbulence.Mole
