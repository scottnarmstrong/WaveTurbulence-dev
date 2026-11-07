/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
import Mathlib.Tactic

/-! # Appendix B incidence tables compute actual deleted-atom degrees -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

@[expose] def appbIncidence (M : Molecule V D) (v : V) (x : D) : ℕ :=
  (if M.atom x = v then 1 else 0) + (if M.atom (M.mate x) = v then 1 else 0)

/-- Handshaking localized at one atom, with outgoing bond representatives. -/
theorem appb_degree_bond_sum (M : Molecule V D) (v : V) :
    M.deg v = ∑ x ∈ M.bonds, appbIncidence M v x := by
  unfold appbIncidence
  rw [sum_add_distrib]
  simp only [sum_boole]
  change M.deg v = (Degen.bondsOutAt M v).card + (Degen.bondsInto M v).card
  rw [Degen.card_bondsOutAt,Degen.card_bondsInto]
  exact (outdeg_add_indeg M v).symm

/-- At a deleted atom all its incidences occur in the deleted bond list. -/
theorem appb_removed_degree_sum (M : Molecule V D) (Y : Finset V) {v : V} (hv : v ∈ Y) :
    M.deg v = ∑ x ∈ appbRemovedBonds M Y, appbIncidence M v x := by
  rw [appb_degree_bond_sum]
  symm
  apply sum_subset (filter_subset _ _)
  intro x hx hnot
  have ha : M.atom x ≠ v := by
    intro he
    exact hnot (mem_filter.mpr ⟨hx,Or.inl (he ▸ hv)⟩)
  have hb : M.atom (M.mate x) ≠ v := by
    intro he
    exact hnot (mem_filter.mpr ⟨hx,Or.inr (he ▸ hv)⟩)
  simp only [appbIncidence,ha,hb,ite_false,zero_add]

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Distinct figure labels cannot become accidentally identified by deletion. -/
theorem vertex_mem_removed_iff (a : ℕ) (ha : a ∈ P.vertices) :
    r.vertex a ∈ r.removedAtoms ↔ a ∈ P.removed := by
  constructor
  · intro h
    obtain ⟨b,hb,he⟩ := mem_image.mp h
    have he' := r.vertex_injective (mem_union_left _ hb) ha he
    simpa only [he'] using hb
  · exact mem_image_of_mem _

/-- Reindex a sum over the actual deleted bonds by their figure labels. -/
theorem removedBond_sum {A : Type*} [AddCommMonoid A] (f : D → A) :
    (∑ i : Fin P.edges.length, f (r.edge i).val) =
      ∑ x ∈ appbRemovedBonds M r.removedAtoms, f x := by
  apply sum_bij (fun i _ => (r.edge i).val)
  · intro i _; exact (r.edge i).property
  · intro i _ j _ h
    exact r.edge.injective (Subtype.ext h)
  · intro x hx
    refine ⟨r.edge.symm ⟨x,hx⟩,mem_univ _,?_⟩
    exact congrArg Subtype.val (r.edge.apply_symm_apply ⟨x,hx⟩)
  · intro i _; rfl

/-- Unordered endpoint equality suffices for the local incidence sum. -/
theorem edge_incidence (i : Fin P.edges.length) (a : ℕ) (ha : a ∈ P.vertices) :
    appbIncidence M (r.vertex a) (r.edge i).val =
      (if P.edges[i].1 = a then 1 else 0) + (if P.edges[i].2 = a then 1 else 0) := by
  have hleft : P.edges[i].1 ∈ P.vertices := by
    apply mem_union_right
    simp only [List.mem_toFinset,List.mem_flatMap]
    exact ⟨P.edges[i],List.getElem_mem _,by simp⟩
  have hright : P.edges[i].2 ∈ P.vertices := by
    apply mem_union_right
    simp only [List.mem_toFinset,List.mem_flatMap]
    exact ⟨P.edges[i],List.getElem_mem _,by simp⟩
  have he1 : r.vertex P.edges[i].1 = r.vertex a ↔ P.edges[i].1 = a :=
    ⟨fun h => r.vertex_injective hleft ha h,fun h => congrArg r.vertex h⟩
  have he2 : r.vertex P.edges[i].2 = r.vertex a ↔ P.edges[i].2 = a :=
    ⟨fun h => r.vertex_injective hright ha h,fun h => congrArg r.vertex h⟩
  have hs := r.endpoints i
  unfold Molecule.ends at hs
  rcases Sym2.eq_iff.mp hs with h | h
  · simp only [appbIncidence,h.1,h.2,he1,he2]
  · simp only [appbIncidence,h.1,h.2,he1,he2]
    omega

/-- The advertised degrees at all deleted atoms are consequences of the
actual old incident-bond enumeration, rather than additional assumptions. -/
theorem deleted_degree (a : ℕ) (ha : a ∈ P.removed) :
    M.deg (r.vertex a) = P.localDegree a := by
  have hav : a ∈ P.vertices := mem_union_left _ ha
  have hdel : r.vertex a ∈ r.removedAtoms := mem_image_of_mem _ ha
  rw [appb_removed_degree_sum M r.removedAtoms hdel, ← r.removedBond_sum]
  unfold AppbPattern.localDegree
  apply sum_congr rfl
  intro i _
  exact r.edge_incidence i a hav

end AppbRealization
end WaveTurbulence.Mole
