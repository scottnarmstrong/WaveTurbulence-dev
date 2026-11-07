/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceCounts
public import WaveTurbulence.Foundations.Molecule.Degen.ComponentQuotient
import Mathlib.Tactic

/-! # Boundary counts of the Appendix B incidence patterns -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

@[expose] def appbCrossingBonds (M : Molecule V D) (Y : Finset V) : Finset D :=
  M.bonds.filter fun x => (M.atom x ∈ Y ∧ M.atom (M.mate x) ∉ Y) ∨
    (M.atom x ∉ Y ∧ M.atom (M.mate x) ∈ Y)

/-- Each crossing bond has exactly one half-edge on the removed side. -/
theorem appb_boundary_card (M : Molecule V D) (Y : Finset V) :
    (Degen.boundaryDarts M Y).card = (appbCrossingBonds M Y).card := by
  apply card_bij (fun x _ => if M.out x then x else M.mate x)
  · intro x hx
    obtain ⟨ha,hb⟩ : M.atom x ∈ Y ∧ M.atom (M.mate x) ∉ Y := (mem_filter.mp hx).2
    cases ho : M.out x
    · simp only [ho,Bool.false_eq_true,ite_false,appbCrossingBonds,Molecule.bonds,
        mem_filter,mem_univ,true_and,M.out_mate,M.mate_mate]
      exact ⟨rfl,Or.inr ⟨hb,ha⟩⟩
    · simp only [ho,ite_true,appbCrossingBonds,Molecule.bonds,mem_filter,mem_univ,true_and]
      exact Or.inl ⟨ha,hb⟩
  · intro x hx y hy h
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    cases ho : M.out x <;> cases hp : M.out y
    · have he : M.mate x = M.mate y := by simpa only [ho,hp,Bool.false_eq_true,ite_false] using h
      exact mate_injective M he
    · have he : M.mate x = y := by simpa only [ho,hp,Bool.false_eq_true,ite_false,ite_true] using h
      exact (hx'.2 (he ▸ hy'.1)).elim
    · have he : x = M.mate y := by simpa only [ho,hp,Bool.false_eq_true,ite_false,ite_true] using h
      exact (hy'.2 (he ▸ hx'.1)).elim
    · simpa only [ho,hp,ite_true] using h
  · intro x hx
    obtain ⟨hxout,hcross⟩ := mem_filter.mp hx
    have hout : M.out x = true := (mem_filter.mp hxout).2
    rcases hcross with h | h
    · refine ⟨x,mem_filter.mpr ⟨mem_univ _,h⟩,?_⟩
      simp only [hout,ite_true]
    · refine ⟨M.mate x,?_,?_⟩
      · exact mem_filter.mpr ⟨mem_univ _,by simpa only [M.mate_mate] using And.intro h.2 h.1⟩
      · simp only [M.out_mate,hout,Bool.not_true,Bool.false_eq_true,ite_false,M.mate_mate]

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- The local figure's boundary count is the actual ambient cut size. -/
theorem boundary_card : (Degen.boundaryDarts M r.removedAtoms).card = P.boundaryCount := by
  rw [appb_boundary_card]
  let cross : D → Prop := fun x =>
    (M.atom x ∈ r.removedAtoms ∧ M.atom (M.mate x) ∉ r.removedAtoms) ∨
    (M.atom x ∉ r.removedAtoms ∧ M.atom (M.mate x) ∈ r.removedAtoms)
  have hfilter : appbCrossingBonds M r.removedAtoms =
      (appbRemovedBonds M r.removedAtoms).filter cross := by
    ext x
    simp only [appbCrossingBonds,appbRemovedBonds,mem_filter,cross]
    tauto
  rw [hfilter]
  have hsum : (filter cross (appbRemovedBonds M r.removedAtoms)).card =
      ∑ x ∈ appbRemovedBonds M r.removedAtoms, if cross x then (1 : ℕ) else 0 :=
    (sum_boole (R := ℕ) cross _).symm
  rw [hsum]
  rw [← r.removedBond_sum]
  unfold AppbPattern.boundaryCount
  apply sum_congr rfl
  intro i _
  have hleft : P.edges[i].1 ∈ P.vertices := by
    apply mem_union_right
    simp only [List.mem_toFinset,List.mem_flatMap]
    exact ⟨P.edges[i],List.getElem_mem _,by simp⟩
  have hright : P.edges[i].2 ∈ P.vertices := by
    apply mem_union_right
    simp only [List.mem_toFinset,List.mem_flatMap]
    exact ⟨P.edges[i],List.getElem_mem _,by simp⟩
  have hl := r.vertex_mem_removed_iff _ hleft
  have hr := r.vertex_mem_removed_iff _ hright
  have hs := r.endpoints i
  unfold Molecule.ends at hs
  rcases Sym2.eq_iff.mp hs with h | h
  · simp only [cross,h.1,h.2,hl,hr]
  · have hc : cross (r.edge i).val ↔
        (P.edges[i].1 ∈ P.removed ∧ P.edges[i].2 ∉ P.removed) ∨
        (P.edges[i].1 ∉ P.removed ∧ P.edges[i].2 ∈ P.removed) := by
      simp only [cross,h.1,h.2,hl,hr]
      tauto
    exact if_congr hc rfl rfl

/-- The bridgeless bound on residual components, with the cut cardinality
computed from the figure, not supplied as a hypothesis. -/
theorem two_mul_post_components_le
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) (hne : P.removed.Nonempty) :
    2 * r.post.numComponents ≤ P.boundaryCount := by
  have hY : r.removedAtoms.Nonempty := hne.image r.vertex
  change 2 * (Degen.eraseAtoms M r.removedAtoms).numComponents ≤ _
  rw [Degen.numComponents_eraseAtoms_eq_card_newComponents M hconn _ hY r.removedAtoms_subset]
  exact (Degen.two_mul_card_newComponents_le M hbridge r.removedAtoms).trans_eq r.boundary_card

end AppbRealization

end WaveTurbulence.Mole
