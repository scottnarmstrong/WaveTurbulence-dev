/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalLabels
public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceCounts
public import WaveTurbulence.Foundations.Molecule.Degen.Cut
import Mathlib.Tactic

/-! # Actual outgoing-bond coordinates for local conservation equations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Reindex every signed incidence by its outgoing representative. Loops
are counted at both ends and cancel, as required by conservation. -/
theorem appb_sum_dartsAt_outgoing (M : Molecule V D) (v : V)
    {E : Type*} [AddCommGroup E] (g : D → E) (hg : ∀ x, g (M.mate x) = -g x) :
    (∑ x ∈ M.dartsAt v, g x) = ∑ x ∈ M.bonds,
      ((if M.atom x = v then g x else 0) -
        (if M.atom (M.mate x) = v then g x else 0)) := by
  classical
  have hsplit := sum_filter_add_sum_filter_not (M.dartsAt v) (fun x => M.out x = true) g
  have hout : (∑ x ∈ (M.dartsAt v).filter (fun x => M.out x = true),g x) =
      ∑ x ∈ M.bonds, if M.atom x = v then g x else 0 := by
    rw [← sum_filter]
    apply sum_congr
    · ext x; simp only [Molecule.dartsAt,Molecule.bonds,mem_filter,mem_univ,true_and,and_comm]
    · intro x hx; rfl
  have hin : (∑ x ∈ (M.dartsAt v).filter (fun x => ¬M.out x = true),g x) =
      ∑ x ∈ M.bonds, if M.atom (M.mate x) = v then -g x else 0 := by
    rw [← sum_filter]
    symm
    apply sum_bij (fun x _ => M.mate x)
    · intro x hx
      obtain ⟨hx,hv⟩ := mem_filter.mp hx
      have ho := (mem_filter.mp hx).2
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hv⟩,by rw [M.out_mate,ho]; decide⟩
    · intro x _ y _ h
      exact mate_injective M h
    · intro x hx
      obtain ⟨hx,hout⟩ := mem_filter.mp hx
      have hv := (mem_filter.mp hx).2
      refine ⟨M.mate x,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩,M.mate_mate x⟩
      · rw [M.out_mate]
        cases h : M.out x <;> simp_all
      · simpa only [M.mate_mate] using hv
    · intro x hx
      exact (hg x).symm
  rw [← hsplit,hout,hin,← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  by_cases h : M.atom (M.mate x) = v <;> simp [h,sub_eq_add_neg]

/-- At a deleted atom only enumerated local bonds contribute. -/
theorem appb_sum_dartsAt_removed (M : Molecule V D) (Y : Finset V) {v : V} (hv : v ∈ Y)
    {E : Type*} [AddCommGroup E] (g : D → E) (hg : ∀ x, g (M.mate x) = -g x) :
    (∑ x ∈ M.dartsAt v,g x) = ∑ x ∈ appbRemovedBonds M Y,
      ((if M.atom x = v then g x else 0) -
        (if M.atom (M.mate x) = v then g x else 0)) := by
  rw [appb_sum_dartsAt_outgoing M v g hg]
  symm
  apply sum_subset (filter_subset _ _)
  intro x hx hn
  have hp : ¬(M.atom x ∈ Y ∨ M.atom (M.mate x) ∈ Y) := by
    intro hp
    exact hn (mem_filter.mpr ⟨hx,hp⟩)
  have h1 : M.atom x ≠ v := by intro he; apply hp; exact Or.inl (he.symm ▸ hv)
  have h2 : M.atom (M.mate x) ≠ v := by intro he; apply hp; exact Or.inr (he.symm ▸ hv)
  simp only [h1,h2,ite_false,sub_zero]

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Every source conservation equation at a removed vertex becomes an
exact finite equation in the actual figure edge coordinates. -/
theorem sum_dartsAt_local_edges {v : V} (hv : v ∈ r.removedAtoms)
    {E : Type*} [AddCommGroup E] (g : D → E) (hg : ∀ x, g (M.mate x) = -g x) :
    (∑ x ∈ M.dartsAt v,g x) = ∑ i : Fin P.edges.length,
      ((if M.atom (r.edge i).val = v then g (r.edge i).val else 0) -
        (if M.atom (M.mate (r.edge i).val) = v then g (r.edge i).val else 0)) := by
  rw [r.removedBond_sum (fun x => (if M.atom x = v then g x else 0) -
    (if M.atom (M.mate x) = v then g x else 0))]
  exact appb_sum_dartsAt_removed M r.removedAtoms hv g hg

end AppbRealization
end WaveTurbulence.Mole
