/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutTriple
import Mathlib.Tactic

/-! # Three-bond cut coordinates from an exact ambient crossing enumeration -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_image_fin_three {A : Type*} [DecidableEq A] (f : Fin 3 → A) :
    univ.image f = {f 0,f 1,f 2} := by
  ext x
  simp only [mem_image,mem_univ,true_and,mem_insert,mem_singleton]
  constructor
  · rintro ⟨j,rfl⟩
    fin_cases j <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

noncomputable def appbCutTripleOfCrossing {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (S : Finset V) (hS : S ⊆ M.atoms) (e : Fin 3 ↪ Fin P.edges.length)
    (hc : appbCrossingBonds M S = univ.image (fun j => (r.edge (e j)).val)) : AppbCutTriple r S where
  subset_atoms := hS
  crossing := by
    intro x hx
    rw [hc] at hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    exact (r.edge (e j)).property
  index := e
  cross := by
    intro j
    have hx : (r.edge (e j)).val ∈ appbCrossingBonds M S :=
      hc.symm ▸ mem_image_of_mem _ (mem_univ j)
    exact (mem_filter.mp hx).2
  other := by
    intro i hi
    by_contra hn
    have hcross : (M.atom (r.edge i).val ∈ S ∧ M.atom (M.mate (r.edge i).val) ∉ S) ∨
        (M.atom (r.edge i).val ∉ S ∧ M.atom (M.mate (r.edge i).val) ∈ S) := by tauto
    have hx : (r.edge i).val ∈ appbCrossingBonds M S :=
      mem_filter.mpr ⟨(mem_filter.mp (r.edge i).property).1,hcross⟩
    rw [hc] at hx
    obtain ⟨j,hj,he⟩ := mem_image.mp hx
    exact hi j (r.edge.injective (Subtype.ext he))

end WaveTurbulence.Mole
