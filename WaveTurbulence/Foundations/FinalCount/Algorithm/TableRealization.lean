/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TableIncidences
import Mathlib.Tactic

/-! # Construct complete atomic-group realizations from old incidence data

Exact degrees at removed atoms prove exhaustion of the old bond list.
Completeness of the output enumeration is a conclusion, not an input.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def realizationOfTable (M : Molecule V D) (P : AppbPattern)
    (f : ℕ → V) (hf : Set.InjOn f (P.vertices : Set ℕ)) (hmem : ∀ a ∈ P.vertices,f a ∈ M.atoms)
    (edge : Fin P.edges.length → D) (he : Function.Injective edge)
    (hout : ∀ i,M.out (edge i) = true)
    (hend : ∀ i,M.ends (edge i) = s(f P.edges[i].1,f P.edges[i].2))
    (htouch : ∀ i : Fin P.edges.length,P.edges[i].1 ∈ P.removed ∨ P.edges[i].2 ∈ P.removed)
    (hdeg : ∀ a ∈ P.removed,M.deg (f a) = P.localDegree a) : AppbRealization M P := by
  classical
  have hlisted (i : Fin P.edges.length) : edge i ∈ appbRemovedBonds M (P.removed.image f) := by
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,hout i⟩,?_⟩
    rcases Sym2.eq_iff.mp (hend i) with h | h
    · rcases htouch i with ha | hb
      · exact Or.inl (h.1.symm ▸ mem_image_of_mem f ha)
      · exact Or.inr (h.2.symm ▸ mem_image_of_mem f hb)
    · rcases htouch i with ha | hb
      · exact Or.inr (h.2.symm ▸ mem_image_of_mem f ha)
      · exact Or.inl (h.1.symm ▸ mem_image_of_mem f hb)
  let g : Fin P.edges.length → {x // x ∈ appbRemovedBonds M (P.removed.image f)} :=
    fun i => ⟨edge i,hlisted i⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j hij
      exact he (congrArg Subtype.val hij)
    · intro x
      have hx := table_covers_removed_bond M P f hf edge he hout hend hdeg x.property
      obtain ⟨i,hi,hix⟩ := mem_image.mp hx
      exact ⟨i,Subtype.ext hix⟩
  exact {
    vertex := f
    vertex_injective := hf
    vertex_mem := hmem
    edge := Equiv.ofBijective g hg
    endpoints := hend
  }

end WaveTurbulence.Mole.AppbAlgorithm
