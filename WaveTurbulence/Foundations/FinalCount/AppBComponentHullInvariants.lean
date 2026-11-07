/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBComponentAdmissibility
public import WaveTurbulence.Foundations.FinalCount.AppBClosedSidePaths
public import WaveTurbulence.Foundations.FinalCount.AppBValidLinkScales
public import WaveTurbulence.Foundations.FinalCount.AppBLargeGap
import Mathlib.Tactic

/-! # Component projection preserves the physical tests used by Appendix B -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_componentHull_largeGap (M : Molecule V D) (S : Finset V) {d : ℕ}
    (L : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (g : ℝ)
    (hA : ∀ κ,A κ → AppbLargeGap M L w κ g)
    {κ : D → (Fin d → ℤ)} (hκ : appbComponentHull M S A κ) : AppbLargeGap M L w κ g := by
  intro v hv x hx y hy hdir hmate
  by_cases hvS : v ∈ S
  · obtain ⟨ζ,hζ,he⟩ := hκ.1
    have hxS : M.atom x ∈ S := (mem_filter.mp hx).2.symm ▸ hvS
    have hyS : M.atom y ∈ S := (mem_filter.mp hy).2.symm ▸ hvS
    have hex : ζ x = κ x := congrFun he ⟨x,hxS⟩
    have hey : ζ y = κ y := congrFun he ⟨y,hyS⟩
    simpa only [Molecule.kvec,hex,hey] using hA ζ hζ v hv x hx y hy hdir hmate
  · obtain ⟨ζ,hζ,he⟩ := hκ.2
    have hvR : v ∈ M.atoms \ S := mem_sdiff.mpr ⟨hv,hvS⟩
    have hxR : M.atom x ∈ M.atoms \ S := (mem_filter.mp hx).2.symm ▸ hvR
    have hyR : M.atom y ∈ M.atoms \ S := (mem_filter.mp hy).2.symm ▸ hvR
    have hex : ζ x = κ x := congrFun he ⟨x,hxR⟩
    have hey : ζ y = κ y := congrFun he ⟨y,hyR⟩
    simpa only [Molecule.kvec,hex,hey] using hA ζ hζ v hv x hx y hy hdir hmate

theorem AppbValidLinkScales.componentHull {M : Molecule V D} {S : Finset V}
    (hS : AppbClosedSide M S) {d : ℕ} {L c : ℝ} {w : Mom d}
    {A : (D → (Fin d → ℤ)) → Prop} {P : Finset V → ℝ}
    (h : AppbValidLinkScales M L w A c P) :
    AppbValidLinkScales M L w (appbComponentHull M S A) c P := by
  constructor
  · exact h.1
  · intro u v hL κ hκ g hg hp
    obtain ⟨x,y,hx,hy,hax,hay,hg⟩ := hg
    have hne : u 0 ≠ v 0 := (Sum.elim_injective.mp hL.2.1).2.2 0 0
    have hadj := Degen.adj_of_bondsBetween_pos M hne (by rw [hL.2.2.2.1 0]; omega)
    have hmem := hS.path_mem_iff (Relation.EqvGen.rel _ _ hadj)
    have hcomplete : ∃ ζ,A ζ ∧ ζ x = κ x ∧ ζ y = κ y := by
      by_cases huS : u 0 ∈ S
      · obtain ⟨ζ,hζ,he⟩ := hκ.1
        have hxS : M.atom x ∈ S := hax.symm ▸ huS
        have hyS : M.atom y ∈ S := hay.symm ▸ hmem.mp huS
        exact ⟨ζ,hζ,congrFun he ⟨x,hxS⟩,congrFun he ⟨y,hyS⟩⟩
      · obtain ⟨ζ,hζ,he⟩ := hκ.2
        have hvS : v 0 ∉ S := fun hv => huS (hmem.mpr hv)
        have hxR : M.atom x ∈ M.atoms \ S := mem_sdiff.mpr ⟨M.atom_mem _,hax.symm ▸ huS⟩
        have hyR : M.atom y ∈ M.atoms \ S := mem_sdiff.mpr ⟨M.atom_mem _,hay.symm ▸ hvS⟩
        exact ⟨ζ,hζ,congrFun he ⟨x,hxR⟩,congrFun he ⟨y,hyR⟩⟩
    obtain ⟨ζ,hζ,hex,hey⟩ := hcomplete
    apply h.2 u v hL ζ hζ g _ hp
    refine ⟨x,y,hx,hy,hax,hay,?_⟩
    simpa only [Molecule.gapAt,Molecule.kvec,hex,hey] using hg

end WaveTurbulence.Mole
