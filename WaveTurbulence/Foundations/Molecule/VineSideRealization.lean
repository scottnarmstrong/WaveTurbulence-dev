/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSelectedBonds
public import WaveTurbulence.Foundations.Molecule.VineSideRestriction
public import WaveTurbulence.Foundations.Molecule.VineSideGraphInverse
public import WaveTurbulence.Foundations.Molecule.VineCoreAtoms
import Mathlib.Tactic

/-! # Recognizing the actual long VII side as a pinned type-V vine -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The full long side is a type-V vine whenever it is an actual block
with its two prescribed side joints. The graph identification is proved
from the literal expansion, not assumed as a premise. -/
theorem selected_typeVII_side_isVine {M : Molecule V D} {S : Finset V} {a b : V}
    (R : VineRealization M .VII S a b) (kr m kg : ℕ) (hk : R.k=[kr,m+2,kg])
    {u v : V}
    (hB : M.IsBlock (R.selectedAtoms (sideLabels (11+2*kr) (m+2))) u v)
    (hj : ({u,v} : Finset V)={(R.coreAtom (7 : Fin 11)).1,(R.coreAtom (8 : Fin 11)).1}) :
    M.IsVine .V (R.selectedAtoms (sideLabels (11+2*kr) (m+2))) u v := by
  let N := 11+2*kr
  let W := sideLabels N (m+2)
  let A := R.selectedAtoms W
  let g := sideInverse N m ∘ R.f
  have hN : 9 ≤ N := by dsimp [N]; omega
  have hW : W ⊆ range (VineType.VII.expand R.k).n := by
    intro i hi
    have hp := (mem_sideLabels_iff N (m+2) i).mp hi
    rw [hk,expand_atoms_exact .VII [kr,m+2,kg] rfl]
    simp only [VineType.template,List.sum_cons,List.sum_nil,Nat.add_zero]
    apply mem_range.mpr
    dsimp [N] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | ⟨_hlo,hhi⟩ <;> omega
  have hi : ∀ z ∈ A,sideInverse N m (R.f z)<9+2*m ∧
      sideEmbedding N m (sideInverse N m (R.f z))=R.f z := by
    intro z hz
    exact sideInverse_spec N m (R.f z) hN (mem_filter.mp hz).2
  refine ⟨hB,[m],rfl,g,?_,?_,?_,?_⟩
  · intro z hz w hw he
    apply R.injOn (mem_filter.mp hz).1 (mem_filter.mp hw).1
    have hh := congrArg (sideEmbedding N m) he
    exact (hi z hz).2.symm.trans (hh.trans (hi w hw).2)
  · have hn : (VineType.V.expand [m]).n=9+2*m := by rw [expand_atoms]; rfl
    rw [hn]
    apply Finset.ext
    intro i
    constructor
    · intro hiA
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hiA
      exact mem_range.mpr (hi z hz).1
    · intro hir
      have him := mem_range.mp hir
      have hemb := sideEmbedding_mem N m i him
      have hex : sideEmbedding N m i ∈ A.image R.f := by
        rw [R.image_selectedAtoms,inter_eq_left.mpr hW]
        exact hemb
      obtain ⟨z,hz,he⟩ := mem_image.mp hex
      apply mem_image.mpr
      refine ⟨z,hz,?_⟩
      dsimp [g,Function.comp_def]
      rw [he,sideInverse_sideEmbedding N m i hN him]
  · have hjf := congrArg (Finset.image R.f) hj
    simp only [image_insert,image_singleton] at hjf
    have h7 : R.f ((R.coreAtom (7 : Fin 11)).1)=7 := R.label_coreAtom (7 : Fin 11)
    have h8 : R.f ((R.coreAtom (8 : Fin 11)).1)=8 := R.label_coreAtom (8 : Fin 11)
    rw [h7,h8] at hjf
    have hjg := congrArg (Finset.image (sideInverse N m)) hjf
    simpa only [g,Function.comp_def,image_insert,image_singleton,sideInverse,sideCoreInverse,
      show (7:ℕ)<9 from by decide,show (8:ℕ)<9 from by decide,ite_true] using hjg
  · have hb := R.selected_bonds W hW
    rw [hk,typeVII_side_restrict_bonds] at hb
    have hh := congrArg (Multiset.map (Sym2.map (sideInverse N m))) hb
    rw [Multiset.map_map,sideInverse_bonds N m hN] at hh
    simpa only [g,W,N,rawBondMultiset,Function.comp_def,Sym2.map_map] using hh

end WaveTurbulence.Vine
