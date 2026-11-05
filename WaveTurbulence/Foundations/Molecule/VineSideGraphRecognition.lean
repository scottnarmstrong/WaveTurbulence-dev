/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideGraphInverse
public import WaveTurbulence.Foundations.Molecule.VineSideBijection
public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
import Mathlib.Tactic

/-! # Conditional recognition from explicit side-graph realization data -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A block with the explicit side label set, joints and full bond multiset
is a pinned type-V vine. This is a conditional graph-recognition helper;
the source containment theorems must construct all its realization inputs. -/
theorem side_graph_realization_isVineV {M : Molecule V D} {A : Finset V} {x y : V}
    (hB : M.IsBlock A x y) (N m : ℕ) (hN : 9 ≤ N) (f : V → ℕ)
    (hinj : Set.InjOn f A) (himage : A.image f=sideLabels N (m+2))
    (hj : ({f x,f y} : Finset ℕ)={7,8})
    (hbonds : (M.groupBonds A).map (Sym2.map f)=rawBondMultiset (sideBonds N (m+2))) :
    M.IsVine .V A x y := by
  let g := sideInverse N m ∘ f
  have hmem (v : V) (hv : v ∈ A) : f v ∈ sideLabels N (m+2) :=
    himage ▸ mem_image_of_mem f hv
  have hspec (v : V) (hv : v ∈ A) := sideInverse_spec N m (f v) hN (hmem v hv)
  refine ⟨hB,[m],rfl,g,?_,?_,?_,?_⟩
  · intro u hu v hv he
    apply hinj hu hv
    have hh := congrArg (sideEmbedding N m) he
    exact (hspec u hu).2.symm.trans (hh.trans (hspec v hv).2)
  · have hn : (VineType.V.expand [m]).n=9+2*m := by rw [expand_atoms]; rfl
    rw [hn]
    ext i
    constructor
    · intro hi
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
      exact mem_range.mpr (hspec v hv).1
    · intro hi
      have hir := mem_range.mp hi
      have hg := sideEmbedding_mem N m i hir
      rw [← himage] at hg
      obtain ⟨v,hv,he⟩ := mem_image.mp hg
      apply mem_image.mpr
      refine ⟨v,hv,?_⟩
      dsimp [g,Function.comp_def]
      rw [he,sideInverse_sideEmbedding N m i hN hir]
  · have hh := congrArg (Finset.image (sideInverse N m)) hj
    simpa only [g,Function.comp_def,image_insert,image_singleton,
      sideInverse,sideCoreInverse,show (7:ℕ)<9 by decide,
      show (8:ℕ)<9 by decide,ite_true] using hh
  · have hh := congrArg (Multiset.map (Sym2.map (sideInverse N m))) hbonds
    rw [Multiset.map_map,sideInverse_bonds N m hN] at hh
    simpa only [g,Function.comp_def,Sym2.map_map,rawBondMultiset] using hh

end WaveTurbulence.Vine
