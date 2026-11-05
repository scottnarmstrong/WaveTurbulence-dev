/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemoval
import Mathlib.Tactic

/-! # Local surviving paths embed into a containing removal family -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V]

/-- A path inside B after its local removals survives the global family
when each other global piece is disjoint from B. Selected darts must
belong to their actual source atom group. -/
theorem removal_local_path_lift (M : Molecule V D) {B U : Finset V} (hBU : B ⊆ U)
    (qs ps : List (RemovalPiece V D))
    (hparts : ∀ P ∈ ps,P ∈ qs ∨ Disjoint P.atoms B)
    (hinside : ∀ P ∈ ps,∀ d ∈ P.darts,M.InGroup P.atoms d)
    {u v : V} (hp : (removeBlocks M B qs).SameComponent u v) :
    (removeBlocks M U ps).SameComponent u v := by
  have atoms (z : V) (hz : z ∈ remainingAtoms B qs) : z ∈ remainingAtoms U ps := by
    have hh := mem_filter.mp hz
    refine mem_filter.mpr ⟨hBU hh.1,?_⟩
    intro P hP
    rcases hparts P hP with hQ | hd
    · exact hh.2 P hQ
    · intro hm
      exact (disjoint_left.mp hd) (mem_sdiff.mp hm).1 hh.1
  have keep (d : D) (hd : KeepDart M B qs d) : KeepDart M U ps d := by
    refine ⟨atoms _ hd.1,atoms _ hd.2.1,?_⟩
    intro P hP
    rcases hparts P hP with hQ | hdis
    · exact hd.2.2 P hQ
    · have hb := (mem_filter.mp hd.1).1
      constructor
      · intro hm
        exact (disjoint_left.mp hdis) (hinside P hP d hm).1 hb
      · intro hm
        have hh := (hinside P hP (M.mate d) hm).2
        rw [M.mate_mate] at hh
        exact (disjoint_left.mp hdis) hh hb
  induction hp with
  | rel u v huv =>
    obtain ⟨d,hdu,hdv⟩ := huv
    exact Relation.EqvGen.rel _ _ ⟨⟨d.1,keep d.1 d.2⟩,hdu,hdv⟩
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end WaveTurbulence.Vine
