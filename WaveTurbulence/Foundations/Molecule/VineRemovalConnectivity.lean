/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemovalRetraction
public import WaveTurbulence.Foundations.Molecule.VineChainConnected
import Mathlib.Tactic

/-! # Gluing surviving joint paths after disjoint removals -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [DecidableEq D] [Fintype D]

omit [DecidableEq D] [Fintype D] in
/-- A local path-gluing lemma for simultaneous removals. It is conditional
on surviving paths between each piece's joints; it is not the source
subsetvc theorem. Source applications must construct those local paths. -/
theorem removal_connected_of_joint_paths (M : Molecule V D) (S : Finset V)
    (ps : List (RemovalPiece V D)) (hS : GroupConnected M S)
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hinside : ∀ P ∈ ps,∀ d ∈ P.darts,M.InGroup P.atoms d)
    (hclosed : ∀ P ∈ ps,∀ u ∈ P.interior,∀ v,M.Adj u v → v ∈ P.atoms)
    (hjoints : ∀ P ∈ ps,∀ u ∈ ({P.left,P.right} : Finset V),
      ∀ v ∈ ({P.left,P.right} : Finset V),(removeBlocks M S ps).SameComponent u v) :
    ∀ u ∈ remainingAtoms S ps,∀ v ∈ remainingAtoms S ps,
      (removeBlocks M S ps).SameComponent u v := by
  let r := removalRetraction ps
  let N := removeBlocks M S ps
  have hedge : ∀ u v,(Mole.induced M S).Adj u v → N.SameComponent (r u) (r v) := by
    intro u v huv
    obtain ⟨hadj,huS,hvS⟩ := (Mole.induced_adj_iff M S u v).mp huv
    by_cases hpiece : ∃ P,P ∈ ps ∧ u ∈ P.atoms ∧ v ∈ P.atoms
    · obtain ⟨P,hP,huP,hvP⟩ := hpiece
      exact hjoints P hP _ (removalRetraction_joint ps hdis hP huP)
        _ (removalRetraction_joint ps hdis hP hvP)
    · have hui : ∀ P ∈ ps,u ∉ P.interior := by
        intro P hP hi
        exact hpiece ⟨P,hP,(mem_sdiff.mp hi).1,hclosed P hP u hi v hadj⟩
      have hvi : ∀ P ∈ ps,v ∉ P.interior := by
        intro P hP hi
        exact hpiece ⟨P,hP,hclosed P hP v hi u (Mole.adj_symmetric M hadj),(mem_sdiff.mp hi).1⟩
      have huR : u ∈ remainingAtoms S ps := mem_filter.mpr ⟨huS,hui⟩
      have hvR : v ∈ remainingAtoms S ps := mem_filter.mpr ⟨hvS,hvi⟩
      have hru : r u=u := removalRetraction_fixed S ps huR
      have hrv : r v=v := removalRetraction_fixed S ps hvR
      rw [hru,hrv]
      obtain ⟨d,hdu,hdv⟩ := hadj
      have hk : KeepDart M S ps d := by
        refine ⟨hdu.symm ▸ huR,hdv.symm ▸ hvR,?_⟩
        intro P hP
        constructor
        · intro hdP
          have hh := hinside P hP d hdP
          exact hpiece ⟨P,hP,hdu ▸ hh.1,hdv ▸ hh.2⟩
        · intro hdP
          have hh := hinside P hP (M.mate d) hdP
          dsimp only [Molecule.InGroup] at hh
          rw [M.mate_mate] at hh
          exact hpiece ⟨P,hP,hdu ▸ hh.2,hdv ▸ hh.1⟩
      exact Relation.EqvGen.rel _ _ ⟨⟨d,hk⟩,hdu,hdv⟩
  have lift : ∀ u v,(Mole.induced M S).SameComponent u v → N.SameComponent (r u) (r v) := by
    intro u v hp
    induction hp with
    | rel u v huv => exact hedge u v huv
    | refl u => exact Relation.EqvGen.refl _
    | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  intro u hu v hv
  have hp := lift u v (hS u (mem_filter.mp hu).1 v (mem_filter.mp hv).1)
  have hru : r u=u := removalRetraction_fixed S ps hu
  have hrv : r v=v := removalRetraction_fixed S ps hv
  simpa only [hru,hrv] using hp

end WaveTurbulence.Vine
